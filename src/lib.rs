//! This module implements a prefix-based variable length integer coding scheme.
//!
//! Unlike an [LEB128](https://en.wikipedia.org/wiki/LEB128)-style encoding scheme, this encoding
//! uses a unary prefix code in the first byte of the value to indicate how many subsequent bytes
//! need to be read followed by the big endian encoding of any remaining bytes. This improves
//! coding speed compared to LEB128 by reducing the number of branches required to code longer
//! values.
//!
//! `uvarint` methods code `u64` values, with values closer to zero producing smaller output.
//! `varint` methods code `i64` values using a [Zigzag](https://en.wikipedia.org/wiki/Variable-length_quantity#Zigzag_encoding)
//! encoding to ensure that small negative numbers produce small output.
//!
//! Coding methods are provided as extensions to the `bytes::{Buf,BufMut}` traits which are
//! implemented for common in-memory byte stream types. Lower level methods that operate directly
//! on pointers are also provided but come with caveats (may overread/overwrite).
//!
//! ```
//! use bytes::Buf;
//! use prefix_uvarint::PrefixVarInt;
//!
//! let mut buf_mut = Vec::new();
//! for v in (0..100).step_by(3) {
//!   v.encode_varint(&mut buf_mut);
//! }
//!
//! // NB: need a mutable slice to use as VarintBuf
//! let mut buf = buf_mut.as_slice();
//! while let Ok(v) = u64::decode_varint(&mut buf) {
//!   assert_eq!(v % 3, 0);
//! }
//! assert!(!buf.has_remaining());
//! ```
pub(crate) mod core;
mod io;
#[cfg(test)]
mod tests;

pub use crate::core::PrefixVarInt;
pub use crate::io::{PrefixVarIntRead, PrefixVarIntWrite};

use bytes::buf::{Buf, BufMut};

/// Maximum number of bytes a single encoded uvarint will occupy.
pub const MAX_LEN: usize = 9;

/// Errors that may occur during decoding.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DecodeError {
    /// Reached end-of-buffer unexpectedly.
    ///
    /// This may happen if you attempt to decode an empty buffer or if the buffer is too short to
    /// contain the expected value.
    UnexpectedEob,
    /// The value read is larger than the destination type.
    Overflow,
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for DecodeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }

    fn description(&self) -> &str {
        ""
    }

    fn cause(&self) -> Option<&dyn std::error::Error> {
        None
    }
}

/// A single encoded prefix varint value for with `PrefixVarInt.to_prefix_varint_bytes()`.
pub struct EncodedPrefixVarint {
    buf: [u8; MAX_LEN],
    len: u8,
}

impl EncodedPrefixVarint {
    fn new(v: u64) -> Self {
        let mut enc = Self::default();
        let len = unsafe { encode_prefix_uvarint(v, enc.buf.as_mut_ptr()) };
        enc.len = len as u8;
        enc
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.buf[..(self.len as usize)]
    }
}

impl Default for EncodedPrefixVarint {
    fn default() -> Self {
        EncodedPrefixVarint {
            buf: [0u8; MAX_LEN],
            len: 0,
        }
    }
}

pub trait PrefixVarIntBufMut {
    fn put_prefix_varint<PV: PrefixVarInt>(&mut self, v: PV);
}

impl<Inner: BufMut> PrefixVarIntBufMut for Inner {
    fn put_prefix_varint<PV: PrefixVarInt>(&mut self, v: PV) {
        let raw = v.to_prefix_varint_raw();
        if raw <= MAX_VALUE[1] {
            self.put_u8(raw as u8);
        } else if self.chunk_mut().len() >= MAX_LEN {
            unsafe {
                let len = encode_prefix_uvarint_slow(raw, self.chunk_mut().as_mut_ptr());
                self.advance_mut(len);
            }
        } else {
            self.put_slice(raw.to_prefix_varint_bytes().as_slice());
        }
    }
}

pub trait PrefixVarIntBuf {
    fn get_prefix_varint<PV: PrefixVarInt>(&mut self) -> Result<PV, DecodeError>;
}

impl<Inner: Buf> PrefixVarIntBuf for Inner {
    fn get_prefix_varint<PV: PrefixVarInt>(&mut self) -> Result<PV, DecodeError> {
        if self.remaining() == 0 {
            return Err(DecodeError::UnexpectedEob);
        }

        if self.chunk().len() >= MAX_LEN || self.remaining() == self.chunk().len() {
            let (v, len) = PV::decode_prefix_varint(self.chunk())?;
            self.advance(len);
            return Ok(v);
        }

        let tag = self.get_u8();
        if tag <= MAX_1BYTE_TAG {
            return PV::from_prefix_varint_raw(tag.into()).ok_or(DecodeError::Overflow);
        }

        let rem = tag.leading_ones() as usize;
        if rem > self.remaining() {
            return Err(DecodeError::UnexpectedEob);
        }
        // XXX consider doing this in a more efficient way rather than being expedient.
        let mut ibuf = [0u8; MAX_LEN];
        ibuf[0] = tag;
        self.copy_to_slice(&mut ibuf[1..(rem + 1)]);
        PV::decode_prefix_varint(ibuf.as_slice()).map(|(v, _)| v)
    }
}

/// Maps negative values to positive values, creating a sequence that alternates between negative
/// and positive values. This makes the value more amenable to efficient prefix uvarint encoding.
#[inline]
pub(crate) fn zigzag_encode(v: i64) -> u64 {
    ((v >> 63) ^ (v << 1)) as u64
}

/// Inverts `zigzag_encode()`.
#[inline]
pub(crate) fn zigzag_decode(v: u64) -> i64 {
    (v >> 1) as i64 ^ -(v as i64 & 1)
}

/// Return the number of bytes required to encode `v` in `[1,MAX_LEN]`.
#[inline]
pub fn prefix_uvarint_len(mut v: u64) -> usize {
    // Mask off the top bit to cap bits_required to a maximum of 63.
    // This avoids a branch to cap the maximum returned value of MAX_LEN.
    v |= v >> 1;
    v &= (1 << 63) - 1;
    let bits_required = 64 - (v.leading_zeros() as usize);
    ((bits_required.saturating_sub(1)) / 7) + 1
}

/// Return the number of bytes required to encode `v` in `[1,MAX_LEN]`.
#[inline]
pub fn prefix_varint_len(v: i64) -> usize {
    prefix_uvarint_len(zigzag_encode(v))
}

/// Max value for an n-byte length.
const MAX_VALUE: [u64; 10] = [
    0x0, // placeholder
    0x7f,
    0x3fff,
    0x1fffff,
    0xfffffff,
    0x7ffffffff,
    0x3ffffffffff,
    0x1ffffffffffff,
    0xffffffffffffff,
    0xffffffffffffffff,
];

// Tag prefix value for an n-byte length to OR with the value.
const TAG_PREFIX: [u64; 9] = [
    0x0, // placeholder
    0x0, // placeholder
    0x8000,
    0xc00000,
    0xe0000000,
    0xf000000000,
    0xf80000000000,
    0xfc000000000000,
    0xfe00000000000000,
];

unsafe fn encode_prefix_uvarint_slow(v: u64, p: *mut u8) -> usize {
    if v <= MAX_VALUE[2] {
        let tv = (v | TAG_PREFIX[2]) as u16;
        std::ptr::write_unaligned(p as *mut u16, tv.to_be());
        2
    } else if v <= MAX_VALUE[3] {
        let tv = ((v | TAG_PREFIX[3]) << 8) as u32;
        std::ptr::write_unaligned(p as *mut u32, tv.to_be());
        3
    } else if v <= MAX_VALUE[4] {
        let tv = (v | TAG_PREFIX[4]) as u32;
        std::ptr::write_unaligned(p as *mut u32, tv.to_be());
        4
    } else if v <= MAX_VALUE[5] {
        let tv = (v | TAG_PREFIX[5]) << 24;
        std::ptr::write_unaligned(p as *mut u64, tv.to_be());
        5
    } else if v <= MAX_VALUE[6] {
        let tv = (v | TAG_PREFIX[6]) << 16;
        std::ptr::write_unaligned(p as *mut u64, tv.to_be());
        6
    } else if v <= MAX_VALUE[7] {
        let tv = (v | TAG_PREFIX[7]) << 8;
        std::ptr::write_unaligned(p as *mut u64, tv.to_be());
        7
    } else if v <= MAX_VALUE[8] {
        let tv = v | TAG_PREFIX[8];
        std::ptr::write_unaligned(p as *mut u64, tv.to_be());
        8
    } else {
        std::ptr::write(p, u8::MAX);
        std::ptr::write_unaligned(p.add(1) as *mut u64, v.to_be());
        9
    }
}

/// Encodes `v` as a prefix uvarint to `p`.
///
/// This may write up to `MAX_LEN` bytes and may panic if fewer bytes are
/// available.
///
/// # Safety
///
/// This method may overread/overwrite memory if `p` is not at least `MAX_LEN`
/// bytes long. It is the caller's responsibility to ensure that `p` is valid
/// for writes of `MAX_LEN` bytes.
#[inline]
pub unsafe fn encode_prefix_uvarint(v: u64, p: *mut u8) -> usize {
    if v <= MAX_VALUE[1] {
        std::ptr::write(p, v as u8);
        1
    } else {
        encode_prefix_uvarint_slow(v, p)
    }
}

pub(crate) unsafe fn decode_prefix_uvarint_slow(tag: u8, p: *const u8) -> (u64, usize) {
    let (raw, len) = match tag.leading_ones() {
        // NB: zero is handled by decode_prefix_uvarint().
        1 => (
            u64::from(u16::from_be(std::ptr::read_unaligned(p as *const u16))) & MAX_VALUE[2],
            2,
        ),
        2 => (
            u64::from(u32::from_be(std::ptr::read_unaligned(p as *const u32)) >> 8) & MAX_VALUE[3],
            3,
        ),
        3 => (
            u64::from(u32::from_be(std::ptr::read_unaligned(p as *const u32))) & MAX_VALUE[4],
            4,
        ),
        4 => (
            (u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 24) & MAX_VALUE[5],
            5,
        ),
        5 => (
            (u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 16) & MAX_VALUE[6],
            6,
        ),
        6 => (
            (u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 8) & MAX_VALUE[7],
            7,
        ),
        7 => (
            u64::from_be(std::ptr::read_unaligned(p as *const u64)) & MAX_VALUE[8],
            8,
        ),
        // NB: this is a catch-all but the maximum possible value for tag.leading_ones() is 8.
        _ => (
            u64::from_be(std::ptr::read_unaligned(p.add(1) as *const u64)),
            9,
        ),
    };
    (raw, len)
}

pub(crate) const MAX_1BYTE_TAG: u8 = MAX_VALUE[1] as u8;

/// Decodes a prefix uvarint value from `p`, returning the value and the number
/// of bytes consumed.
///
/// This function may read up to `MAX_LEN` bytes from `p` and may panic if fewer
/// bytes are available.
///
/// # Safety
///
/// This method may overread memory if `p` is not at least `MAX_LEN` bytes long.
/// It is the caller's responsibility to ensure that `p` is valid for reads of
/// `MAX_LEN` bytes.
#[inline]
pub unsafe fn decode_prefix_uvarint(p: *const u8) -> (u64, usize) {
    let tag = std::ptr::read(p);
    if tag <= MAX_1BYTE_TAG {
        (tag.into(), 1)
    } else {
        decode_prefix_uvarint_slow(tag, p)
    }
}
