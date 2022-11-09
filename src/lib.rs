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
//! use prefix_uvarint::{VarintBuf, VarintBufMut};
//!
//! let mut buf_mut = Vec::new();
//! for v in (0..100).step_by(3) {
//!   buf_mut.put_prefix_uvarint(v);
//! }
//!
//! // NB: need a mutable slice to use as VarintBuf
//! let mut buf = buf_mut.as_slice();
//! while let Some(v) = buf.get_prefix_uvarint() {
//!   assert_eq!(v % 3, 0);
//! }
//! assert!(!buf.has_remaining());
//! ```
pub mod io;
#[cfg(test)]
mod tests;

use bytes::buf::{Buf, BufMut};

//pub use crate::io::{VarintBufRead, VarintRead, VarintWrite};

/// Maximum number of bytes a single encoded uvarint will occupy.
pub const MAX_LEN: usize = 9;

/// Maps negative values to positive values, creating a sequence that alternates between negative
/// and positive values. This makes the value more amenable to efficient prefix uvarint encoding.
pub(crate) fn zigzag_encode(v: i64) -> u64 {
    ((v >> 63) ^ (v << 1)) as u64
}

/// Inverts `zigzag_encode()`.
pub(crate) fn zigzag_decode(v: u64) -> i64 {
    (v >> 1) as i64 ^ -(v as i64 & 1)
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
/// This may write up to `MAX_LEN` bytes and may panic if fewer bytes are available.
#[inline]
pub unsafe fn encode_prefix_uvarint(v: u64, p: *mut u8) -> usize {
    if v <= MAX_VALUE[1] {
        std::ptr::write(p, v as u8);
        1
    } else {
        encode_prefix_uvarint_slow(v, p)
    }
}

/// Encodes `v` as a prefix varint to `p`.
///
/// This may write up to `MAX_LEN` bytes and may panic if fewer bytes are available.
#[inline]
pub unsafe fn encode_prefix_varint(v: i64, p: *mut u8) -> usize {
    encode_prefix_uvarint(zigzag_encode(v), p)
}

fn put_prefix_uvarint_slow<B: bytes::BufMut + ?Sized>(b: &mut B, v: u64) {
    if v < MAX_VALUE[2] {
        b.put_u16((v | TAG_PREFIX[2]) as u16)
    } else if v < MAX_VALUE[3] {
        b.put_uint(v | TAG_PREFIX[3], 3)
    } else if v < MAX_VALUE[4] {
        b.put_u32((v | TAG_PREFIX[4]) as u32)
    } else if v < MAX_VALUE[5] {
        b.put_uint(v | TAG_PREFIX[5], 5)
    } else if v < MAX_VALUE[6] {
        b.put_uint(v | TAG_PREFIX[6], 6)
    } else if v < MAX_VALUE[7] {
        b.put_uint(v | TAG_PREFIX[7], 7)
    } else if v < MAX_VALUE[8] {
        b.put_u64(v | TAG_PREFIX[8])
    } else {
        b.put_u8(u8::MAX);
        b.put_u64(v)
    }
}

/// An extension to the `bytes::BufMut` trait to add prefix varint encoding methods.
pub trait VarintBufMut: bytes::BufMut {
    /// Puts `v` into the buffer in a variable length encoding using 1-9 bytes.
    #[inline]
    fn put_prefix_uvarint(&mut self, v: u64) {
        let buf = self.chunk_mut();
        if buf.len() >= MAX_LEN {
            unsafe {
                let len = encode_prefix_uvarint(v, buf.as_mut_ptr());
                self.advance_mut(len);
            }
        } else if v <= MAX_VALUE[1] {
            self.put_u8(v as u8)
        } else {
            put_prefix_uvarint_slow(self, v)
        }
    }

    /// Puts `v` into the buffer in a variable length encoding using 1-9 bytes.
    #[inline]
    fn put_prefix_varint(&mut self, v: i64) {
        self.put_prefix_uvarint(zigzag_encode(v))
    }
}

/// Implement for all types that implement `bytes::BufMut`.
impl<B: BufMut + ?Sized> VarintBufMut for B {}

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

/// Decodes a prefix uvarint value from `p`, returning the value and the number of bytes consumed.
///
/// This function may read up to `MAX_LEN` bytes from `p` and may panic if fewer bytes are available.
#[inline]
pub unsafe fn decode_prefix_uvarint(p: *const u8) -> (u64, usize) {
    let tag = std::ptr::read(p);
    if tag <= MAX_1BYTE_TAG {
        (tag.into(), 1)
    } else {
        decode_prefix_uvarint_slow(tag, p)
    }
}

/// Decodes a prefix varint value from `p`, returning the value and the number of bytes consumed.
///
/// This function may read up to `MAX_LEN` bytes from `p` and may panic if fewer bytes are available.
#[inline]
pub unsafe fn decode_prefix_varint(p: *const u8) -> (i64, usize) {
    let (v, len) = decode_prefix_uvarint(p);
    (zigzag_decode(v), len)
}

fn get_prefix_uvarint_slow<B: Buf + ?Sized>(b: &mut B, tag: u8) -> Option<u64> {
    let remaining_bytes = tag.leading_ones() as usize;
    if b.remaining() < remaining_bytes {
        b.advance(b.remaining());
        return None;
    }

    let raw = match remaining_bytes {
        1 => ((u64::from(tag) << 8) | b.get_uint(1)) & MAX_VALUE[2],
        2 => ((u64::from(tag) << 16) | u64::from(b.get_u16())) & MAX_VALUE[3],
        3 => ((u64::from(tag) << 24) | b.get_uint(3)) & MAX_VALUE[4],
        4 => ((u64::from(tag) << 32) | u64::from(b.get_u32())) & MAX_VALUE[5],
        5 => ((u64::from(tag) << 40) | b.get_uint(5)) & MAX_VALUE[6],
        6 => ((u64::from(tag) << 48) | b.get_uint(6)) & MAX_VALUE[7],
        7 => ((u64::from(tag) << 56) | b.get_uint(7)) & MAX_VALUE[8],
        _ => b.get_u64(),
    };
    Some(raw)
}

/// Extensions for `bytes::Buf` trait to add prefix varint decoding methods.
pub trait VarintBuf: bytes::Buf {
    /// Reads a single prefix uvarint value from the buffer.
    /// If the input is not long enough to produce a value, advances to the end and returns `None`.
    #[inline]
    fn get_prefix_uvarint(&mut self) -> Option<u64> {
        let buf = self.chunk();
        if buf.len() >= MAX_LEN {
            let (value, len) = unsafe { decode_prefix_uvarint(buf.as_ptr()) };
            self.advance(len);
            Some(value)
        } else if !self.has_remaining() {
            None
        } else {
            let tag = self.get_u8();
            if tag <= MAX_1BYTE_TAG {
                Some(tag.into())
            } else {
                get_prefix_uvarint_slow(self, tag)
            }
        }
    }

    /// Reads a single prefix varint value from the buffer.
    /// If the input is not long enough to produce a value, advances to the end and returns `None`.
    #[inline]
    fn get_prefix_varint(&mut self) -> Option<i64> {
        let v = self.get_prefix_uvarint()?;
        Some(zigzag_decode(v))
    }
}

/// Implement for all types that implement `bytes::Buf`.
impl<B: Buf + ?Sized> VarintBuf for B {}
