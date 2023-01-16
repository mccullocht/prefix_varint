//! Routines for working with raw (u64) prefix varints.
//!
//! Other types should be shuffled to/from raw values using the `core::Int` trait.

use crate::{MAX_1BYTE_TAG, MAX_VALUE, TAG_PREFIX};

/// Return the number of bytes required to encode `v` in `[1,MAX_LEN]`.
#[inline]
pub(crate) fn len(mut v: u64) -> usize {
    // Mask off the top bit to cap bits_required to a maximum of 63.
    // This avoids a branch to cap the maximum returned value of MAX_LEN.
    v |= v >> 1;
    v &= (1 << 63) - 1;
    let bits_required = 64 - (v.leading_zeros() as usize);
    ((bits_required.saturating_sub(1)) / 7) + 1
}

/// Encodes a raw value that produce multiple bytes of output.
///
/// This may generate a substantial amount of code so it is not inlined.
///
/// # Safety
///
/// This assumes that bytes `p..=(p + MAX_LEN)` may be written to.
pub(crate) unsafe fn encode_multibyte(v: u64, p: *mut u8) -> usize {
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

/// Encodes a raw value as prefix uvarint to `p`.
///
/// # Safety
///
/// This assumes that bytes `p..=(p + MAX_LEN)` may be written to.
#[inline]
pub unsafe fn encode(v: u64, p: *mut u8) -> usize {
    if v <= MAX_VALUE[1] {
        std::ptr::write(p, v as u8);
        1
    } else {
        encode_multibyte(v, p)
    }
}

/// Decodes a prefix uvarint value from `p`, returning the value and the number
/// of bytes consumed.
///
/// `p` points to the byte that produced the value `tag`.
///
/// # Safety
///
/// This assumes that bytes `p..=(p + MAX_LEN)` may be read from.
pub(crate) unsafe fn decode_multibyte(tag: u8, p: *const u8) -> (u64, usize) {
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

/// Decode a prefix uvarint value from `p`, returning the raw value and number of bytes consumed.
///
/// # Safety
///
/// This assumes that bytes `p..=(p + MAX_LEN)` may be read from.
#[inline]
pub unsafe fn decode(p: *const u8) -> (u64, usize) {
    let tag = std::ptr::read(p);
    if tag <= MAX_1BYTE_TAG {
        (tag.into(), 1)
    } else {
        decode_multibyte(tag, p)
    }
}
