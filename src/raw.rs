//! Routines for working with raw (u64) prefix varints.
//!
//! Other types should be shuffled to/from raw values using the `core::Int` trait.

/// Return the number of bytes required to encode `v` in `[1,MAX_LEN]`.
#[inline]
pub(crate) const fn len(mut v: u64) -> usize {
    // Mask off the top bit to cap bits_required to a maximum of 63.
    // This avoids a branch to cap the maximum returned value of MAX_LEN.
    v |= v >> 1;
    v &= !(1 << 63);
    let bits_required = 64 - (v.leading_zeros() as usize);
    // XXX could avoid saturating sub by doing v | 1.
    ((bits_required.saturating_sub(1)) / 7) + 1
}

#[inline(always)]
const fn tag_prefix(len: usize) -> u64 {
    !(u64::MAX >> (len - 1))
}

/// Returns the maximum value for a given byte length. Useful for masking out tag bits.
#[inline(always)]
const fn max_value(len: usize) -> u64 {
    if len >= 9 {
        u64::MAX
    } else {
        !(u64::MAX << (len * 7))
    }
}

/// Encodes a raw value that produce multiple bytes of output.
///
/// This may generate a substantial amount of code so it is not inlined.
///
/// # Safety
///
/// This assumes that bytes `p..=(p + MAX_LEN)` may be written to.
pub(crate) unsafe fn encode_multibyte(v: u64, p: *mut u8) -> usize {
    if v <= max_value(2) {
        let tag_prefix = tag_prefix(2) >> 48;
        let tagged = (v | tag_prefix) as u16;
        std::ptr::write_unaligned(p as *mut u16, tagged.to_be());
        2
    } else if v <= max_value(3) {
        let tag_prefix = tag_prefix(3) >> 32;
        let tagged = (tag_prefix | (v << 8)) as u32;
        std::ptr::write_unaligned(p as *mut u32, tagged.to_be());
        3
    } else if v <= max_value(4) {
        let tag_prefix = tag_prefix(4) >> 32;
        let tagged = (tag_prefix | v) as u32;
        std::ptr::write_unaligned(p as *mut u32, tagged.to_be());
        4
    } else if v <= max_value(8) {
        // This is a shortcut for len() where we assume the result is in 1..=8 (true here)
        let len = (70 - v.leading_zeros()) as usize / 7;
        let tag_prefix = tag_prefix(len);
        let tagged = tag_prefix | (v << (64 - (len * 8)));
        std::ptr::write_unaligned(p as *mut u64, tagged.to_be());
        len
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
    if v <= max_value(1) {
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
    if tag < 0b11000000 {
        (
            u64::from(u16::from_be(std::ptr::read_unaligned(p as *const u16))) & max_value(2),
            2,
        )
    } else if tag < 0b11100000 {
        (
            u64::from(u32::from_be(std::ptr::read_unaligned(p as *const u32)) >> 8) & max_value(3),
            3,
        )
    } else if tag < 0b11110000 {
        (
            u64::from(u32::from_be(std::ptr::read_unaligned(p as *const u32))) & max_value(4),
            4,
        )
    } else if tag < 0b11111111 {
        let len = tag.leading_ones() as usize + 1;
        let shift = (8 - len) * 8;
        let mask = !(u64::MAX << (len * 7));
        (
            (u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> shift) & mask,
            len,
        )
    } else {
        (
            u64::from_be(std::ptr::read_unaligned(p.add(1) as *const u64)),
            9,
        )
    }
}

/// Decode a prefix uvarint value from `p`, returning the raw value and number of bytes consumed.
///
/// # Safety
///
/// This assumes that bytes `p..=(p + MAX_LEN)` may be read from.
#[inline]
pub unsafe fn decode(p: *const u8) -> (u64, usize) {
    let tag = std::ptr::read(p);
    if tag <= max_value(1) as u8 {
        (tag.into(), 1)
    } else {
        decode_multibyte(tag, p)
    }
}
