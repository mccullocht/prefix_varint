//! Routines for working with raw (u64) prefix varints.
//!
//! Other types should be shuffled to/from raw values using the `core::Int` trait.

const fn len_slow(v: u64) -> usize {
    if v < (1 << 63) {
        // Dividing by 7 triggers an optimization that yields a multiply instruction plus multiple
        // shifts and masks to produce the length and this is slower than the encode path.
        (70 - (v | 1).leading_zeros() as usize) / 7
    } else {
        9
    }
}

const fn compute_len_table() -> [u8; 64] {
    let mut tbl = [0u8; 64];
    let mut i = 0;
    while i < tbl.len() {
        let v = 1u64 << i;
        tbl[v.leading_zeros() as usize] = len_slow(v) as u8;
        i += 1;
    }
    tbl
}

const LEN_TABLE: [u8; 64] = compute_len_table();

/// Return the number of bytes required to encode `v` in `[1,MAX_LEN]`.
#[inline]
pub(crate) const fn len(v: u64) -> usize {
    LEN_TABLE[(v | 1).leading_zeros() as usize] as usize
}

#[inline(always)]
const fn tag_prefix(len: usize) -> u64 {
    !(u64::MAX >> (len - 1))
}

/// Returns the maximum value for a given byte length. Useful for masking out tag bits.
#[inline(always)]
pub(crate) const fn max_value(len: usize) -> u64 {
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
    } else if v <= max_value(5) {
        let tag_prefix = tag_prefix(5);
        let tagged = tag_prefix | (v << 24);
        std::ptr::write_unaligned(p as *mut u64, tagged.to_be());
        5
    } else if v <= max_value(6) {
        let tag_prefix = tag_prefix(6);
        let tagged = tag_prefix | (v << 16);
        std::ptr::write_unaligned(p as *mut u64, tagged.to_be());
        6
    } else if v <= max_value(7) {
        let tag_prefix = tag_prefix(7);
        let tagged = tag_prefix | (v << 8);
        std::ptr::write_unaligned(p as *mut u64, tagged.to_be());
        7
    } else if v <= max_value(8) {
        let tag_prefix = tag_prefix(8);
        let tagged = tag_prefix | v;
        std::ptr::write_unaligned(p as *mut u64, tagged.to_be());
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
    } else if tag < 0b11111000 {
        (
            u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 24 & max_value(5),
            5,
        )
    } else if tag < 0b11111100 {
        (
            u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 16 & max_value(6),
            6,
        )
    } else if tag < 0b11111110 {
        (
            u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 8 & max_value(7),
            7,
        )
    } else if tag < 0b11111111 {
        (
            u64::from_be(std::ptr::read_unaligned(p as *const u64)) & max_value(8),
            8,
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
