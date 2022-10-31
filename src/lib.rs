/// TODO: module level comment with an explanation of the encoding and API usage.
///
use bytes::buf::{Buf, BufMut};

/// Maximum number of bytes a single encoded uvarint will occupy.
pub const MAX_LEN: usize = 9;

/// Maximum value for a 1-byte tag (0 leading ones).
// TODO: replace with MAX_VALUE[1]
const TAG_1BYTE_MAX: u8 = 0x7f;

// alt: make N leading zeros and invert.
// so: 8, 7, 6, 5, 4, 3, 2, 1, 0
// (1 << N) - 1 is good unless N is 0 or 8.
// in terms of u8::MAX???
fn make_tag_prefix<const N: usize>() -> u8 {
    match N {
        0 => 0b00000000u8,
        1 => 0b10000000u8,
        2 => 0b11000000u8,
        3 => 0b11100000u8,
        4 => 0b11110000u8,
        5 => 0b11111000u8,
        6 => 0b11111100u8,
        7 => 0b11111110u8,
        _ => 0b11111111u8,
    }
}

// TODO: remove this in favor of VALUE_MASK.
fn make_tag_value_mask<const N: usize>() -> u8 {
    match N {
        0 => 0b01111111u8,
        1 => 0b00111111u8,
        2 => 0b00011111u8,
        3 => 0b00001111u8,
        4 => 0b00000111u8,
        5 => 0b00000011u8,
        6 => 0b00000001u8,
        _ => 0b00000000u8,
    }
}

fn make_tag<const N: usize>(v: u64) -> u8 {
    if N < 8 {
        let v8: u8 = (v >> (N * 8)).try_into().unwrap();
        (v8 & make_tag_value_mask::<N>()) | make_tag_prefix::<N>()
    } else {
        u8::MAX
    }
}

/// Maps negative values to positive values, creating a sequence that alternates between negative
/// and positive values. This makes the value more amenable to efficient prefix uvarint encoding.
fn zigzag_encode(v: i64) -> u64 {
    ((v >> 63) ^ (v << 1)) as u64
}

/// Inverts `zigzag_encode()`.
fn zigzag_decode(v: u64) -> i64 {
    (v >> 1) as i64 ^ -(v as i64 & 1)
}

/// Max value for an n-byte length.
const MAX_VALUE: [u64; 10] = [
    0x0,
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
    0x0,
    0x0,
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

/// Encodes `v` as a prefix uvarint to `p`.
///
/// This may write up to `MAX_LEN` bytes and may panic if fewer bytes are available.
#[inline]
pub unsafe fn encode_prefix_varint(v: i64, p: *mut u8) -> usize {
    encode_prefix_uvarint(zigzag_encode(v), p)
}

fn put_prefix_uvarint_slow<B: bytes::BufMut + ?Sized>(b: &mut B, v: u64) {
    if v < (1 << 14) {
        b.put_u8(make_tag::<1>(v));
        b.put_u8(v as u8);
    } else if v < (1 << 21) {
        b.put_u8(make_tag::<2>(v));
        b.put_u16(v as u16)
    } else if v < (1 << 28) {
        b.put_u8(make_tag::<3>(v));
        b.put_uint(v, 3)
    } else if v < (1 << 35) {
        b.put_u8(make_tag::<4>(v));
        b.put_u32(v as u32)
    } else if v < (1 << 42) {
        b.put_u8(make_tag::<5>(v));
        b.put_uint(v, 5)
    } else if v < (1 << 49) {
        b.put_u8(make_tag::<6>(v));
        b.put_uint(v, 6)
    } else if v < (1 << 56) {
        b.put_u8(make_tag::<7>(v));
        b.put_uint(v, 7)
    } else {
        b.put_u8(make_tag::<8>(v));
        b.put_u64(v)
    }
}

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

// Implement for all tyeps that implement BufMut
impl<B: BufMut + ?Sized> VarintBufMut for B {}

/// Mask for an n-byte length value that removes prefix code bits.
// TODO: replace with MAX_VALUE
const VALUE_MASK: [u64; 10] = [
    0x0,
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

unsafe fn decode_prefix_uvarint_slow(tag: u8, p: *const u8) -> (u64, usize) {
    let (raw, len) = match tag.leading_ones() {
        // NB: zero is handled by decode_prefix_uvarint().
        1 => (
            u16::from_be(std::ptr::read_unaligned(p as *const u16)).into(),
            2,
        ),
        2 => (
            (u32::from_be(std::ptr::read_unaligned(p as *const u32)) >> 8).into(),
            3,
        ),
        3 => (
            u32::from_be(std::ptr::read_unaligned(p as *const u32)).into(),
            4,
        ),
        4 => (
            (u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 24).into(),
            5,
        ),
        5 => (
            (u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 16).into(),
            6,
        ),
        6 => (
            (u64::from_be(std::ptr::read_unaligned(p as *const u64)) >> 8).into(),
            7,
        ),
        7 => (
            u64::from_be(std::ptr::read_unaligned(p as *const u64)).into(),
            8,
        ),
        // NB: this is a catch-all but the maximum possible value for tag.leading_ones() is 8.
        _ => (
            u64::from_be(std::ptr::read_unaligned(p.add(1) as *const u64)),
            9,
        ),
    };
    (raw & VALUE_MASK[len], len)
}

/// Decodes a prefix uvarint value from `p`, returning the value and the number of bytes consumed.
///
/// This function may read up to `MAX_LEN` bytes from `p` and may panic if fewer bytes are available.
#[inline]
pub unsafe fn decode_prefix_uvarint(p: *const u8) -> (u64, usize) {
    let tag = std::ptr::read(p);
    if tag <= TAG_1BYTE_MAX {
        return (tag.into(), 1);
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
        return None;
    }

    let raw = match remaining_bytes {
        1 => (u64::from(tag & make_tag_value_mask::<1>()) << 8) | b.get_uint(1),
        2 => (u64::from(tag & make_tag_value_mask::<2>()) << 16) | u64::from(b.get_u16()),
        3 => (u64::from(tag & make_tag_value_mask::<3>()) << 24) | b.get_uint(3),
        4 => (u64::from(tag & make_tag_value_mask::<4>()) << 32) | u64::from(b.get_u32()),
        5 => (u64::from(tag & make_tag_value_mask::<5>()) << 40) | b.get_uint(5),
        6 => (u64::from(tag & make_tag_value_mask::<6>()) << 48) | b.get_uint(6),
        7 => (u64::from(tag & make_tag_value_mask::<7>()) << 56) | b.get_uint(7),
        _ => b.get_u64(),
    };
    Some(raw)
}

pub trait VarintBuf: bytes::Buf {
    /// Reads a single value written by `VarintBufMut.put_prefix_uvarint()`.
    /// Returns `None` if there are not enough remaining bytes to produce a value, in which case
    /// the buffer may be left in an indeterminate state.
    #[inline]
    fn get_prefix_uvarint(&mut self) -> Option<u64> {
        let buf = self.chunk();
        if buf.len() >= MAX_LEN {
            let (value, len) = unsafe { decode_prefix_uvarint(buf.as_ptr()) };
            self.advance(len);
            Some(value)
        } else if !self.has_remaining() {
            return None;
        } else {
            let tag = self.get_u8();
            if tag <= TAG_1BYTE_MAX {
                Some(tag.into())
            } else {
                get_prefix_uvarint_slow(self, tag)
            }
        }
    }

    /// Reads a single value written by `VarintBufMut.put_prefix_varint()`.
    /// Returns `None` if there are not enough remaining bytes to produce a value, in which case
    /// the buffer may be left in an indeterminate state.
    #[inline]
    fn get_prefix_varint(&mut self) -> Option<i64> {
        let v = self.get_prefix_uvarint()?;
        Some(zigzag_decode(v))
    }
}

// Implement for all types that implement Buf.
impl<B: Buf + ?Sized> VarintBuf for B {}

#[cfg(test)]
mod test {
    use super::*;
    use rand::distributions::Uniform;
    use rand::prelude::*;

    macro_rules! test_encode_decode1 {
        ($name:ident, $value:literal, $size:literal) => {
            #[test]
            fn $name() {
                let mut buf: Vec<u8> = Vec::new();
                buf.put_prefix_uvarint($value);
                assert_eq!($size, buf.len());
                assert_eq!(Some($value), buf.as_slice().get_prefix_uvarint());
            }
        };
    }

    test_encode_decode1!(min_1byte, 0x0, 1);
    test_encode_decode1!(max_1byte, 0x7f, 1);
    test_encode_decode1!(min_2byte, 0x80, 2);
    test_encode_decode1!(max_2byte, 0x3fff, 2);
    test_encode_decode1!(min_3byte, 0x4000, 3);
    test_encode_decode1!(max_3byte, 0x1fffff, 3);
    test_encode_decode1!(min_4byte, 0x200000, 4);
    test_encode_decode1!(max_4byte, 0xfffffff, 4);

    test_encode_decode1!(min_5byte, 0x10000000, 5);
    test_encode_decode1!(max_5byte, 0x7ffffffff, 5);
    test_encode_decode1!(min_6byte, 0x800000000, 6);
    test_encode_decode1!(max_6byte, 0x3ffffffffff, 6);
    test_encode_decode1!(min_7byte, 0x40000000000, 7);
    test_encode_decode1!(max_7byte, 0x1ffffffffffff, 7);
    test_encode_decode1!(min_8byte, 0x2000000000000, 8);
    test_encode_decode1!(max_8byte, 0xffffffffffffff, 8);
    test_encode_decode1!(min_9byte, 0x100000000000000, 9);
    test_encode_decode1!(max_9byte, 0xffffffffffffffff, 9);

    macro_rules! test_encode_decode {
        ($name:ident, $expected:expr) => {
            #[test]
            fn $name() {
                let mut wbuf: Vec<u8> = Vec::new();
                for v in $expected {
                    wbuf.put_prefix_uvarint(v);
                }

                let mut rbuf = wbuf.as_slice();
                let mut actual: Vec<u64> = Vec::new();
                while let Some(v) = rbuf.get_prefix_uvarint() {
                    actual.push(v);
                }
                assert_eq!($expected.as_slice(), actual);
                assert_eq!(rbuf.len(), 0);
            }
        };
    }

    test_encode_decode!(
        ascending,
        [
            0x7f,
            0x3ff,
            0x1fffff,
            0xfffffff,
            0x7ffffffff,
            0x3ffffffffff,
            0x1ffffffffffff,
            0xffffffffffffff,
            0xffffffffffffffff
        ]
    );

    test_encode_decode!(
        descending,
        [
            0xffffffffffffffff,
            0xffffffffffffff,
            0x1ffffffffffff,
            0x3ffffffffff,
            0x7ffffffff,
            0xfffffff,
            0x1fffff,
            0x3ff,
            0x7f,
        ]
    );

    const RANDOM_TEST_LEN: usize = 128;
    macro_rules! test_random_encode_decode_uvarint {
        ($name:ident, $max_value:literal) => {
            #[test]
            fn $name() {
                let mut rng = StdRng::from_seed([0xabu8; 32]);
                let input_values = (0..RANDOM_TEST_LEN)
                    .map(|_| Uniform::from(0..$max_value).sample(&mut rng))
                    .collect::<Vec<_>>();
                let mut buf_mut: Vec<u8> = Vec::new();
                for v in input_values.iter() {
                    buf_mut.put_prefix_uvarint(*v);
                }

                let mut output_values = Vec::new();
                let mut buf = buf_mut.as_slice();
                for _ in 0..RANDOM_TEST_LEN {
                    output_values.push(buf.get_prefix_uvarint().unwrap());
                }

                assert_eq!(input_values, output_values);
            }
        };
    }

    test_random_encode_decode_uvarint!(uvarint_1byte, 0x7f);
    test_random_encode_decode_uvarint!(uvarint_2byte, 0x3fff);
    test_random_encode_decode_uvarint!(uvarint_3byte, 0x1fffff);
    test_random_encode_decode_uvarint!(uvarint_4byte, 0xfffffff);
    test_random_encode_decode_uvarint!(uvarint_5byte, 0x7ffffffff);
    test_random_encode_decode_uvarint!(uvarint_6byte, 0x3ffffffffff);
    test_random_encode_decode_uvarint!(uvarint_7byte, 0x1ffffffffffff);
    test_random_encode_decode_uvarint!(uvarint_8byte, 0xffffffffffffff);
    test_random_encode_decode_uvarint!(uvarint_9byte, 0xffffffffffffffff);

    macro_rules! test_random_encode_decode_varint {
        ($name:ident, $max_value:literal) => {
            #[test]
            fn $name() {
                let mut rng = StdRng::from_seed([0xabu8; 32]);
                let min_value = -$max_value - 1;
                let input_values = (0..RANDOM_TEST_LEN)
                    .map(|_| Uniform::from(min_value..$max_value).sample(&mut rng))
                    .collect::<Vec<_>>();
                let mut buf_mut: Vec<u8> = Vec::new();
                for v in input_values.iter() {
                    buf_mut.put_prefix_varint(*v);
                }

                let mut output_values = Vec::new();
                let mut buf = buf_mut.as_slice();
                for _ in 0..RANDOM_TEST_LEN {
                    output_values.push(buf.get_prefix_varint().unwrap());
                }

                assert_eq!(input_values, output_values);
            }
        };
    }

    test_random_encode_decode_varint!(varint_1byte, 63);
    test_random_encode_decode_varint!(varint_2byte, 8191);
    test_random_encode_decode_varint!(varint_3byte, 1048575);
    test_random_encode_decode_varint!(varint_4byte, 134217727);
    test_random_encode_decode_varint!(varint_5byte, 17179869183);
    test_random_encode_decode_varint!(varint_6byte, 2199023255551);
    test_random_encode_decode_varint!(varint_7byte, 281474976710655);
    test_random_encode_decode_varint!(varint_8byte, 36028797018963967);
    test_random_encode_decode_varint!(varint_9byte, 9223372036854775807);

    // TODO: decoding tests for data loss cases.
}
