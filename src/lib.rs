//! This module implements a prefix-based variable length integer coding scheme.
//!
//! Unlike an [LEB128](https://en.wikipedia.org/wiki/LEB128)-style encoding scheme, this encoding
//! uses a unary prefix code in the first byte of the value to indicate how many subsequent bytes
//! need to be read followed by the big endian encoding of any remaining bytes. This improves
//! coding speed compared to LEB128 by reducing the number of branches evaluated to code longer
//! values, and allows those branches to be different to improve branch mis-prediction.
//!
//! The `PrefixVarInt` trait is implemented for `u64`, `u32`, `u16`, `i64`, `i32`, and `i16`, with
//! values closer to zero producing small output. Signed values are written using a [Zigzag](https://en.wikipedia.org/wiki/Variable-length_quantity#Zigzag_encoding)
//! coding to ensure that small negative numbers produce small output.
//!
//! `PrefixVarInt` includes methods to code values directly to/from byte slices, but traits are
//! provided to extend `bytes::{Buf,BufMut}`, and to handle these values in `std::io::{Write,Read}.
//!
//! ```
//! use bytes::Buf;
//! use prefix_uvarint::{PrefixVarInt, PrefixVarIntBufMut, PrefixVarIntBuf};
//!
//! // value_buf is the maximum size needed to encode a value.
//! let mut value_buf = [0u8; prefix_uvarint::MAX_LEN];
//! assert_eq!(167894u64.encode_prefix_varint(&mut value_buf), 3);
//! assert_eq!((167894u64, 3), u64::decode_prefix_varint(&value_buf).unwrap());
//!
//! let mut buf_mut = vec![];
//! for v in (0..100).step_by(3) {
//!   buf_mut.put_prefix_varint(v);
//! }
//!
//! // NB: need a mutable slice to use as PrefixVarIntBufMut
//! let mut buf = buf_mut.as_slice();
//! while let Ok(v) = buf.get_prefix_varint::<u64>() {
//!   assert_eq!(v % 3, 0);
//! }
//! assert!(!buf.has_remaining());
//! ```
mod bytes;
pub(crate) mod core;
mod io;
mod raw;
#[cfg(test)]
mod tests;

pub use crate::bytes::{PrefixVarIntBuf, PrefixVarIntBufMut};
pub use crate::core::{DecodeError, EncodedPrefixVarInt, PrefixVarInt};
pub use crate::io::{read_prefix_varint, read_prefix_varint_buf, write_prefix_varint};

/// Maximum number of bytes a single encoded uvarint will occupy.
pub const MAX_LEN: usize = 9;

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

/// Tag prefix value for an n-byte length to OR with the value.
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

pub(crate) const MAX_1BYTE_TAG: u8 = MAX_VALUE[1] as u8;
