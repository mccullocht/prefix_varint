//! Extensions to `std::io` traits to support reading/writing prefix varints.
use std::io::{BufRead, Error, ErrorKind, Read, Result, Write};

use crate::raw::{encode_multibyte_writer_skip_2, max_value, tag_prefix};
use crate::{DecodeError, PrefixVarInt, MAX_1BYTE_TAG, MAX_LEN};

impl From<DecodeError> for Error {
    fn from(value: DecodeError) -> Self {
        let kind = match value {
            DecodeError::UnexpectedEob => ErrorKind::UnexpectedEof,
            DecodeError::Overflow => ErrorKind::InvalidData,
        };
        Error::new(kind, value)
    }
}

/// Prefix varint code a value and write it to `w`. Returns the number of bytes
/// written.
#[inline]
pub fn write_prefix_varint<PV: PrefixVarInt>(v: PV, w: &mut impl Write) -> Result<usize> {
    let v = v.to_prefix_varint_raw();
    if v <= max_value(1) {
        return w.write_all(&[v as u8]).map(|_| 1);
    } else if v <= max_value(2) {
        let tag_prefix = tag_prefix(2) >> 48;
        let tagged = (v | tag_prefix) as u16;
        return w.write_all(&tagged.to_be_bytes()).map(|_| 2);
    }
    encode_multibyte_writer_skip_2(v, w)
}

/// Read and decode a prefix varint value from `r`.
/// Prefer `read_prefix_varint_buf()` wherever possible as it should be more efficient.
#[inline]
pub fn read_prefix_varint<PV: PrefixVarInt>(r: &mut impl Read) -> Result<PV> {
    let mut buf = [0u8; MAX_LEN];
    r.read_exact(&mut buf[..1])?;
    let tag = buf[0];
    if tag <= MAX_1BYTE_TAG {
        return PV::from_prefix_varint_raw(tag.into()).ok_or_else(|| DecodeError::Overflow.into());
    }
    let rem = tag.leading_ones() as usize;
    r.read_exact(&mut buf[1..(1 + rem)])?;
    PV::decode_prefix_varint(buf.as_slice())
        .map(|(v, _)| v)
        .map_err(|e| e.into())
}

/// Read and decode a prefix varint value from `r`.
#[inline]
pub fn read_prefix_varint_buf<PV: PrefixVarInt>(r: &mut impl BufRead) -> Result<PV> {
    let buf = r.fill_buf()?;
    if buf.len() >= MAX_LEN {
        let (v, len) = PV::decode_prefix_varint(buf).map_err(Error::from)?;
        r.consume(len);
        Ok(v)
    } else {
        read_prefix_varint(r)
    }
}
