//! Extensions to `std::io` traits to support reading/writing prefix varints.
use std::io::{BufRead, Error, ErrorKind, Result, Write};

use crate::{DecodeError, PrefixVarInt, MAX_LEN};

impl From<DecodeError> for Error {
    fn from(value: DecodeError) -> Self {
        let kind = match value {
            DecodeError::UnexpectedEob => ErrorKind::UnexpectedEof,
            DecodeError::Overflow => ErrorKind::InvalidData,
        };
        Error::new(kind, value)
    }
}

/// Extension for `std::io::Write` to write any `PrefixVarInt` type.
pub trait PrefixVarIntWrite {
    /// Write a prefix varint to an output stream.
    fn write_prefix_varint<PV: PrefixVarInt>(&mut self, v: PV) -> Result<()>;
}

/// Implement `PrefixVarIntWrite` for all types that implement `Write`.
impl<Inner: Write> PrefixVarIntWrite for Inner {
    #[inline]
    fn write_prefix_varint<PV: PrefixVarInt>(&mut self, v: PV) -> Result<()> {
        self.write_all(v.to_prefix_varint_bytes().as_slice())
    }
}

/// Extension for `std::io::BufRead` to read any `PrefixVarInt` type.
pub trait PrefixVarIntRead {
    // Read prefix varint from input, returning the value.
    fn read_prefix_varint<PV: PrefixVarInt>(&mut self) -> Result<PV>;
}

/// Implement `PrefixVarIntRead` for all types that implement `BufRead`.
/// Note that `Read` is not supported -- the input ought to be buffered as reads will be small.
impl<Inner: BufRead> PrefixVarIntRead for Inner {
    #[inline]
    fn read_prefix_varint<PV: PrefixVarInt>(&mut self) -> Result<PV> {
        let mut buf = self.fill_buf()?;
        if buf.len() >= MAX_LEN {
            // XXX this is hellaciously unergonomic.
            let old_len = buf.len();
            let v = PV::decode_varint(&mut buf).map_err(|e| Error::from(e))?;
            let len = old_len - buf.len();
            self.consume(len);
            Ok(v)
        } else {
            let mut buf = [0u8; MAX_LEN];
            self.read_exact(&mut buf[..1])?;
            // XXX find a solution that allows us to bail early when buf[0] <= MAX_1BYTE_TAG
            // this will also be a problem if PrefixVarInt stop encoding directly to BufMut.
            let rem = buf[0].leading_ones() as usize;
            if rem > 0 {
                self.read_exact(&mut buf[1..(1 + rem)])?;
            }
            PV::decode_varint(&mut buf.as_slice()).map_err(|e| e.into())
        }
    }
}
