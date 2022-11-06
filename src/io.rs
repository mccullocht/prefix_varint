//! Extensions to `std::io` traits to support reading/writing signed/unsigned prefix varints.
//!
//! `BufRead` should preferred over `Read` wherever possible as it should roughly halve the number
//! of calls to the underlying reader.
use std::io::{BufRead, Read, Result, Write};

use crate::{
    decode_prefix_uvarint, decode_prefix_uvarint_slow, encode_prefix_uvarint, zigzag_decode,
    zigzag_encode, MAX_1BYTE_TAG, MAX_LEN,
};

/// Extensions for `std::io::Write` to write unsigned/signed prefix varints.
pub trait VarintWrite: Write {
    /// Write a prefix uvarint. Returns the number of bytes written.`
    #[inline]
    fn write_prefix_uvarint(&mut self, v: u64) -> Result<usize> {
        let mut buf = [0u8; 16];
        let len = unsafe { encode_prefix_uvarint(v, buf.as_mut_ptr()) };
        self.write(&buf[..len])
    }

    /// Write a prefix varint. Returns the number of bytes written.`
    #[inline]
    fn write_prefix_varint(&mut self, v: i64) -> Result<usize> {
        self.write_prefix_uvarint(zigzag_encode(v))
    }
}

/// Implement for all types that implement 'std::io::Write`.
impl<W: Write + ?Sized> VarintWrite for W {}

#[inline]
fn read_prefix_uvarint_generic<R: Read + ?Sized>(r: &mut R) -> Result<u64> {
    let mut buf = [0u8; 16];
    r.read_exact(&mut buf[..1])?;
    if buf[0] <= MAX_1BYTE_TAG {
        return Ok(buf[0].into());
    }

    let extra_bytes = buf[0].leading_ones() as usize;
    r.read_exact(&mut buf[1..(extra_bytes + 1)])?;
    Ok(unsafe { decode_prefix_uvarint_slow(buf[0], buf.as_ptr()).0 })
}

/// Extensions for `std::io::Read` to read unsigned/signed prefix varints.
pub trait VarintRead: Read {
    fn read_prefix_uvarint(&mut self) -> Result<u64>;
    fn read_prefix_varint(&mut self) -> Result<i64>;
}

/// Implement for all types that implement `std::io::Read`.
impl<R: Read + ?Sized> VarintRead for R {
    /// Read a prefix uvarint, returning the value.
    #[inline]
    fn read_prefix_uvarint(&mut self) -> Result<u64> {
        read_prefix_uvarint_generic(self)
    }

    /// Read a prefix varint, returning the value.
    #[inline]
    fn read_prefix_varint(&mut self) -> Result<i64> {
        Ok(zigzag_decode(self.read_prefix_uvarint()?))
    }
}

/// Extensions for `std::io::BufRead` to read unsigned/signed prefix varints.
pub trait VarintBufRead: BufRead {
    fn read_prefix_uvarint(&mut self) -> Result<u64>;
    fn read_prefix_varint(&mut self) -> Result<i64>;
}

/// Implement for all types that implement `std::io::BufRead`.
impl<R: BufRead + ?Sized> VarintBufRead for R {
    /// Read a prefix uvarint, returning the value.
    #[inline]
    fn read_prefix_uvarint(&mut self) -> Result<u64> {
        let buf = self.fill_buf()?;
        if buf.len() >= MAX_LEN {
            let (v, len) = unsafe { decode_prefix_uvarint(buf.as_ptr()) };
            self.consume(len);
            Ok(v)
        } else {
            read_prefix_uvarint_generic(self)
        }
    }

    /// Read a prefix varint, returning the value.
    #[inline]
    fn read_prefix_varint(&mut self) -> Result<i64> {
        Ok(zigzag_decode(VarintBufRead::read_prefix_uvarint(self)?))
    }
}
