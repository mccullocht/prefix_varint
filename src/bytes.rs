//! Traits that allow writing/reading `PrefixVarInt` types on `bytes::{BufMut,Buf}`.

use crate::{raw, DecodeError, PrefixVarInt, MAX_1BYTE_TAG, MAX_LEN, MAX_VALUE, TAG_PREFIX};

use bytes::{Buf, BufMut};

fn put_prefix_varint_slow<B: BufMut>(v: u64, buf: &mut B) -> usize {
    if v <= MAX_VALUE[8] {
        let len = v.prefix_varint_len();
        buf.put_uint(v | TAG_PREFIX[len], len);
        len
    } else {
        buf.put_u8(u8::MAX);
        buf.put_u64(v);
        9
    }
}

/// Extension for `buf::BufMut` to write any `PrefixVarInt` type.
pub trait PrefixVarIntBufMut {
    fn put_prefix_varint<PV: PrefixVarInt>(&mut self, v: PV);
}

impl<Inner: BufMut> PrefixVarIntBufMut for Inner {
    /// Writes a `PrefixVarInt` value to the buffer.
    #[inline]
    fn put_prefix_varint<PV: PrefixVarInt>(&mut self, v: PV) {
        let raw = v.to_prefix_varint_raw();
        if raw <= crate::MAX_VALUE[1] {
            self.put_u8(raw as u8);
        } else if self.chunk_mut().len() >= MAX_LEN {
            unsafe {
                let len = raw::encode_multibyte(raw, self.chunk_mut().as_mut_ptr());
                self.advance_mut(len);
            }
        } else {
            put_prefix_varint_slow(raw, self);
        }
    }
}

fn get_prefix_varint_slow<B: Buf>(tag: u8, buf: &mut B) -> Result<u64, DecodeError> {
    let rem = tag.leading_ones() as usize;
    if rem > buf.remaining() {
        buf.advance(buf.remaining());
        Err(DecodeError::UnexpectedEob)
    } else if rem < 8 {
        let raw = (u64::from(tag) << (rem * 8)) | buf.get_uint(rem);
        Ok(raw & MAX_VALUE[rem + 1])
    } else {
        Ok(buf.get_u64())
    }
}

/// Extension for `buf::Buf` to read any `PrefixVarInt` type.
pub trait PrefixVarIntBuf {
    /// Reads a `PrefixVarInt` from the buffer. After a successful read, the
    /// buffer will be advanced by the number of bytes read.
    ///
    /// # Examples
    ///
    /// ```
    /// use prefix_uvarint::{PrefixVarIntBufMut, PrefixVarIntBuf};
    ///
    /// let to_encode = [1, 2, 400];
    /// let mut buf = vec![];
    /// for v in &to_encode {
    ///    buf.put_prefix_varint(*v);
    /// }
    ///
    /// let mut buf = &buf[..];
    /// for v in &to_encode {
    ///   let decoded = buf.get_prefix_varint::<u16>().unwrap();
    ///   assert_eq!(decoded, *v);
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an `UnexpectedEob` error if the buffer is empty or if the buffer
    /// is not long enough to contain the full encoded value.
    ///
    /// Returns an `Overflow` error if the encoded value is larger than the
    /// maximum value that can be represented by the `PrefixVarInt` type.
    fn get_prefix_varint<PV: PrefixVarInt>(&mut self) -> Result<PV, DecodeError>;

    // iter_prefix_varint method
    /// Returns an iterator over `PrefixVarInt` values in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use prefix_uvarint::{PrefixVarIntBufMut, PrefixVarIntBuf};
    ///
    /// let to_encode = [1, 2, -30, -24_000];
    /// let mut buf = vec![];
    /// for n in to_encode.iter() {
    ///     buf.put_prefix_varint(*n);
    /// }
    /// let mut result = vec![];
    /// let mut decode_data = buf.as_slice();
    /// for decoded in decode_data.iter_prefix_varint::<i16>() {
    ///     result.push(decoded.unwrap());
    /// }
    /// assert_eq!(to_encode, result.as_slice());
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an `UnexpectedEob` error if the buffer is empty or if the buffer
    /// is not long enough to contain the full encoded value.
    ///
    /// Returns an `Overflow` error if the encoded value is larger than the
    /// maximum value that can be represented by the `PrefixVarInt` type.
    fn iter_prefix_varint<PV: PrefixVarInt>(&mut self) -> PrefixVarIntIter<'_, Self, PV>
    where
        Self: Sized,
    {
        PrefixVarIntIter::new(self)
    }
}

impl<Inner: Buf> PrefixVarIntBuf for Inner {
    #[inline]
    fn get_prefix_varint<PV: PrefixVarInt>(&mut self) -> Result<PV, DecodeError> {
        if self.remaining() == 0 {
            return Err(DecodeError::UnexpectedEob);
        }

        if self.chunk().len() >= MAX_LEN {
            // SAFETY: we checked that the buffer is at least MAX_LEN bytes long
            // so we can always safely call decode_multibyte and never read
            // uninitialized memory.
            let (raw, len) = unsafe { raw::decode(self.chunk().as_ptr()) };
            self.advance(len);
            return PV::from_prefix_varint_raw(raw).ok_or(DecodeError::Overflow);
        }

        let tag = self.get_u8();
        if tag <= MAX_1BYTE_TAG {
            PV::from_prefix_varint_raw(tag.into()).ok_or(DecodeError::Overflow)
        } else {
            PV::from_prefix_varint_raw(get_prefix_varint_slow(tag, self)?)
                .ok_or(DecodeError::Overflow)
        }
    }
}

/// An iterator over `PrefixVarInt` values in a `Buf`.
pub struct PrefixVarIntIter<'a, B, PV> {
    buf: &'a mut B,
    _marker: std::marker::PhantomData<PV>,
}

// new method
impl<'a, B, PV> PrefixVarIntIter<'a, B, PV> {
    /// Creates a new `PrefixVarIntIter`.
    pub fn new(buf: &'a mut B) -> Self {
        Self {
            buf,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, B, PV> Iterator for PrefixVarIntIter<'a, B, PV>
where
    B: Buf,
    PV: PrefixVarInt,
{
    type Item = Result<PV, DecodeError>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.buf.has_remaining() {
            Some(self.buf.get_prefix_varint())
        } else {
            None
        }
    }
}
