//! Traits that allow writing/reading `PrefixVarInt` types on `bytes::{BufMut,Buf}`.

use crate::{
    decode_prefix_uvarint, DecodeError, PrefixVarInt, MAX_1BYTE_TAG, MAX_LEN, MAX_VALUE, TAG_PREFIX,
};
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
    #[inline]
    fn put_prefix_varint<PV: PrefixVarInt>(&mut self, v: PV) {
        let raw = v.to_prefix_varint_raw();
        if raw <= crate::MAX_VALUE[1] {
            self.put_u8(raw as u8);
        } else if self.chunk_mut().len() >= MAX_LEN {
            unsafe {
                let len = crate::encode_prefix_uvarint_slow(raw, self.chunk_mut().as_mut_ptr());
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
    fn get_prefix_varint<PV: PrefixVarInt>(&mut self) -> Result<PV, DecodeError>;
}

impl<Inner: Buf> PrefixVarIntBuf for Inner {
    #[inline]
    fn get_prefix_varint<PV: PrefixVarInt>(&mut self) -> Result<PV, DecodeError> {
        if self.remaining() == 0 {
            return Err(DecodeError::UnexpectedEob);
        }

        if self.chunk().len() >= MAX_LEN || self.remaining() == self.chunk().len() {
            let (raw, len) = unsafe { decode_prefix_uvarint(self.chunk().as_ptr()) };
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
