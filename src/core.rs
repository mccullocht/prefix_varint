use crate::MAX_LEN;

/// Base integer trait for prefix varints. Provides internal APIs to facilitate the transforms in
/// the PrefixVarInt trait.
pub trait Int: Sized + Copy {
    fn to_prefix_varint_raw(self) -> u64;
    fn from_prefix_varint_raw(r: u64) -> Option<Self>;
}

impl Int for u64 {
    #[inline(always)]
    fn to_prefix_varint_raw(self) -> u64 {
        self
    }
    #[inline(always)]
    fn from_prefix_varint_raw(raw: u64) -> Option<Self> {
        Some(raw)
    }
}

impl Int for i64 {
    #[inline(always)]
    fn to_prefix_varint_raw(self) -> u64 {
        crate::zigzag_encode(self)
    }
    #[inline(always)]
    fn from_prefix_varint_raw(raw: u64) -> Option<Self> {
        Some(crate::zigzag_decode(raw))
    }
}

macro_rules! impl_int {
    ($int:ty, $pint:ty) => {
        impl Int for $int {
            #[inline(always)]
            fn to_prefix_varint_raw(self) -> u64 {
                <$pint>::from(self).to_prefix_varint_raw()
            }
            #[inline(always)]
            fn from_prefix_varint_raw(raw: u64) -> Option<Self> {
                let v = <$pint>::from_prefix_varint_raw(raw)?;
                v.try_into().ok()
            }
        }
    };
}
impl_int!(u16, u64);
impl_int!(u32, u64);
impl_int!(i16, i64);
impl_int!(i32, i64);

#[inline(always)]
fn decode_prefix_varint_raw(buf: &[u8]) -> Result<(u64, usize), crate::DecodeError> {
    if buf.is_empty() {
        return Err(crate::DecodeError::UnexpectedEob);
    }

    if buf.len() >= MAX_LEN {
        return Ok(unsafe { crate::decode_prefix_uvarint(buf.as_ptr()) });
    }

    let tag = buf[0];
    if tag <= crate::MAX_1BYTE_TAG {
        return Ok((tag.into(), 1));
    }

    let len = tag.leading_ones() as usize + 1;
    if len <= buf.len() {
        let mut ibuf = [0u8; crate::MAX_LEN];
        ibuf[..len].copy_from_slice(&buf[..len]);
        Ok(unsafe { crate::decode_prefix_uvarint_slow(tag, ibuf.as_ptr()) })
    } else {
        Err(crate::DecodeError::UnexpectedEob)
    }
}

/// Trait for integer types that can be prefix varint coded.
///
/// Signed integer types are zigzag coded before encoding/after decoding.
pub trait PrefixVarInt: Sized + Copy + Int {
    /// Returns the number of bytes required to encode `self`.
    /// This value will always be in `[1, MAX_LEN]`
    fn prefix_varint_len(self) -> usize {
        crate::prefix_uvarint_len(self.to_prefix_varint_raw())
    }

    /// Encode `self` to buf and return the number of bytes written.
    ///
    /// # Panics
    ///
    /// If `self.prefix_varint_len() > buf.remaining()`.
    fn encode_prefix_varint(self, buf: &mut [u8]) -> usize {
        if buf.len() >= crate::MAX_LEN {
            unsafe { crate::encode_prefix_uvarint(self.to_prefix_varint_raw(), buf.as_mut_ptr()) }
        } else {
            let enc = self.to_prefix_varint_bytes();
            let ebytes = enc.as_slice();
            buf[..ebytes.len()].copy_from_slice(ebytes);
            ebytes.len()
        }
    }

    /// Decode an integer from the bytes in `buf` and return the value and number of bytes consumed.
    fn decode_prefix_varint(buf: &[u8]) -> Result<(Self, usize), crate::DecodeError> {
        let (raw, len) = decode_prefix_varint_raw(buf)?;
        Ok((
            Self::from_prefix_varint_raw(raw).ok_or(crate::DecodeError::Overflow)?,
            len,
        ))
    }

    /// Encode `self` to an owned buffer and return it.
    /// Use `as_slice()` to access the encoded bytes.
    fn to_prefix_varint_bytes(self) -> crate::EncodedPrefixVarint {
        crate::EncodedPrefixVarint::new(self.to_prefix_varint_raw())
    }
}

impl PrefixVarInt for u16 {}
impl PrefixVarInt for u32 {}
impl PrefixVarInt for u64 {}
impl PrefixVarInt for i16 {}
impl PrefixVarInt for i32 {}
impl PrefixVarInt for i64 {}
