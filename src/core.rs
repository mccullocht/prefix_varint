use crate::{raw, MAX_1BYTE_TAG, MAX_LEN};

/// Errors that may occur when decoding a `PrefixVarInt`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DecodeError {
    /// Reached end-of-buffer unexpectedly.
    ///
    /// This may happen if you attempt to decode an empty buffer or if the buffer is too short to
    /// contain the expected value.
    UnexpectedEob,
    /// The value read is larger than the destination type.
    Overflow,
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for DecodeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }

    fn description(&self) -> &str {
        ""
    }

    fn cause(&self) -> Option<&dyn std::error::Error> {
        None
    }
}

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

/// Maps negative values to positive values, creating a sequence that alternates between negative
/// and positive values. This makes the value more amenable to efficient prefix uvarint encoding.
#[inline]
pub(crate) fn zigzag_encode(v: i64) -> u64 {
    ((v >> 63) ^ (v << 1)) as u64
}

/// Inverts `zigzag_encode()`.
#[inline]
pub(crate) fn zigzag_decode(v: u64) -> i64 {
    (v >> 1) as i64 ^ -(v as i64 & 1)
}

impl Int for i64 {
    #[inline(always)]
    fn to_prefix_varint_raw(self) -> u64 {
        zigzag_encode(self)
    }
    #[inline(always)]
    fn from_prefix_varint_raw(raw: u64) -> Option<Self> {
        Some(zigzag_decode(raw))
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

/// A single encoded prefix varint value for with `PrefixVarInt.to_prefix_varint_bytes()`.
pub struct EncodedPrefixVarInt {
    buf: [u8; MAX_LEN],
    len: u8,
}

#[allow(clippy::len_without_is_empty)]
impl EncodedPrefixVarInt {
    fn new(v: u64) -> Self {
        let mut enc = Self::default();
        let len = unsafe { raw::encode(v, enc.buf.as_mut_ptr()) };
        enc.len = len as u8;
        enc
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.buf[..self.len()]
    }

    /// Returns the number of bytes used to encode the value.
    pub fn len(&self) -> usize {
        self.len as usize
    }
}

impl Default for EncodedPrefixVarInt {
    fn default() -> Self {
        Self {
            buf: [0u8; MAX_LEN],
            len: 0,
        }
    }
}

#[inline(always)]
fn decode_raw(buf: &[u8]) -> Result<(u64, usize), DecodeError> {
    if buf.is_empty() {
        return Err(DecodeError::UnexpectedEob);
    }

    if buf.len() >= MAX_LEN {
        return Ok(unsafe { raw::decode(buf.as_ptr()) });
    }

    let tag = buf[0];
    if tag <= MAX_1BYTE_TAG {
        return Ok((tag.into(), 1));
    }

    let len = tag.leading_ones() as usize + 1;
    if len <= buf.len() {
        let mut ibuf = [0u8; MAX_LEN];
        ibuf[..len].copy_from_slice(&buf[..len]);
        Ok(unsafe { raw::decode_multibyte(tag, ibuf.as_ptr()) })
    } else {
        Err(DecodeError::UnexpectedEob)
    }
}

/// Trait for integer types that can be prefix varint coded.
///
/// Signed integer types are zigzag coded before encoding/after decoding.
pub trait PrefixVarInt: Sized + Copy + Int {
    /// Returns the number of bytes required to encode `self`.
    /// This value will always be in `[1, MAX_LEN]`
    #[inline]
    fn prefix_varint_len(self) -> usize {
        raw::len(self.to_prefix_varint_raw())
    }

    /// Encode `self` to buf and return the number of bytes written.
    ///
    /// # Panics
    ///
    /// If `self.prefix_varint_len() > buf.len()`.
    #[inline]
    fn encode_prefix_varint(self, buf: &mut [u8]) -> usize {
        if buf.len() >= MAX_LEN {
            unsafe { raw::encode(self.to_prefix_varint_raw(), buf.as_mut_ptr()) }
        } else {
            let enc = self.to_prefix_varint_bytes();
            let ebytes = enc.as_slice();
            buf[..ebytes.len()].copy_from_slice(ebytes);
            ebytes.len()
        }
    }

    /// Decode an integer from the bytes in `buf` and return the value and number of bytes consumed.
    #[inline]
    fn decode_prefix_varint(buf: &[u8]) -> Result<(Self, usize), DecodeError> {
        let (raw, len) = decode_raw(buf)?;
        Ok((
            Self::from_prefix_varint_raw(raw).ok_or(DecodeError::Overflow)?,
            len,
        ))
    }

    /// Encode `self` to an owned buffer and return it.
    /// Use `as_slice()` to access the encoded bytes.
    #[inline]
    fn to_prefix_varint_bytes(self) -> EncodedPrefixVarInt {
        EncodedPrefixVarInt::new(self.to_prefix_varint_raw())
    }
}

impl PrefixVarInt for u16 {}
impl PrefixVarInt for u32 {}
impl PrefixVarInt for u64 {}
impl PrefixVarInt for i16 {}
impl PrefixVarInt for i32 {}
impl PrefixVarInt for i64 {}
