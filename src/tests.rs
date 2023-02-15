use rand::distributions::uniform::SampleUniform;
use rand::distributions::Uniform;
use rand::prelude::*;

trait PrefixVarIntBounds: Sized {
    fn prefix_varint_bounds() -> Vec<(Self, Self)>;
}

impl PrefixVarIntBounds for u64 {
    fn prefix_varint_bounds() -> Vec<(Self, Self)> {
        crate::MAX_VALUE
            .iter()
            .copied()
            .zip(crate::MAX_VALUE.iter().skip(1).copied())
            .map(|(min, max)| if min > 0 { (min + 1, max) } else { (min, max) })
            .collect()
    }
}

impl PrefixVarIntBounds for i64 {
    fn prefix_varint_bounds() -> Vec<(Self, Self)> {
        u64::prefix_varint_bounds()
            .into_iter()
            .map(|(_, max)| {
                (
                    crate::core::zigzag_decode(max),
                    crate::core::zigzag_decode(max - 1),
                )
            })
            .collect()
    }
}

fn generate_array<V: SampleUniform + Copy>(len: usize, min: V, max: V) -> Vec<V> {
    let mut rng = StdRng::from_seed([0xabu8; 32]);
    (0..len)
        .map(|_| Uniform::from(min..=max).sample(&mut rng))
        .collect::<Vec<_>>()
}

const RANDOM_TEST_LEN: usize = 4096;

mod core {
    use super::PrefixVarIntBounds;
    use crate::{DecodeError, PrefixVarInt, MAX_LEN};

    #[test]
    fn boundary_coding() {
        let mut buf = [0u8; MAX_LEN];
        for (len, (min, max)) in u64::prefix_varint_bounds()
            .into_iter()
            .enumerate()
            .map(|(i, x)| (i + 1, x))
        {
            assert_eq!(min.prefix_varint_len(), len, "{}", min);
            assert_eq!(min.encode_prefix_varint(&mut buf), len);
            assert_eq!((min, len), u64::decode_prefix_varint(&buf).unwrap());
            assert_eq!(max.prefix_varint_len(), len, "{}", max);
            assert_eq!(max.encode_prefix_varint(&mut buf), len);
            assert_eq!((max, len), u64::decode_prefix_varint(&buf).unwrap());
        }
    }

    #[test]
    fn signed_int() {
        let mut buf = [0u8; MAX_LEN];
        let v: i64 = -1;
        assert_eq!(v.prefix_varint_len(), 1);
        assert_eq!(v.encode_prefix_varint(&mut buf), 1);
        assert_eq!((v, 1), i64::decode_prefix_varint(&buf).unwrap());
    }

    #[test]
    fn uint16() {
        let mut buf = [0u8; MAX_LEN];
        assert_eq!(1024u16.prefix_varint_len(), 2);
        assert_eq!(1024u16.encode_prefix_varint(&mut buf), 2);
        assert_eq!((1024u16, 2), u16::decode_prefix_varint(&buf).unwrap());

        // Write something too large and decode it as u16
        (1u32 << 16).encode_prefix_varint(&mut buf);
        assert_eq!(Err(DecodeError::Overflow), u16::decode_prefix_varint(&buf));
    }

    #[test]
    fn uint32() {
        let mut buf = [0u8; MAX_LEN];
        assert_eq!(1048576u32.prefix_varint_len(), 3);
        assert_eq!(1048576u32.encode_prefix_varint(&mut buf), 3);
        assert_eq!((1048576u32, 3), u32::decode_prefix_varint(&buf).unwrap());

        // Write something too large and decode it as u16
        (1u64 << 32).encode_prefix_varint(&mut buf);
        assert_eq!(Err(DecodeError::Overflow), u32::decode_prefix_varint(&buf));
    }
}

mod buf {
    use super::{generate_array, PrefixVarIntBounds, RANDOM_TEST_LEN};
    use crate::{
        DecodeError, PrefixVarInt, PrefixVarIntBuf, PrefixVarIntBufMut, MAX_VALUE, TAG_PREFIX,
    };

    macro_rules! test_random_buf_put_get {
        ($int:ty, $name:ident) => {
            #[test]
            fn $name() {
                for (min, max) in <$int>::prefix_varint_bounds() {
                    let input_values = generate_array(RANDOM_TEST_LEN, min, max);
                    let mut buf_mut: Vec<u8> = Vec::new();
                    for v in input_values.iter() {
                        buf_mut.put_prefix_varint(*v);
                    }

                    let mut output_values: Vec<$int> = vec![];
                    let mut buf = buf_mut.as_slice();
                    for _ in 0..input_values.len() {
                        output_values.push(buf.get_prefix_varint().unwrap());
                    }

                    assert_eq!(input_values, output_values, "{}..{}", min, max);
                }
            }
        };
    }

    test_random_buf_put_get!(u64, random_u64);
    test_random_buf_put_get!(i64, random_i64);

    #[test]
    fn decode_empty_fail() {
        assert_eq!(
            u64::decode_prefix_varint(&mut [].as_slice()),
            Err(DecodeError::UnexpectedEob)
        );
    }

    #[test]
    fn decode_tag_only_fail() {
        let mut tag = u8::MAX;
        while tag != 0 {
            assert_eq!(
                u64::decode_prefix_varint(&mut [tag].as_slice()),
                Err(DecodeError::UnexpectedEob),
                "{:#b}",
                tag
            );
            tag <<= 1;
        }
    }

    #[test]
    fn decode_truncated() {
        for v in MAX_VALUE.iter().skip(1) {
            let mut buf = Vec::new();
            buf.put_prefix_varint(*v);
            let mut trunc = &buf[0..(buf.len() - 1)];
            assert_eq!(
                u64::decode_prefix_varint(&mut trunc),
                Err(DecodeError::UnexpectedEob),
                "{}",
                *v
            );
        }
    }

    #[test]
    fn decode_overflow() {
        let mut buf = Vec::new();
        buf.put_prefix_varint(u64::MAX);
        assert_eq!(
            u32::decode_prefix_varint(&mut buf.as_slice()),
            Err(DecodeError::Overflow)
        );
    }

    #[test]
    fn max_val_and_tag_prefix_cancel() {
        for i in 2..9 {
            let tag = TAG_PREFIX[i];
            let max = MAX_VALUE[i];
            assert_eq!(tag & max, 0);
        }
    }
}

mod io {
    use super::{generate_array, PrefixVarIntBounds, RANDOM_TEST_LEN};
    use crate::io::{read_prefix_varint, read_prefix_varint_buf, write_prefix_varint};

    macro_rules! test_random_io_write_read {
        ($name:ident, $int:ty) => {
            #[test]
            fn $name() {
                for (min, max) in <$int>::prefix_varint_bounds() {
                    let input_values = generate_array(RANDOM_TEST_LEN, min, max);
                    let mut writer: Vec<u8> = Vec::new();
                    for v in input_values.iter() {
                        write_prefix_varint(*v, &mut writer).unwrap();
                    }

                    let mut output_values = Vec::new();
                    let mut reader = writer.as_slice();
                    while let Ok(v) = read_prefix_varint::<$int>(&mut reader) {
                        output_values.push(v);
                    }

                    assert_eq!(input_values, output_values, "{}..{}", min, max);

                    output_values.clear();
                    let mut buf_reader = writer.as_slice();
                    while let Ok(v) = read_prefix_varint_buf::<$int>(&mut buf_reader) {
                        output_values.push(v);
                    }
                    assert_eq!(input_values, output_values, "{}..{}", min, max);
                }
            }
        };
    }
    test_random_io_write_read!(random_read_u64, u64);
    test_random_io_write_read!(random_read_i64, i64);
}
