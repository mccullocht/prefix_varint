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
            .map(|(_, max)| (crate::zigzag_decode(max), crate::zigzag_decode(max - 1)))
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

mod raw {
    use super::PrefixVarIntBounds;
    use crate::{decode_prefix_uvarint, encode_prefix_uvarint, prefix_uvarint_len, MAX_LEN};

    #[test]
    fn boundary_coding() {
        let mut buf = [0u8; MAX_LEN];
        for (len, (min, max)) in u64::prefix_varint_bounds()
            .into_iter()
            .enumerate()
            .map(|(i, x)| (i + 1, x))
        {
            assert_eq!(prefix_uvarint_len(min), len, "{}", min);
            assert_eq!(unsafe { encode_prefix_uvarint(min, buf.as_mut_ptr()) }, len);
            assert_eq!(unsafe { decode_prefix_uvarint(buf.as_ptr()) }, (min, len));
            assert_eq!(prefix_uvarint_len(max), len, "{}", max);
            assert_eq!(unsafe { encode_prefix_uvarint(max, buf.as_mut_ptr()) }, len);
            assert_eq!(unsafe { decode_prefix_uvarint(buf.as_ptr()) }, (max, len));
        }
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
    use crate::io::{PrefixVarIntRead, PrefixVarIntWrite};

    macro_rules! test_random_io_write_read {
        ($name:ident, $int:ty) => {
            #[test]
            fn $name() {
                for (min, max) in <$int>::prefix_varint_bounds() {
                    let input_values = generate_array(RANDOM_TEST_LEN, min, max);
                    let mut writer: Vec<u8> = Vec::new();
                    for v in input_values.iter() {
                        writer.write_prefix_varint(*v).unwrap();
                    }

                    let mut output_values = Vec::new();
                    let mut reader = writer.as_slice();
                    while let Ok(v) = reader.read_prefix_varint::<$int>() {
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
