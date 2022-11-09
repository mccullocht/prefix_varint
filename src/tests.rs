use rand::distributions::uniform::SampleUniform;
use rand::distributions::Uniform;
use rand::prelude::*;

fn bounds_u64() -> impl Iterator<Item = (u64, u64)> {
    crate::MAX_VALUE
        .iter()
        .copied()
        .zip(crate::MAX_VALUE.iter().skip(1).copied())
        .map(|(min, max)| if min > 0 { (min + 1, max) } else { (min, max) })
}

fn bounds_i64() -> impl Iterator<Item = (i64, i64)> {
    bounds_u64().map(|(_, max)| (crate::zigzag_decode(max), crate::zigzag_decode(max - 1)))
}

fn generate_array<V: SampleUniform + Copy>(len: usize, min: V, max: V) -> Vec<V> {
    let mut rng = StdRng::from_seed([0xabu8; 32]);
    (0..len)
        .map(|_| Uniform::from(min..=max).sample(&mut rng))
        .collect::<Vec<_>>()
}

const RANDOM_TEST_LEN: usize = 4096;

mod raw {
    use super::bounds_u64;
    use crate::{decode_prefix_uvarint, encode_prefix_uvarint, MAX_LEN};

    #[test]
    fn boundary_coding() {
        let mut buf = [0u8; MAX_LEN];
        for (len, (min, max)) in bounds_u64().enumerate().map(|(i, x)| (i + 1, x)) {
            assert_eq!(unsafe { encode_prefix_uvarint(min, buf.as_mut_ptr()) }, len);
            assert_eq!(unsafe { decode_prefix_uvarint(buf.as_ptr()) }, (min, len));
            assert_eq!(unsafe { encode_prefix_uvarint(max, buf.as_mut_ptr()) }, len);
            assert_eq!(unsafe { decode_prefix_uvarint(buf.as_ptr()) }, (max, len));
        }
    }
}

mod buf {
    use super::{bounds_i64, bounds_u64, generate_array, RANDOM_TEST_LEN};
    use crate::{VarintBuf, VarintBufMut, MAX_VALUE, TAG_PREFIX};

    macro_rules! test_random_buf_put_get {
        ($name:ident, $bounds:ident, $put:ident, $get:ident) => {
            #[test]
            fn $name() {
                for (min, max) in $bounds() {
                    let input_values = generate_array(RANDOM_TEST_LEN, min, max);
                    let mut buf_mut: Vec<u8> = Vec::new();
                    for v in input_values.iter() {
                        buf_mut.$put(*v);
                    }

                    let mut output_values = Vec::new();
                    let mut buf = buf_mut.as_slice();
                    for _ in 0..input_values.len() {
                        output_values.push(buf.$get().unwrap());
                    }

                    assert_eq!(input_values, output_values, "{}..{}", min, max);
                }
            }
        };
    }

    test_random_buf_put_get!(
        random_u64,
        bounds_u64,
        put_prefix_uvarint,
        get_prefix_uvarint
    );
    test_random_buf_put_get!(random_i64, bounds_i64, put_prefix_varint, get_prefix_varint);

    #[test]
    fn decode_empty_fail() {
        assert_eq!([].as_slice().get_prefix_uvarint(), None);
    }

    #[test]
    fn decode_tag_only_fail() {
        let mut tag = u8::MAX;
        while tag != 0 {
            assert_eq!([tag].as_slice().get_prefix_uvarint(), None, "{:#b}", tag);
            tag <<= 1;
        }
    }

    #[test]
    fn decode_truncated() {
        for v in MAX_VALUE.iter().skip(1) {
            let mut buf = Vec::new();
            buf.put_prefix_uvarint(*v);
            let mut trunc = &buf[0..(buf.len() - 1)];
            assert_eq!(trunc.get_prefix_uvarint(), None, "{}", *v);
        }
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
    use super::{bounds_i64, bounds_u64, generate_array, RANDOM_TEST_LEN};
    use crate::io::VarintWrite;

    macro_rules! test_random_io_write_read {
        ($name:ident, $reader:ident, $bounds:ident, $write:ident, $read:ident) => {
            #[test]
            fn $name() {
                use crate::io::$reader;

                for (min, max) in $bounds() {
                    let input_values = generate_array(RANDOM_TEST_LEN, min, max);
                    let mut write: Vec<u8> = Vec::new();
                    for v in input_values.iter() {
                        write.$write(*v).unwrap();
                    }

                    let mut output_values = Vec::new();
                    let mut read = write.as_slice();
                    while let Ok(v) = read.$read() {
                        output_values.push(v);
                    }

                    assert_eq!(input_values, output_values, "{}..{}", min, max);
                }
            }
        };
    }
    test_random_io_write_read!(
        random_read_u64,
        VarintRead,
        bounds_u64,
        write_prefix_uvarint,
        read_prefix_uvarint
    );
    test_random_io_write_read!(
        random_read_i64,
        VarintRead,
        bounds_i64,
        write_prefix_varint,
        read_prefix_varint
    );
    test_random_io_write_read!(
        random_bufread_u64,
        VarintBufRead,
        bounds_u64,
        write_prefix_uvarint,
        read_prefix_uvarint
    );
    test_random_io_write_read!(
        random_bufread_i64,
        VarintBufRead,
        bounds_i64,
        write_prefix_varint,
        read_prefix_varint
    );
}
