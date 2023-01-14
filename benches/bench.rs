use std::ops::RangeInclusive;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use prefix_uvarint::{VarintBuf, VarintBufMut};
use rand::distributions::{Uniform, WeightedIndex};
use rand::prelude::*;

// Use a zipf-ian distribution of lengths.
const WEIGHTS: [usize; 9] = [7560, 3780, 2520, 1890, 1512, 1260, 1080, 945, 840];
// Empirically we need this length to get at least one element of every size when max_bytes=9.
const ARRARY_LEN: usize = 1024;

fn range_for_byte_size(nbytes: usize) -> RangeInclusive<u64> {
    let min = if nbytes == 1 {
        0
    } else {
        1 << ((nbytes - 1) * 7)
    };
    let max = if nbytes < 9 {
        u64::MAX >> (64 - (7 * nbytes))
    } else {
        u64::MAX
    };
    min..=max
}

// Generate an array of len with values no larger than max_bytes with a zipf-ian distribution.
fn generate_array(len: usize, max_bytes: usize) -> Vec<u64> {
    let mut len_rng = StdRng::from_seed([0xabu8; 32]);
    let len_dist = WeightedIndex::new(&WEIGHTS[..max_bytes]).unwrap();
    let mut value_rng = StdRng::from_seed([0xcdu8; 32]);
    len_dist
        .sample_iter(&mut len_rng)
        .take(len)
        .map(|n| Uniform::from(range_for_byte_size(n + 1)).sample(&mut value_rng))
        .collect()
}

fn benchmark(c: &mut Criterion) {
    let mut encode_group = c.benchmark_group("put_prefix_uvarint");
    encode_group.throughput(Throughput::Elements(ARRARY_LEN as u64));
    for max_bytes in 1..=9 {
        let input_value = generate_array(ARRARY_LEN, max_bytes);
        encode_group.bench_with_input(format!("{}", max_bytes), &input_value, |b, iv| {
            let mut output = Vec::with_capacity(ARRARY_LEN * max_bytes);
            b.iter(|| {
                output.clear();
                for v in iv {
                    output.put_prefix_uvarint(*v)
                }
                assert!(output.len() > 0);
            });
        });
    }
    drop(encode_group);

    let mut decode_group = c.benchmark_group("get_prefix_uvarint");
    decode_group.throughput(Throughput::Elements(ARRARY_LEN as u64));
    for max_bytes in 1..=9 {
        let mut encoded = Vec::with_capacity(ARRARY_LEN * max_bytes);
        for v in generate_array(ARRARY_LEN, max_bytes) {
            encoded.put_prefix_uvarint(v)
        }
        decode_group.bench_with_input(format!("{}", max_bytes), &encoded, |b, e| {
            b.iter(|| {
                let mut b = e.as_slice();
                for _ in 0..ARRARY_LEN {
                    b.get_prefix_uvarint().unwrap();
                }
                assert!(b.is_empty())
            });
        });
    }
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
