use std::ops::RangeInclusive;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use prefix_uvarint::PrefixVarInt;
use rand::distributions::{Uniform, WeightedIndex};
use rand::prelude::*;

// Uniform weights: equal probability of a value of each length.
const UNIFORM_WEIGHTS: [usize; 9] = [1, 1, 1, 1, 1, 1, 1, 1, 1];
// Zipf-like weights: decreasing but non-zero probability for larger values.
const ZIPF_WEIGHTS: [usize; 9] = [7560, 3780, 2520, 1890, 1512, 1260, 1080, 945, 840];
// Empirically we need this length to get at least one element of every size when max_bytes=9.
const ARRAY_LEN: usize = 1024;

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
fn generate_array(len: usize, max_bytes: usize, weights: &[usize; 9]) -> Vec<u64> {
    let mut len_rng = StdRng::from_seed([0xabu8; 32]);
    let len_dist = WeightedIndex::new(&weights[..max_bytes]).unwrap();
    let mut value_rng = StdRng::from_seed([0xcdu8; 32]);
    len_dist
        .sample_iter(&mut len_rng)
        .take(len)
        .map(|n| Uniform::from(range_for_byte_size(n + 1)).sample(&mut value_rng))
        .collect()
}

fn benchmark(c: &mut Criterion) {
    for (name, weights) in [("uniform", &UNIFORM_WEIGHTS), ("zipf", &ZIPF_WEIGHTS)] {
        let mut g = c.benchmark_group(name);
        g.throughput(Throughput::Elements(ARRAY_LEN as u64));
        for max_bytes in 1..=9 {
            let input_value = generate_array(ARRAY_LEN, max_bytes, weights);
            g.bench_with_input(
                format!("max_bytes{}/put_prefix_varint", max_bytes),
                &input_value,
                |b, iv| {
                    let mut output = Vec::with_capacity(ARRAY_LEN * max_bytes);
                    b.iter(|| {
                        output.clear();
                        for v in iv {
                            v.encode_varint(&mut output);
                        }
                        assert!(output.len() > 0);
                    });
                },
            );

            let mut encoded = Vec::with_capacity(ARRAY_LEN * max_bytes);
            for v in input_value.iter().copied() {
                v.encode_varint(&mut encoded);
            }
            g.bench_with_input(
                format!("max_bytes{}/get_prefix_uvarint", max_bytes),
                encoded.as_slice(),
                |b, e| {
                    b.iter(|| {
                        let mut b = e;
                        for _ in 0..ARRAY_LEN {
                            u64::decode_varint(&mut b).unwrap();
                        }
                        assert!(b.is_empty());
                    })
                },
            );
        }
    }
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
