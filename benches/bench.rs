use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use prefix_uvarint::{VarintBuf, VarintBufMut};
use rand::distributions::Uniform;
use rand::prelude::*;

fn generate_array(len: usize, max_bytes: usize) -> Vec<u64> {
    let seed = &[0xabu8; 32];
    let mut rng = StdRng::from_seed(*seed);
    // Each output byte contains at most 7 bytes of the input value, except for 9 (all possible values).
    let mut max_value = u64::MAX;
    if max_bytes < 9 {
        max_value >>= 64 - (7 * max_bytes);
    }
    let between = Uniform::from(1..max_value);
    (0..len).map(|_| between.sample(&mut rng)).collect()
}

fn benchmark(c: &mut Criterion) {
    for len in [8, 256] {
        let mut encode_group = c.benchmark_group(format!("put_prefix_uvarint/{}", len));
        encode_group.throughput(Throughput::Elements(len as u64));
        for max_bytes in 1..=9 {
            let input_value = generate_array(len, max_bytes);
            encode_group.bench_with_input(format!("{}", max_bytes), &input_value, |b, iv| {
                let mut output = Vec::with_capacity(len * max_bytes);
                b.iter(|| {
                    output.clear();
                    for v in iv {
                        output.put_prefix_uvarint(*v)
                    }
                    assert!(output.len() > 0);
                });
            });
        }
    }

    for len in [8, 256] {
        let mut decode_group = c.benchmark_group(format!("get_prefix_uvarint/{}", len));
        decode_group.throughput(Throughput::Elements(len as u64));
        for max_bytes in 1..=9 {
            let mut encoded = Vec::with_capacity(len * max_bytes);
            for v in generate_array(len, max_bytes) {
                encoded.put_prefix_uvarint(v)
            }
            decode_group.bench_with_input(format!("{}", max_bytes), &encoded, |b, e| {
                b.iter(|| {
                    let mut b = e.as_slice();
                    for _ in 0..len {
                        assert!(b.get_prefix_uvarint().unwrap() > 0);
                    }
                });
            });
        }
    }
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
