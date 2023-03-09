#![no_main]

use std::hint::black_box;

use libfuzzer_sys::fuzz_target;
use prefix_uvarint::PrefixVarIntBuf;

fuzz_target!(|data: &[u8]| {
    // attempts to decode all the data as a u32 error are ok, panics are not
    let mut src = data;
    let iter = src.iter_prefix_varint::<u32>();
    for v in iter {
        let _ = black_box(v);
    }
});
