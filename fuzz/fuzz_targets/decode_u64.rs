#![no_main]

use libfuzzer_sys::fuzz_target;
use prefix_uvarint::PrefixVarIntBuf;

fuzz_target!(|data: &[u8]| {
    // attempts to decode all the data as a u64 error are ok, panics are not
    let mut src = data;
    while !src.is_empty() {
        if let Err(_) = src.get_prefix_varint::<u64>() {
            break;
        }
    }
});
