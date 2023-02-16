#![no_main]

use libfuzzer_sys::fuzz_target;
use prefix_uvarint::{read_prefix_varint, read_prefix_varint_buf};

fuzz_target!(|data: &[u8]| {
    // attempts to decode all the data as a u32 error are ok, panics are not
    let mut src = data;
    while !src.is_empty() {
        if let Err(_) = read_prefix_varint::<u32>(&mut src) {
            break;
        }
    }

    // do buffered reader
    let mut src = data;
    let mut src = std::io::BufReader::new(&mut src);
    while let Ok(_) = read_prefix_varint_buf::<u32>(&mut src) {}
});
