#![no_main]

use libfuzzer_sys::fuzz_target;
use prefix_uvarint::{read_prefix_varint, write_prefix_varint};

fuzz_target!(|data: &[u8]| {
    let mut dst = vec![];
    for chunk in data.chunks_exact(4) {
        let u32 = u32::from_le_bytes(chunk.try_into().unwrap());
        write_prefix_varint(u32, &mut dst).unwrap();
    }

    let mut src = &dst[..];
    for chunk in data.chunks_exact(4) {
        let u32 = u32::from_le_bytes(chunk.try_into().unwrap());
        assert_eq!(read_prefix_varint::<u32>(&mut src).unwrap(), u32);
    }
});
