#![no_main]

use libfuzzer_sys::fuzz_target;
use prefix_uvarint::{PrefixVarIntBuf, PrefixVarIntBufMut};

fuzz_target!(|data: &[u8]| {
    let mut dst = vec![];
    for chunk in data.chunks_exact(4) {
        let mut buf = [0; 4];
        buf.copy_from_slice(chunk);
        let n = u32::from_le_bytes(buf);
        dst.put_prefix_varint(n);
    }

    let mut src = &dst[..];
    for chunk in data.chunks_exact(4) {
        let mut buf = [0; 4];
        buf.copy_from_slice(chunk);
        let n = u32::from_le_bytes(buf);
        assert_eq!(src.get_prefix_varint::<u32>().unwrap(), n);
    }
});
