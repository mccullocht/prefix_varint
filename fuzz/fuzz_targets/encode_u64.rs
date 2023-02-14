#![no_main]

use libfuzzer_sys::fuzz_target;
use prefix_uvarint::{PrefixVarIntBuf, PrefixVarIntBufMut};

fuzz_target!(|data: &[u8]| {
    let mut dst = vec![];
    for chunk in data.chunks_exact(8) {
        let mut buf = [0; 8];
        buf.copy_from_slice(chunk);
        let n = u64::from_le_bytes(buf);
        dst.put_prefix_varint(n);
    }

    let mut src = &dst[..];
    for chunk in data.chunks_exact(8) {
        let mut buf = [0; 8];
        buf.copy_from_slice(chunk);
        let n = u64::from_le_bytes(buf);
        assert_eq!(src.get_prefix_varint::<u64>().unwrap(), n);
    }
});
