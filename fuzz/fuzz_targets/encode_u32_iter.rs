#![no_main]

use libfuzzer_sys::fuzz_target;
use prefix_uvarint::{PrefixVarIntBuf, PrefixVarIntBufMut};

fuzz_target!(|data: &[u8]| {
    let mut dst = vec![];
    let mut decoded = vec![];
    for chunk in data.chunks_exact(4) {
        let mut buf = [0; 4];
        buf.copy_from_slice(chunk);
        let n = u32::from_le_bytes(buf);
        decoded.push(n);
        dst.put_prefix_varint(n);
    }

    let mut src = &dst[..];
    let iter = src.iter_prefix_varint::<u32>();
    for (decoded, truth) in iter.zip(decoded.iter()) {
        assert_eq!(decoded.unwrap(), *truth);
    }
    
    // check that the iterator is exhausted
    assert!(src.iter_prefix_varint::<u32>().next().is_none());
});
