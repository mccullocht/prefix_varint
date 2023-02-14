use prefix_uvarint::PrefixVarIntBuf;

#[test]
fn does_not_read_out_of_bounds() {
    // Run with RUSTFLAGS=-Zsanitizer=address cargo +nightly test -Zbuild-std --target x86_64-unknown-linux-gnu --test fuzz
    let decode_data = [240u8, 175, 59, 43, 0];
    let mut buf = decode_data.as_slice();
    let v = buf.get_prefix_varint::<u32>().unwrap();
    assert_eq!(v, 2939890432);
}

#[test]
fn returns_error_for_small_data() {
    let decode_data = [171u8];
    let mut buf = decode_data.as_slice();
    assert!(buf.get_prefix_varint::<u32>().is_err());
}
