# prefix_uvarint

[![Crates.io][crates-badge]][crates-url]

[crates-badge]: https://img.shields.io/crates/v/prefix_uvarint.svg
[crates-url]: https://crates.io/crates/prefix_uvarint

This module implements a prefix-based variable length integer coding scheme.

Unlike an [LEB128](https://en.wikipedia.org/wiki/LEB128)-style encoding scheme, this encoding
uses a unary prefix code in the first byte of the value to indicate how many subsequent bytes
need to be read followed by the big endian encoding of any remaining bytes. This improves
coding speed compared to LEB128 by reducing the number of branches evaluated to code longer
values, and allows those branches to be different to improve branch mis-prediction.

The `PrefixVarInt` trait is implemented for `u64`, `u32`, `u16`, `i64`, `i32`, and `i16`, with
values closer to zero producing small output. Signed values are written using a [Zigzag](https://en.wikipedia.org/wiki/Variable-length_quantity#Zigzag_encoding)
coding to ensure that small negative numbers produce small output.

`PrefixVarInt` includes methods to code values directly to/from byte slices, but traits are
provided to extend `bytes::{Buf,BufMut}`, and to handle these values in `std::io::{Write,Read}`.

## Performance

To get a sense of how fast this is on your host, run `cargo bench`.

Benchmarks run with two value distributions: uniform by encoded length, and zipf by encoded length.
On an M1 MacBookAir coding speeds average 1.2G elem/s for values that encode to a single byte,
dropping off to around 400M elem/s for the longest (9 byte) values. The encoded length of a value
(`PrefixVarInt::prefix_varint_len()`) averages 3G+ elem/s.
