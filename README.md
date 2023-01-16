# prefix_uvarint

[![Crates.io][crates-badge]][crates-url]

[crates-badge]: https://img.shields.io/crates/v/prefix_uvarint.svg
[crates-url]: https://crates.io/crates/prefix_uvarint

This crate implements a prefix-based variable length integer coding scheme.

Unlike an [LEB128](https://en.wikipedia.org/wiki/LEB128)-style encoding scheme, this encoding
uses a unary prefix code in the first byte of the value to indicate how many subsequent bytes
need to be read followed by the big endian encoding of any remaining bytes. This improves
coding speed compared to LEB128 by reducing the number of branches required to code longer
values.

XXX this needs to be updated.
`uvarint` methods code `u64` values, with values closer to zero producing smaller output.
`varint` methods code `i64` values using a [Zigzag](https://en.wikipedia.org/wiki/Variable-length_quantity#Zigzag_encoding)
encoding to ensure that small negative numbers produce small output.

XXX this needs to be updated. prefer PrefixVarInt, PrefixVarIntBuf, PrefixVarIntBufMut over IO
XXX for speed.
Coding methods are provided as extensions to the `bytes::{Buf,BufMut}` traits which are
implemented for common in-memory byte stream types. Lower level methods that operate directly
on pointers are also provided but come with caveats (may overread/overwrite).

## Performance

XXX this needs to be updated.
On an M1 MacbookAir compression speeds range from 250-450M elem/s depending on the lengths of the
input values, with smaller values (`0..=127 u64` or `-64..=63 i64`) being the fastest. To get a
sense of how fast this is on your host run `cargo bench`.
