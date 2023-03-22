# bytes-varint

This crate extends the `bytes` crate with support for variable-length serialization and deserialization
of integer values (protobuf style).

### Seamless integration with `bytes`

This crate is not affiliated with the `bytes` crate, but it integrates seamlessly by providing
blanket implementations for `bytes::Buf` / `bytes::BufMut`.

Importing `bytes_varint::*` makes varint functions available on `Buf` / `BufMut` instances:

```rust
use bytes_varint::*;

fn put_numbers(buf: &mut impl BufMut, i: i16, j: u64) {
    buf.put_i16_varint(i);
    buf.put_u64_varint(j);
}

fn get_number(buf: &mut impl Buf) -> VarIntResult<u32> {
    buf.get_u32_varint()
}
```


### Failure Modes 

Variable-length decoding can fail, and callers have no way of performing checks up-front to
 ensure success. This is different from fixed-length decoding that is guaranteed to succeed if
 e.g. the buffer has at least four available bytes when decoding an i32.

There are two failure modes:
 * numeric overflow - the encoding has no inherent upper bound on the number of bits in a number,
     so a decoded number may be too large to fit into a given numeric primitive type
 * buffer underflow - there is no way to know in advance how many bytes will be read when decoding
     a number. So callers can not check in advance, and decoding can fail.

### Algorithm

Variable-length encoding (see https://en.wikipedia.org/wiki/Variable-length_quantity for details
 and trade-offs) stores a number in a sequence of bytes, using each byte's seven least
  significant bits storing actual data, and the most significant bit specifying if there are
  more bytes to come. This allows small numbers to be stored in a single byte regardless of
  the raw value's number of bits.

Signed integers are 'zig-zag' encoded (https://developers.google.com/protocol-buffers/docs/encoding#types),
  mapping the range of `-64` to `63` to a single byte.
