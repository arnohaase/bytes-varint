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

### Buffer underflow checks when reading fixed-length numbers

The `bytes` crate focuses on fixed-length buffers where decoders can check the length of available data before
decoding parts. That makes for a simple decoding API that panics if a buffer underflows - it is after all the caller's
responsibility to check buffer size before decoding.

When a buffer contains var-length data, this becomes murkier: It is impossible to check a buffer's length up-front in
general, and even something as simple as `get_u8()` requires a check for availability of data.

To simplify working with fixed-length numbers in a variable-length buffer, there is now a trait `TryGetFixedSupport`
that wraps decoding fixed-length numbers with buffer underflow checks.

```rust
use bytes_varint::*;
use bytes_varint::TryGetFixedSupport;

fn get_number(buf: &mut impl Buf) -> VarIntResult<u32> {
    buf.try_get_u32()
}
```

Note that this trait is in a separate module, so it is simple to ignore if you don't need or want it.

## Release Notes

### 1.1.0
* `VarIntError` implements the `Error` trait now that it has become stable in `no_std`
* Rename `get_u32_varint()` to `try_get_u32_varint()` etc. to be more in line with Rust naming conventions.
    The old functions are deprecated and will remain for the foreseeable future.
* Add `put_usize_varint()`, `put_isize_varint()`, `try_get_usize_varint()` and `try_get_isize_varint()`
* `TryGetFixedSupport` trait for getting fixed-length encoded numbers with buffer underflow checks.




