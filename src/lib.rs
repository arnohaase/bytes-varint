#![warn(missing_docs, rust_2018_idioms)]
#![no_std]

//! Extends the `bytes` crate with support for variable-length serialization and deserialization
//!  of integer values.
//!
//! This crate is not affiliated with the `bytes` crate, but it integrates seamlessly by providing
//!  blanket implementations for `bytes::Buf` / `bytes::BufMut`.
//!
//! Variable-length decoding can fail, and callers have no way of performing checks up-front to
//!  ensure success. This is different from fixed-length decoding that is guaranteed to succeed if
//!  e.g. the buffer has at least four available bytes when decoding an i32.
//!
//! There are two failure modes:
//!
//! * numeric overflow - the encoding has no inherent upper bound on the number of bits in a number,
//!     so a decoded number may be too large to fit into a given numeric primitive type
//! * buffer underflow - there is no way to know in advance how many bytes will be read when decoding
//!     a number. So callers can not check in advance, and decoding can fail.
//!
//! Variable-length encoding (see https://en.wikipedia.org/wiki/Variable-length_quantity for details
//!  and trade-offs) stores a number in a sequence of bytes, using each byte's seven least
//!  significant bits storing actual data, and the most significant bit specifying if there are
//!  more bytes to come. This allows small numbers to be stored in a single byte regardless of
//!  the raw value's number of bits.
//!
//! Signed integers are 'zig-zag' encoded (https://developers.google.com/protocol-buffers/docs/encoding#types),
//!  mapping the range of `-64` to `63` to a single byte.


use core::cmp::Ordering;

/// Variable-length decoding can fail, and callers have no way of performing checks up-front to
///  ensure success. This is different from fixed-length decoding that is guaranteed to succeed if
///  e.g. the buffer has at least four available bytes when decoding an i32.
#[derive(Debug, Eq, PartialEq)]
pub enum VarIntError {
    /// Returned if the encoded number has more bits than the primitive integer type into which
    ///  it is decoded.
    ///
    /// Implementations do *not* attempt to consume remaining bytes beyond the target type's
    ///  capacity, and a numeric overflow leaves the buffer's pointer in an undefined position.
    NumericOverflow,
    /// Returned if the encoded number specifies that there are more bytes to come, but the buffer
    ///  has no more available bytes
    BufferUnderflow,
}

/// Convenience alias for decoding functions
pub type VarIntResult<T> = Result<T, VarIntError>;


/// Functions for reading variable-length encoded integers into various integer types.
///
/// This trait is not meant to be implemented by application code, but is the basis for a
///  blanket implementation for `bytes::Buf`.
pub trait VarIntSupport: bytes::Buf {
    /// Read a variable-length encoded integer value into a u16.
    fn get_u16_varint(&mut self) -> VarIntResult<u16> {
        let mut result = 0;
        let mut shift = 0;

        loop {
            if !self.has_remaining() {
                return Err(VarIntError::BufferUnderflow);
            }
            let next = self.get_u8() as u16;

            // shift grows in increments of 7, and 2*7 is the largest shift possible without
            //  potentially losing significant bits
            let has_overflow = match shift.cmp(&(2*7)) {
                Ordering::Less => false,
                Ordering::Equal => next & !0x03 != 0,
                Ordering::Greater => true,
            };
            if has_overflow {
                return Err(VarIntError::NumericOverflow);
            }

            result += (next & 0x7F) << shift;
            if next & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        Ok(result)
    }

    /// Read a variable-length encoded integer value into a u32.
    fn get_u32_varint(&mut self) -> VarIntResult<u32> {
        let mut result = 0;
        let mut shift = 0;

        loop {
            if !self.has_remaining() {
                return Err(VarIntError::BufferUnderflow);
            }
            let next = self.get_u8() as u32;

            // shift grows in increments of 7, and 4*7 is the largest shift possible without
            //  potentially losing significant bits
            let has_overflow = match shift.cmp(&(4*7)) {
                Ordering::Less => false,
                Ordering::Equal => next & !0x0f != 0,
                Ordering::Greater => true,
            };
            if has_overflow {
                return Err(VarIntError::NumericOverflow);
            }

            result += (next & 0x7F) << shift;
            if next & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        Ok(result)
    }

    /// Read a variable-length encoded integer value into a u64.
    fn get_u64_varint(&mut self) -> VarIntResult<u64> {
        let mut result = 0;
        let mut shift = 0;

        loop {
            if !self.has_remaining() {
                return Err(VarIntError::BufferUnderflow);
            }
            let next = self.get_u8() as u64;

            // shift grows in increments of 7, and 9*7 is the largest shift possible without
            //  potentially losing significant bits
            let has_overflow = match shift.cmp(&(9*7)) {
                Ordering::Less => false,
                Ordering::Equal => next & !0x01 != 0,
                Ordering::Greater => true,
            };
            if has_overflow {
                return Err(VarIntError::NumericOverflow);
            }

            result += (next & 0x7F) << shift;
            if next & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        Ok(result)
    }

    /// Read a variable-length encoded integer value into a u128.
    fn get_u128_varint(&mut self) -> VarIntResult<u128> {
        let mut result = 0;
        let mut shift = 0;

        loop {
            if !self.has_remaining() {
                return Err(VarIntError::BufferUnderflow);
            }
            let next = self.get_u8() as u128;

            // shift grows in increments of 7, and 18*7 is the largest shift possible without
            //  potentially losing significant bits
            let has_overflow = match shift.cmp(&(18*7)) {
                Ordering::Less => false,
                Ordering::Equal => next & !0x03 != 0,
                Ordering::Greater => true,
            };
            if has_overflow {
                return Err(VarIntError::NumericOverflow);
            }

            result += (next & 0x7F) << shift;
            if next & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        Ok(result)
    }

    /// Read a variable-length encoded integer value into an i16, using zig-zag encoding.
    fn get_i16_varint(&mut self) -> VarIntResult<i16> {
        let raw = self.get_u16_varint()?;
        if (raw & 1) == 0 {
            Ok((raw >> 1) as i16)
        }
        else if raw == u16::MAX {
            Ok(i16::MIN)
        }
        else {
            Ok(-(((raw + 1) >> 1) as i16))
        }
    }

    /// Read a variable-length encoded integer value into an i32, using zig-zag encoding.
    fn get_i32_varint(&mut self) -> VarIntResult<i32> {
        let raw = self.get_u32_varint()?;
        if (raw & 1) == 0 {
            Ok((raw >> 1) as i32)
        }
        else if raw == u32::MAX {
            Ok(i32::MIN)
        }
        else {
            Ok(-(((raw + 1) >> 1) as i32))
        }
    }

    /// Read a variable-length encoded integer value into an i64, using zig-zag encoding.
    fn get_i64_varint(&mut self) -> VarIntResult<i64> {
        let raw = self.get_u64_varint()?;
        if (raw & 1) == 0 {
            Ok((raw >> 1) as i64)
        }
        else if raw == u64::MAX {
            Ok(i64::MIN)
        }
        else {
            Ok(-(((raw + 1) >> 1) as i64))
        }
    }

    /// Read a variable-length encoded integer value into an i128, using zig-zag encoding.
    fn get_i128_varint(&mut self) -> VarIntResult<i128> {
        let raw = self.get_u128_varint()?;
        if (raw & 1) == 0 {
            Ok((raw >> 1) as i128)
        }
        else if raw == u128::MAX {
            Ok(i128::MIN)
        }
        else {
            Ok(-(((raw + 1) >> 1) as i128))
        }
    }
}


/// Functions for writing variable-length encoded integers.
///
/// This trait is not meant to be implemented by application code, but is the basis for a
///  blanket implementation for `bytes::BufMut`.
pub trait VarIntSupportMut: bytes::BufMut {
    /// Write a u16 to a buffer using variable-length encoding.
    fn put_u16_varint(&mut self, mut value: u16) {
        while value >= 0x80 {
            self.put_u8(((value & 0x7F) | 0x80) as u8);
            value >>= 7;
        }
        self.put_u8(value as u8)
    }

    /// Write a u32 to a buffer using variable-length encoding.
    fn put_u32_varint(&mut self, mut value: u32) {
        while value >= 0x80 {
            self.put_u8(((value & 0x7F) | 0x80) as u8);
            value >>= 7;
        }
        self.put_u8(value as u8)
    }

    /// Write a u64 to a buffer using variable-length encoding.
    fn put_u64_varint(&mut self, mut value: u64) {
        while value >= 0x80 {
            self.put_u8(((value & 0x7F) | 0x80) as u8);
            value >>= 7;
        }
        self.put_u8(value as u8)
    }

    /// Write a u128 to a buffer using variable-length encoding.
    fn put_u128_varint(&mut self, mut value: u128) {
        while value >= 0x80 {
            self.put_u8(((value & 0x7F) | 0x80) as u8);
            value >>= 7;
        }
        self.put_u8(value as u8)
    }

    /// Write an i16 to a buffer using variable-length zig-zag encoding.
    fn put_i16_varint(&mut self, value: i16) {
        if value >= 0 {
            self.put_u16_varint((value as u16) << 1)
        }
        else if value == i16::MIN {
            self.put_u16_varint(u16::MAX)
        }
        else {
            self.put_u16_varint(((-value as u16) << 1) - 1)
        }
    }

    /// Write an i32 to a buffer using variable-length zig-zag encoding.
    fn put_i32_varint(&mut self, value: i32) {
        if value >= 0 {
            self.put_u32_varint((value as u32) << 1)
        }
        else if value == i32::MIN {
            self.put_u32_varint(u32::MAX)
        }
        else {
            self.put_u32_varint(((-value as u32) << 1) - 1)
        }
    }

    /// Write an i64 to a buffer using variable-length zig-zag encoding.
    fn put_i64_varint(&mut self, value: i64) {
        if value >= 0 {
            self.put_u64_varint((value as u64) << 1)
        }
        else if value == i64::MIN {
            self.put_u64_varint(u64::MAX)
        }
        else {
            self.put_u64_varint(((-value as u64) << 1) - 1)
        }
    }

    /// Write an i128 to a buffer using variable-length zig-zag encoding.
    fn put_i128_varint(&mut self, value: i128) {
        if value >= 0 {
            self.put_u128_varint((value as u128) << 1)
        }
        else if value == i128::MIN {
            self.put_u128_varint(u128::MAX)
        }
        else {
            self.put_u128_varint(((-value as u128) << 1) - 1)
        }
    }
}


// blanket implementations for seamless integration with bytes::Buf / bytes::BufMut

impl <T: bytes::Buf> VarIntSupport for T {}
impl <T: bytes::BufMut> VarIntSupportMut for T {}

#[cfg(test)]
mod test {
    extern crate alloc;

    use alloc::vec;
    use alloc::vec::Vec;
    use bytes::Buf;
    use rstest::*;

    use super::*;

    #[rstest]
    #[case::n_0(vec![0], Ok(0))]
    #[case::n_1(vec![1], Ok(1))]
    #[case::n_129(vec![0x81, 1], Ok(129))]
    #[case::max         (vec![0xff, 0xff, 0x03], Ok(u16::MAX))]
    #[case::num_overflow(vec![0xff, 0xff, 0x04], Err(VarIntError::NumericOverflow))]
    #[case::buf_empty(vec![], Err(VarIntError::BufferUnderflow))]
    #[case::buf_underflow(vec![0x80], Err(VarIntError::BufferUnderflow))]
    fn test_u16(#[case] bytes: Vec<u8>, #[case] expected: VarIntResult<u16>) {
        let mut bytes = bytes;
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(expected, buf.get_u16_varint());
        assert!(!buf.has_remaining());

        if let Ok(n) = expected {
            let mut write_buf = Vec::new();
            write_buf.put_u16_varint(n);
            assert_eq!(bytes, write_buf);
        }
    }

    #[rstest]
    #[case::n_0(vec![0], Ok(0))]
    #[case::n_1(vec![1], Ok(1))]
    #[case::n_129(vec![0x81, 1], Ok(129))]
    #[case::max         (vec![0xff, 0xff, 0xff, 0xff, 0x0f], Ok(u32::MAX))]
    #[case::num_overflow(vec![0xff, 0xff, 0xff, 0xff, 0x10], Err(VarIntError::NumericOverflow))]
    #[case::buf_empty(vec![], Err(VarIntError::BufferUnderflow))]
    #[case::buf_underflow(vec![0x80], Err(VarIntError::BufferUnderflow))]
    fn test_u32(#[case] bytes: Vec<u8>, #[case] expected: VarIntResult<u32>) {
        let mut bytes = bytes;
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(expected, buf.get_u32_varint());
        assert!(!buf.has_remaining());

        if let Ok(n) = expected {
            let mut write_buf = Vec::new();
            write_buf.put_u32_varint(n);
            assert_eq!(bytes, write_buf);
        }
    }

    #[rstest]
    #[case::n_0(vec![0], Ok(0))]
    #[case::n_1(vec![1], Ok(1))]
    #[case::n_129(vec![0x81, 1], Ok(129))]
    #[case::max         (vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01], Ok(u64::MAX))]
    #[case::num_overflow(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02], Err(VarIntError::NumericOverflow))]
    #[case::buf_empty(vec![], Err(VarIntError::BufferUnderflow))]
    #[case::buf_underflow(vec![0x80], Err(VarIntError::BufferUnderflow))]
    fn test_u64(#[case] bytes: Vec<u8>, #[case] expected: VarIntResult<u64>) {
        let mut bytes = bytes;
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(expected, buf.get_u64_varint());
        assert!(!buf.has_remaining());

        if let Ok(n) = expected {
            let mut write_buf = Vec::new();
            write_buf.put_u64_varint(n);
            assert_eq!(bytes, write_buf);
        }
    }

    #[rstest]
    #[case::n_0(vec![0], Ok(0))]
    #[case::n_1(vec![1], Ok(1))]
    #[case::n_129(vec![0x81, 1], Ok(129))]
    #[case::max         (vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x03], Ok(u128::MAX))]
    #[case::num_overflow(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x04], Err(VarIntError::NumericOverflow))]
    #[case::buf_empty(vec![], Err(VarIntError::BufferUnderflow))]
    #[case::buf_underflow(vec![0x80], Err(VarIntError::BufferUnderflow))]
    fn test_u128(#[case] bytes: Vec<u8>, #[case] expected: VarIntResult<u128>) {
        let mut bytes = bytes;
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(expected, buf.get_u128_varint());
        assert!(!buf.has_remaining());

        if let Ok(n) = expected {
            let mut write_buf = Vec::new();
            write_buf.put_u128_varint(n);
            assert_eq!(bytes, write_buf);
        }
    }

    #[rstest]
    #[case::n_0(vec![0], Ok(0))]
    #[case::n_1(vec![2], Ok(1))]
    #[case::n_128(vec![0x80, 0x2], Ok(128))]
    #[case::minus_1(vec![0x1], Ok(-1))]
    #[case::minus_129(vec![0x1], Ok(-1))]
    #[case::max               (vec![0xfe, 0xff, 0x03], Ok(i16::MAX))]
    #[case::minus_max         (vec![0xfd, 0xff, 0x03], Ok(-i16::MAX))]
    #[case::min               (vec![0xff, 0xff, 0x03], Ok(i16::MIN))]
    #[case::num_overflow_plus (vec![0xfe, 0xff, 0x04], Err(VarIntError::NumericOverflow))]
    #[case::num_overflow_minus(vec![0xff, 0xff, 0x04], Err(VarIntError::NumericOverflow))]
    #[case::buf_empty(vec![], Err(VarIntError::BufferUnderflow))]
    #[case::buf_underflow(vec![0x80], Err(VarIntError::BufferUnderflow))]
    fn test_i16(#[case] bytes: Vec<u8>, #[case] expected: VarIntResult<i16>) {
        let mut bytes = bytes;
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(expected, buf.get_i16_varint());
        assert!(!buf.has_remaining());

        if let Ok(n) = expected {
            let mut write_buf = Vec::new();
            write_buf.put_i16_varint(n);
            assert_eq!(bytes, write_buf);
        }
    }

    #[rstest]
    #[case::n_0(vec![0], Ok(0))]
    #[case::n_1(vec![2], Ok(1))]
    #[case::n_128(vec![0x80, 0x2], Ok(128))]
    #[case::minus_1(vec![0x1], Ok(-1))]
    #[case::minus_129(vec![0x1], Ok(-1))]
    #[case::max               (vec![0xfe, 0xff, 0xff, 0xff, 0x0f], Ok(i32::MAX))]
    #[case::minus_max         (vec![0xfd, 0xff, 0xff, 0xff, 0x0f], Ok(-i32::MAX))]
    #[case::min               (vec![0xff, 0xff, 0xff, 0xff, 0x0f], Ok(i32::MIN))]
    #[case::num_overflow_plus (vec![0xfe, 0xff, 0xff, 0xff, 0x10], Err(VarIntError::NumericOverflow))]
    #[case::num_overflow_minus(vec![0xff, 0xff, 0xff, 0xff, 0x10], Err(VarIntError::NumericOverflow))]
    #[case::buf_empty(vec![], Err(VarIntError::BufferUnderflow))]
    #[case::buf_underflow(vec![0x80], Err(VarIntError::BufferUnderflow))]
    fn test_i32(#[case] bytes: Vec<u8>, #[case] expected: VarIntResult<i32>) {
        let mut bytes = bytes;
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(expected, buf.get_i32_varint());
        assert!(!buf.has_remaining());

        if let Ok(n) = expected {
            let mut write_buf = Vec::new();
            write_buf.put_i32_varint(n);
            assert_eq!(bytes, write_buf);
        }
    }

    #[rstest]
    #[case::n_0(vec![0], Ok(0))]
    #[case::n_1(vec![2], Ok(1))]
    #[case::n_128(vec![0x80, 0x2], Ok(128))]
    #[case::minus_1(vec![0x1], Ok(-1))]
    #[case::minus_129(vec![0x1], Ok(-1))]
    #[case::max               (vec![0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01], Ok(i64::MAX))]
    #[case::minus_max         (vec![0xfd, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01], Ok(-i64::MAX))]
    #[case::min               (vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01], Ok(i64::MIN))]
    #[case::num_overflow_plus (vec![0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02], Err(VarIntError::NumericOverflow))]
    #[case::num_overflow_minus(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02], Err(VarIntError::NumericOverflow))]
    #[case::buf_empty(vec![], Err(VarIntError::BufferUnderflow))]
    #[case::buf_underflow(vec![0x80], Err(VarIntError::BufferUnderflow))]
    fn test_i64(#[case] bytes: Vec<u8>, #[case] expected: VarIntResult<i64>) {
        let mut bytes = bytes;
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(expected, buf.get_i64_varint());
        assert!(!buf.has_remaining());

        if let Ok(n) = expected {
            let mut write_buf = Vec::new();
            write_buf.put_i64_varint(n);
            assert_eq!(bytes, write_buf);
        }
    }

    #[rstest]
    #[case::n_0(vec![0], Ok(0))]
    #[case::n_1(vec![2], Ok(1))]
    #[case::n_128(vec![0x80, 0x2], Ok(128))]
    #[case::minus_1(vec![0x1], Ok(-1))]
    #[case::minus_129(vec![0x1], Ok(-1))]
    #[case::max               (vec![0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x03], Ok(i128::MAX))]
    #[case::minus_max         (vec![0xfd, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x03], Ok(-i128::MAX))]
    #[case::min               (vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x03], Ok(i128::MIN))]
    #[case::num_overflow_plus (vec![0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x04], Err(VarIntError::NumericOverflow))]
    #[case::num_overflow_minus(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x04], Err(VarIntError::NumericOverflow))]
    #[case::buf_empty(vec![], Err(VarIntError::BufferUnderflow))]
    #[case::buf_underflow(vec![0x80], Err(VarIntError::BufferUnderflow))]
    fn test_i128(#[case] bytes: Vec<u8>, #[case] expected: VarIntResult<i128>) {
        let mut bytes = bytes;
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(expected, buf.get_i128_varint());
        assert!(!buf.has_remaining());

        if let Ok(n) = expected {
            let mut write_buf = Vec::new();
            write_buf.put_i128_varint(n);
            assert_eq!(bytes, write_buf);
        }
    }
}
