#![warn(missing_docs, rust_2018_idioms)]
#![no_std]

//TODO RustDoc
// format
// why 'VarIntResult'
//
//TODO format

use core::cmp::Ordering;

#[derive(Debug, Eq, PartialEq)]
pub enum VarIntError {
    NumericOverflow,
    BufferUnderflow,
}

pub type VarIntResult<T> = Result<T, VarIntError>;

pub trait VarIntSupport: bytes::Buf {
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

pub trait VarIntSupportMut: bytes::BufMut {
    fn put_u16_varint(&mut self, mut value: u16) {
        while value >= 0x80 {
            self.put_u8(((value & 0x7F) | 0x80) as u8);
            value >>= 7;
        }
        self.put_u8(value as u8)
    }

    fn put_u32_varint(&mut self, mut value: u32) {
        while value >= 0x80 {
            self.put_u8(((value & 0x7F) | 0x80) as u8);
            value >>= 7;
        }
        self.put_u8(value as u8)
    }

    fn put_u64_varint(&mut self, mut value: u64) {
        while value >= 0x80 {
            self.put_u8(((value & 0x7F) | 0x80) as u8);
            value >>= 7;
        }
        self.put_u8(value as u8)
    }

    fn put_u128_varint(&mut self, mut value: u128) {
        while value >= 0x80 {
            self.put_u8(((value & 0x7F) | 0x80) as u8);
            value >>= 7;
        }
        self.put_u8(value as u8)
    }

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


//TODO documentation - blanket implementation
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
