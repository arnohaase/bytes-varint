
//TODO RustDoc
// format
// why 'VarIntResult'
//
//TODO unit tests
//TODO feature for bigint

use std::cmp::Ordering;

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
                Ordering::Equal => next & !0x07 != 0,
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
                Ordering::Equal => next & !0x02 != 0,
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
