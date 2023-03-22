
//TODO unit tests
//TODO explain 'overflow'
//TODO interact with 'panic on eof'
//TODO feature for bigint


pub trait VarIntSupport: bytes::Buf {
    fn decode_varint_u16(&mut self, overflow: &mut bool) -> u16 {
        let mut result = 0;
        let mut shift = 0;

        loop {
            let next = self.get_u8() as u16;
            if shift > 16-7 {
                *overflow = true;
                return 0;
            }
            result += (next & 0x7F) << shift;
            shift += 7;
            if next & 0x80 == 0 {
                break;
            }
        }

        *overflow = false;
        result
    }

    fn decode_varint_u32(&mut self, overflow: &mut bool) -> u32 {
        let mut result = 0;
        let mut shift = 0;

        loop {
            let next = self.get_u8() as u32;
            if shift > 32-7 {
                *overflow = true;
                return 0;
            }
            result += (next & 0x7F) << shift;
            shift += 7;
            if next & 0x80 == 0 {
                break;
            }
        }

        *overflow = false;
        result
    }

    fn get_u64_varint(&mut self, overflow: &mut bool) -> u64 {
        let mut result = 0;
        let mut shift = 0;

        loop {
            let next = self.get_u8() as u64;
            if shift > 64-7 {
                *overflow = true;
                return 0;
            }
            result += (next & 0x7F) << shift;
            shift += 7;
            if next & 0x80 == 0 {
                break;
            }
        }

        *overflow = false;
        result
    }

    fn get_u128_varint(&mut self, overflow: &mut bool) -> u128 {
        let mut result = 0;
        let mut shift = 0;

        loop {
            let next = self.get_u8() as u128;
            result += (next & 0x7F) << shift;
            if shift > 128-7 {
                *overflow = true;
                return 0;
            }
            shift += 7;
            if next & 0x80 == 0 {
                break;
            }
        }
        result
    }

    fn get_i128_varint(&mut self) -> i128 {
        let raw = self.get_u128_varint();
        if (raw & 1) == 0 {
            (raw >> 1) as i128
        }
        else if raw == u128::MAX {
            i128::MIN
        }
        else {
            -(((raw + 1) >> 1) as i128)
        }
    }

    fn get_i64_varint(&mut self) -> i64 {
        let raw = self.get_u64_varint();
        if (raw & 1) == 0 {
            (raw >> 1) as i64
        }
        else if raw == u64::MAX {
            i64::MIN
        }
        else {
            -(((raw + 1) >> 1) as i64)
        }
    }

    fn get_i32_varint(&mut self) -> i32 {
        let raw = self.get_u32_varint();
        if (raw&1) == 0 {
            (raw >> 1) as i32
        }
        else if raw == u32::MAX {
            i32::MIN
        }
        else {
            -(((raw + 1) >> 1) as i32)
        }
    }

    fn get_i16_varint(&mut self) -> i16 {
        let raw = self.get_u16_varint();
        if (raw&1) == 0 {
            (raw >> 1) as i16
        }
        else if raw == u16::MAX {
            i16::MIN
        }
        else {
            -(((raw + 1) >> 1) as i16)
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
