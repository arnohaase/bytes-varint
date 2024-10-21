//! Extends the `bytes` crate with functions to read fixed-length numbers wrapped in buffer
//!  underflow checks. This is often useful when working with variable-length encoded buffers.
//!
//! This is in a separate module to make it easy to ignore when it is not needed.

macro_rules! get_try_impl {
    ($try_getter: ident, $ty:ty, $getter: ident) => {
        /// Get a fixed-length encoded number, checking for buffer underflow.
        fn $try_getter(&mut self) -> $crate::VarIntResult<$ty> {
            if self.remaining() < size_of::<$ty>() {
                return Err($crate::VarIntError::BufferUnderflow);
            }
            Ok(self.$getter())
        }
    }
}


/// When working with variable-length encodings for numbers, the buffers themselves become
///  variable length, and it is impossible to check that they are long enough before decoding
///  them. Fixed-length buffer layouts have obvious benefits, but if some protocol uses var-length
///  encoding, buffer underflow can occur even when reading fixed-length numbers.
///
/// This trait provides functionality for decoding numbers using fixed-length encodings, but
///  checking for buffer underflow.
pub trait TryGetFixedSupport: bytes::Buf {
    get_try_impl!(try_get_u8, u8, get_u8);

    get_try_impl!(try_get_u16, u16, get_u16);
    get_try_impl!(try_get_u32, u32, get_u32);
    get_try_impl!(try_get_u64, u64, get_u64);
    get_try_impl!(try_get_u128, u128, get_u128);

    get_try_impl!(try_get_u16_le, u16, get_u16_le);
    get_try_impl!(try_get_u32_le, u32, get_u32_le);
    get_try_impl!(try_get_u64_le, u64, get_u64_le);
    get_try_impl!(try_get_u128_le, u128, get_u128_le);

    get_try_impl!(try_get_i8, i8, get_i8);

    get_try_impl!(try_get_i16, i16, get_i16);
    get_try_impl!(try_get_i32, i32, get_i32);
    get_try_impl!(try_get_i64, i64, get_i64);
    get_try_impl!(try_get_i128, i128, get_i128);

    get_try_impl!(try_get_i16_le, i16, get_i16_le);
    get_try_impl!(try_get_i32_le, i32, get_i32_le);
    get_try_impl!(try_get_i64_le, i64, get_i64_le);
    get_try_impl!(try_get_i128_le, i128, get_i128_le);
}

impl<T: bytes::Buf> TryGetFixedSupport for T {}

#[cfg(test)]
mod test {
    extern crate alloc;

    use alloc::vec;
    use alloc::vec::Vec;

    use rstest::rstest;

    use crate::try_get_fixed::TryGetFixedSupport;
    use crate::{VarIntResult, VarIntError};

    #[rstest]
    #[case(vec![1u8], Ok(1))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u8(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u8>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u8(), expected);
    }

    #[rstest]
    #[case(vec![1u8, 2u8], Ok(0x0102))]
    #[case(vec![1u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u16(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u16>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u16(), expected);
    }
    #[rstest]
    #[case(vec![1u8, 2u8], Ok(0x0201))]
    #[case(vec![1u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u16_le(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u16>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u16_le(), expected);
    }

    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8], Ok(0x01020304))]
    #[case(vec![1u8, 2u8, 3u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u32(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u32>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u32(), expected);
    }
    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8], Ok(0x04030201))]
    #[case(vec![1u8, 2u8, 3u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u32_le(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u32>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u32_le(), expected);
    }

    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8], Ok(0x0102030405060708))]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u64(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u64>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u64(), expected);
    }
    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8], Ok(0x0807060504030201))]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u64_le(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u64>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u64_le(), expected);
    }

    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8, 0u8], Ok(0x0102030405060708090a0b0c0d0e0f00))]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u128(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u128>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u128(), expected);
    }
    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8, 0u8], Ok(0x000f0e0d0c0b0a090807060504030201))]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_u128_le(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<u128>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_u128_le(), expected);
    }

    #[rstest]
    #[case(vec![1u8], Ok(1))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i8(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i8>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i8(), expected);
    }

    #[rstest]
    #[case(vec![1u8, 2u8], Ok(0x0102))]
    #[case(vec![1u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i16(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i16>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i16(), expected);
    }
    #[rstest]
    #[case(vec![1u8, 2u8], Ok(0x0201))]
    #[case(vec![1u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i16_le(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i16>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i16_le(), expected);
    }

    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8], Ok(0x01020304))]
    #[case(vec![1u8, 2u8, 3u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i32(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i32>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i32(), expected);
    }
    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8], Ok(0x04030201))]
    #[case(vec![1u8, 2u8, 3u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i32_le(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i32>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i32_le(), expected);
    }

    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8], Ok(0x0102030405060708))]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i64(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i64>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i64(), expected);
    }
    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8], Ok(0x0807060504030201))]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i64_le(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i64>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i64_le(), expected);
    }

    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8, 0u8], Ok(0x0102030405060708090a0b0c0d0e0f00))]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i128(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i128>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i128(), expected);
    }
    #[rstest]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8, 0u8], Ok(0x000f0e0d0c0b0a090807060504030201))]
    #[case(vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8], Err(VarIntError::BufferUnderflow))]
    #[case(vec![], Err(VarIntError::BufferUnderflow))]
    fn test_i128_le(#[case] mut bytes: Vec<u8>, #[case] expected: VarIntResult<i128>) {
        let mut buf: &[u8] = &mut bytes;
        assert_eq!(buf.try_get_i128_le(), expected);
    }
}
