
// Auto-generated numeric functions for C++ interop
#![allow(non_camel_case_types, non_snake_case)]

use crate::LeanObject;
type b_lean_obj_arg = *mut LeanObject;

#[no_mangle] pub extern "C" fn lean_uint8_add(a: u8, b: u8) -> u8 { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_uint8_sub(a: u8, b: u8) -> u8 { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_uint8_mul(a: u8, b: u8) -> u8 { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_uint8_div(a: u8, b: u8) -> u8 { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_uint8_mod(a: u8, b: u8) -> u8 { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_uint8_land(a: u8, b: u8) -> u8 { a & b }
#[no_mangle] pub extern "C" fn lean_uint8_lor(a: u8, b: u8) -> u8 { a | b }
#[no_mangle] pub extern "C" fn lean_uint8_xor(a: u8, b: u8) -> u8 { a ^ b }
#[no_mangle] pub extern "C" fn lean_uint8_shift_left(a: u8, b: u8) -> u8 { a.wrapping_shl((b % 8) as u32) }
#[no_mangle] pub extern "C" fn lean_uint8_shift_right(a: u8, b: u8) -> u8 { a.wrapping_shr((b % 8) as u32) }
#[no_mangle] pub extern "C" fn lean_uint8_complement(a: u8) -> u8 { !a }
#[no_mangle] pub extern "C" fn lean_uint8_log2(a: u8) -> u8 { if a == 0 { 0 } else { (8 - 1 - a.leading_zeros()) as u8 } }
#[no_mangle] pub extern "C" fn lean_uint8_neg(a: u8) -> u8 { (a as i64).wrapping_neg() as u8 }
#[no_mangle] pub extern "C" fn lean_uint8_to_uint16(a: u8) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_uint8_to_uint32(a: u8) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_uint8_to_usize(a: u8) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_uint8_to_int8(a: u8) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_uint8_to_int16(a: u8) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_uint8_to_int32(a: u8) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_uint8_to_int64(a: u8) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_uint8_to_isize(a: u8) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_uint8_to_float32(a: u8) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_uint8_to_float(a: u8) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_uint16_add(a: u16, b: u16) -> u16 { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_uint16_sub(a: u16, b: u16) -> u16 { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_uint16_mul(a: u16, b: u16) -> u16 { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_uint16_div(a: u16, b: u16) -> u16 { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_uint16_mod(a: u16, b: u16) -> u16 { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_uint16_land(a: u16, b: u16) -> u16 { a & b }
#[no_mangle] pub extern "C" fn lean_uint16_lor(a: u16, b: u16) -> u16 { a | b }
#[no_mangle] pub extern "C" fn lean_uint16_xor(a: u16, b: u16) -> u16 { a ^ b }
#[no_mangle] pub extern "C" fn lean_uint16_shift_left(a: u16, b: u16) -> u16 { a.wrapping_shl((b % 16) as u32) }
#[no_mangle] pub extern "C" fn lean_uint16_shift_right(a: u16, b: u16) -> u16 { a.wrapping_shr((b % 16) as u32) }
#[no_mangle] pub extern "C" fn lean_uint16_complement(a: u16) -> u16 { !a }
#[no_mangle] pub extern "C" fn lean_uint16_log2(a: u16) -> u16 { if a == 0 { 0 } else { (16 - 1 - a.leading_zeros()) as u16 } }
#[no_mangle] pub extern "C" fn lean_uint16_neg(a: u16) -> u16 { (a as i64).wrapping_neg() as u16 }
#[no_mangle] pub extern "C" fn lean_uint16_to_uint8(a: u16) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_uint16_to_uint32(a: u16) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_uint16_to_usize(a: u16) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_uint16_to_int8(a: u16) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_uint16_to_int16(a: u16) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_uint16_to_int32(a: u16) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_uint16_to_int64(a: u16) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_uint16_to_isize(a: u16) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_uint16_to_float32(a: u16) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_uint16_to_float(a: u16) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_uint32_add(a: u32, b: u32) -> u32 { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_uint32_sub(a: u32, b: u32) -> u32 { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_uint32_mul(a: u32, b: u32) -> u32 { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_uint32_div(a: u32, b: u32) -> u32 { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_uint32_mod(a: u32, b: u32) -> u32 { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_uint32_land(a: u32, b: u32) -> u32 { a & b }
#[no_mangle] pub extern "C" fn lean_uint32_lor(a: u32, b: u32) -> u32 { a | b }
#[no_mangle] pub extern "C" fn lean_uint32_xor(a: u32, b: u32) -> u32 { a ^ b }
#[no_mangle] pub extern "C" fn lean_uint32_shift_left(a: u32, b: u32) -> u32 { a.wrapping_shl((b % 32) as u32) }
#[no_mangle] pub extern "C" fn lean_uint32_shift_right(a: u32, b: u32) -> u32 { a.wrapping_shr((b % 32) as u32) }
#[no_mangle] pub extern "C" fn lean_uint32_complement(a: u32) -> u32 { !a }
#[no_mangle] pub extern "C" fn lean_uint32_log2(a: u32) -> u32 { if a == 0 { 0 } else { (32 - 1 - a.leading_zeros()) as u32 } }
#[no_mangle] pub extern "C" fn lean_uint32_neg(a: u32) -> u32 { (a as i64).wrapping_neg() as u32 }
#[no_mangle] pub extern "C" fn lean_uint32_to_uint8(a: u32) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_uint32_to_uint16(a: u32) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_uint32_to_usize(a: u32) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_uint32_to_int8(a: u32) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_uint32_to_int16(a: u32) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_uint32_to_int32(a: u32) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_uint32_to_int64(a: u32) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_uint32_to_isize(a: u32) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_uint32_to_float32(a: u32) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_uint32_to_float(a: u32) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_uint64_add(a: u64, b: u64) -> u64 { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_uint64_sub(a: u64, b: u64) -> u64 { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_uint64_mul(a: u64, b: u64) -> u64 { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_uint64_div(a: u64, b: u64) -> u64 { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_uint64_mod(a: u64, b: u64) -> u64 { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_uint64_land(a: u64, b: u64) -> u64 { a & b }
#[no_mangle] pub extern "C" fn lean_uint64_complement(a: u64) -> u64 { !a }
#[no_mangle] pub extern "C" fn lean_uint64_log2(a: u64) -> u64 { if a == 0 { 0 } else { (64 - 1 - a.leading_zeros()) as u64 } }
#[no_mangle] pub extern "C" fn lean_uint64_neg(a: u64) -> u64 { (a as i64).wrapping_neg() as u64 }
#[no_mangle] pub extern "C" fn lean_uint64_to_uint8(a: u64) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_uint64_to_uint16(a: u64) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_uint64_to_uint32(a: u64) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_uint64_to_int8(a: u64) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_uint64_to_int16(a: u64) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_uint64_to_int32(a: u64) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_uint64_to_int64(a: u64) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_uint64_to_isize(a: u64) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_uint64_to_float32(a: u64) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_uint64_to_float(a: u64) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_usize_mul(a: usize, b: usize) -> usize { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_usize_div(a: usize, b: usize) -> usize { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_usize_mod(a: usize, b: usize) -> usize { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_usize_lor(a: usize, b: usize) -> usize { a | b }
#[no_mangle] pub extern "C" fn lean_usize_xor(a: usize, b: usize) -> usize { a ^ b }
#[no_mangle] pub extern "C" fn lean_usize_shift_left(a: usize, b: usize) -> usize { a.wrapping_shl((b % 64) as u32) }
#[no_mangle] pub extern "C" fn lean_usize_shift_right(a: usize, b: usize) -> usize { a.wrapping_shr((b % 64) as u32) }
#[no_mangle] pub extern "C" fn lean_usize_complement(a: usize) -> usize { !a }
#[no_mangle] pub extern "C" fn lean_usize_log2(a: usize) -> usize { if a == 0 { 0 } else { (64 - 1 - a.leading_zeros()) as usize } }
#[no_mangle] pub extern "C" fn lean_usize_neg(a: usize) -> usize { (a as i64).wrapping_neg() as usize }
#[no_mangle] pub extern "C" fn lean_usize_to_uint8(a: usize) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_usize_to_uint16(a: usize) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_usize_to_uint32(a: usize) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_usize_to_uint64(a: usize) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_usize_to_int8(a: usize) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_usize_to_int16(a: usize) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_usize_to_int32(a: usize) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_usize_to_int64(a: usize) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_usize_to_isize(a: usize) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_usize_to_float32(a: usize) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_usize_to_float(a: usize) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_int8_add(a: i8, b: i8) -> i8 { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_int8_sub(a: i8, b: i8) -> i8 { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_int8_mul(a: i8, b: i8) -> i8 { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_int8_div(a: i8, b: i8) -> i8 { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_int8_mod(a: i8, b: i8) -> i8 { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_int8_land(a: i8, b: i8) -> i8 { a & b }
#[no_mangle] pub extern "C" fn lean_int8_lor(a: i8, b: i8) -> i8 { a | b }
#[no_mangle] pub extern "C" fn lean_int8_xor(a: i8, b: i8) -> i8 { a ^ b }
#[no_mangle] pub extern "C" fn lean_int8_shift_left(a: i8, b: i8) -> i8 { a.wrapping_shl((b % 8) as u32) }
#[no_mangle] pub extern "C" fn lean_int8_shift_right(a: i8, b: i8) -> i8 { a.wrapping_shr((b % 8) as u32) }
#[no_mangle] pub extern "C" fn lean_int8_complement(a: i8) -> i8 { !a }
#[no_mangle] pub extern "C" fn lean_int8_log2(a: i8) -> i8 { if a == 0 { 0 } else { (8 - 1 - a.leading_zeros()) as i8 } }
#[no_mangle] pub extern "C" fn lean_int8_dec_eq(a: i8, b: i8) -> u8 { if a == b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int8_dec_lt(a: i8, b: i8) -> u8 { if a < b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int8_dec_le(a: i8, b: i8) -> u8 { if a <= b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int8_neg(a: i8) -> i8 { a.wrapping_neg() }
#[no_mangle] pub extern "C" fn lean_int8_abs(a: i8) -> i8 { if a < 0 { a.wrapping_neg() } else { a } }
#[no_mangle] pub extern "C" fn lean_int8_to_uint8(a: i8) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_int8_to_uint16(a: i8) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_int8_to_uint32(a: i8) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_int8_to_uint64(a: i8) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_int8_to_usize(a: i8) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_int8_to_int16(a: i8) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_int8_to_int32(a: i8) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_int8_to_int64(a: i8) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_int8_to_isize(a: i8) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_int8_to_float32(a: i8) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_int8_to_float(a: i8) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_int16_add(a: i16, b: i16) -> i16 { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_int16_sub(a: i16, b: i16) -> i16 { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_int16_mul(a: i16, b: i16) -> i16 { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_int16_div(a: i16, b: i16) -> i16 { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_int16_mod(a: i16, b: i16) -> i16 { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_int16_land(a: i16, b: i16) -> i16 { a & b }
#[no_mangle] pub extern "C" fn lean_int16_lor(a: i16, b: i16) -> i16 { a | b }
#[no_mangle] pub extern "C" fn lean_int16_xor(a: i16, b: i16) -> i16 { a ^ b }
#[no_mangle] pub extern "C" fn lean_int16_shift_left(a: i16, b: i16) -> i16 { a.wrapping_shl((b % 16) as u32) }
#[no_mangle] pub extern "C" fn lean_int16_shift_right(a: i16, b: i16) -> i16 { a.wrapping_shr((b % 16) as u32) }
#[no_mangle] pub extern "C" fn lean_int16_complement(a: i16) -> i16 { !a }
#[no_mangle] pub extern "C" fn lean_int16_log2(a: i16) -> i16 { if a == 0 { 0 } else { (16 - 1 - a.leading_zeros()) as i16 } }
#[no_mangle] pub extern "C" fn lean_int16_dec_eq(a: i16, b: i16) -> u8 { if a == b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int16_dec_lt(a: i16, b: i16) -> u8 { if a < b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int16_dec_le(a: i16, b: i16) -> u8 { if a <= b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int16_neg(a: i16) -> i16 { a.wrapping_neg() }
#[no_mangle] pub extern "C" fn lean_int16_abs(a: i16) -> i16 { if a < 0 { a.wrapping_neg() } else { a } }
#[no_mangle] pub extern "C" fn lean_int16_to_uint8(a: i16) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_int16_to_uint16(a: i16) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_int16_to_uint32(a: i16) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_int16_to_uint64(a: i16) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_int16_to_usize(a: i16) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_int16_to_int8(a: i16) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_int16_to_int32(a: i16) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_int16_to_int64(a: i16) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_int16_to_isize(a: i16) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_int16_to_float32(a: i16) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_int16_to_float(a: i16) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_int32_add(a: i32, b: i32) -> i32 { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_int32_sub(a: i32, b: i32) -> i32 { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_int32_mul(a: i32, b: i32) -> i32 { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_int32_div(a: i32, b: i32) -> i32 { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_int32_mod(a: i32, b: i32) -> i32 { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_int32_land(a: i32, b: i32) -> i32 { a & b }
#[no_mangle] pub extern "C" fn lean_int32_lor(a: i32, b: i32) -> i32 { a | b }
#[no_mangle] pub extern "C" fn lean_int32_xor(a: i32, b: i32) -> i32 { a ^ b }
#[no_mangle] pub extern "C" fn lean_int32_shift_left(a: i32, b: i32) -> i32 { a.wrapping_shl((b % 32) as u32) }
#[no_mangle] pub extern "C" fn lean_int32_shift_right(a: i32, b: i32) -> i32 { a.wrapping_shr((b % 32) as u32) }
#[no_mangle] pub extern "C" fn lean_int32_complement(a: i32) -> i32 { !a }
#[no_mangle] pub extern "C" fn lean_int32_log2(a: i32) -> i32 { if a == 0 { 0 } else { (32 - 1 - a.leading_zeros()) as i32 } }
#[no_mangle] pub extern "C" fn lean_int32_dec_eq(a: i32, b: i32) -> u8 { if a == b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int32_dec_lt(a: i32, b: i32) -> u8 { if a < b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int32_dec_le(a: i32, b: i32) -> u8 { if a <= b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int32_neg(a: i32) -> i32 { a.wrapping_neg() }
#[no_mangle] pub extern "C" fn lean_int32_abs(a: i32) -> i32 { if a < 0 { a.wrapping_neg() } else { a } }
#[no_mangle] pub extern "C" fn lean_int32_to_uint8(a: i32) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_int32_to_uint16(a: i32) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_int32_to_uint32(a: i32) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_int32_to_uint64(a: i32) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_int32_to_usize(a: i32) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_int32_to_int8(a: i32) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_int32_to_int16(a: i32) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_int32_to_int64(a: i32) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_int32_to_isize(a: i32) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_int32_to_float32(a: i32) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_int32_to_float(a: i32) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_int64_add(a: i64, b: i64) -> i64 { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_int64_sub(a: i64, b: i64) -> i64 { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_int64_mul(a: i64, b: i64) -> i64 { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_int64_div(a: i64, b: i64) -> i64 { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_int64_mod(a: i64, b: i64) -> i64 { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_int64_land(a: i64, b: i64) -> i64 { a & b }
#[no_mangle] pub extern "C" fn lean_int64_lor(a: i64, b: i64) -> i64 { a | b }
#[no_mangle] pub extern "C" fn lean_int64_xor(a: i64, b: i64) -> i64 { a ^ b }
#[no_mangle] pub extern "C" fn lean_int64_shift_left(a: i64, b: i64) -> i64 { a.wrapping_shl((b % 64) as u32) }
#[no_mangle] pub extern "C" fn lean_int64_shift_right(a: i64, b: i64) -> i64 { a.wrapping_shr((b % 64) as u32) }
#[no_mangle] pub extern "C" fn lean_int64_complement(a: i64) -> i64 { !a }
#[no_mangle] pub extern "C" fn lean_int64_log2(a: i64) -> i64 { if a == 0 { 0 } else { (64 - 1 - a.leading_zeros()) as i64 } }
#[no_mangle] pub extern "C" fn lean_int64_dec_eq(a: i64, b: i64) -> u8 { if a == b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int64_dec_lt(a: i64, b: i64) -> u8 { if a < b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int64_dec_le(a: i64, b: i64) -> u8 { if a <= b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_int64_neg(a: i64) -> i64 { a.wrapping_neg() }
#[no_mangle] pub extern "C" fn lean_int64_abs(a: i64) -> i64 { if a < 0 { a.wrapping_neg() } else { a } }
#[no_mangle] pub extern "C" fn lean_int64_to_uint8(a: i64) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_int64_to_uint16(a: i64) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_int64_to_uint32(a: i64) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_int64_to_uint64(a: i64) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_int64_to_usize(a: i64) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_int64_to_int8(a: i64) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_int64_to_int16(a: i64) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_int64_to_int32(a: i64) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_int64_to_isize(a: i64) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_int64_to_float32(a: i64) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_int64_to_float(a: i64) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_isize_add(a: isize, b: isize) -> isize { a.wrapping_add(b) }
#[no_mangle] pub extern "C" fn lean_isize_sub(a: isize, b: isize) -> isize { a.wrapping_sub(b) }
#[no_mangle] pub extern "C" fn lean_isize_mul(a: isize, b: isize) -> isize { a.wrapping_mul(b) }
#[no_mangle] pub extern "C" fn lean_isize_div(a: isize, b: isize) -> isize { if b == 0 { 0 } else { a.wrapping_div(b) } }
#[no_mangle] pub extern "C" fn lean_isize_mod(a: isize, b: isize) -> isize { if b == 0 { a } else { a.wrapping_rem(b) } }
#[no_mangle] pub extern "C" fn lean_isize_land(a: isize, b: isize) -> isize { a & b }
#[no_mangle] pub extern "C" fn lean_isize_lor(a: isize, b: isize) -> isize { a | b }
#[no_mangle] pub extern "C" fn lean_isize_xor(a: isize, b: isize) -> isize { a ^ b }
#[no_mangle] pub extern "C" fn lean_isize_shift_left(a: isize, b: isize) -> isize { a.wrapping_shl((b % 64) as u32) }
#[no_mangle] pub extern "C" fn lean_isize_shift_right(a: isize, b: isize) -> isize { a.wrapping_shr((b % 64) as u32) }
#[no_mangle] pub extern "C" fn lean_isize_complement(a: isize) -> isize { !a }
#[no_mangle] pub extern "C" fn lean_isize_log2(a: isize) -> isize { if a == 0 { 0 } else { (64 - 1 - a.leading_zeros()) as isize } }
#[no_mangle] pub extern "C" fn lean_isize_dec_eq(a: isize, b: isize) -> u8 { if a == b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_isize_dec_lt(a: isize, b: isize) -> u8 { if a < b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_isize_dec_le(a: isize, b: isize) -> u8 { if a <= b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_isize_neg(a: isize) -> isize { a.wrapping_neg() }
#[no_mangle] pub extern "C" fn lean_isize_abs(a: isize) -> isize { if a < 0 { a.wrapping_neg() } else { a } }
#[no_mangle] pub extern "C" fn lean_isize_to_uint8(a: isize) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_isize_to_uint16(a: isize) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_isize_to_uint32(a: isize) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_isize_to_uint64(a: isize) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_isize_to_usize(a: isize) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_isize_to_int8(a: isize) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_isize_to_int16(a: isize) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_isize_to_int32(a: isize) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_isize_to_int64(a: isize) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_isize_to_float32(a: isize) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_isize_to_float(a: isize) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_float32_add(a: f32, b: f32) -> f32 { a + b }
#[no_mangle] pub extern "C" fn lean_float32_sub(a: f32, b: f32) -> f32 { a - b }
#[no_mangle] pub extern "C" fn lean_float32_mul(a: f32, b: f32) -> f32 { a * b }
#[no_mangle] pub extern "C" fn lean_float32_div(a: f32, b: f32) -> f32 { if b == 0.0 { 0.0 } else { a / b } }
#[no_mangle] pub extern "C" fn lean_float32_negate(a: f32) -> f32 { -a }
#[no_mangle] pub extern "C" fn lean_float32_beq(a: f32, b: f32) -> u8 { if a == b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_float32_decLe(a: f32, b: f32) -> u8 { if a <= b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_float32_decLt(a: f32, b: f32) -> u8 { if a < b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_float32_to_uint8(a: f32) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_float32_to_uint16(a: f32) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_float32_to_uint32(a: f32) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_float32_to_uint64(a: f32) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_float32_to_usize(a: f32) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_float32_to_int8(a: f32) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_float32_to_int16(a: f32) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_float32_to_int32(a: f32) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_float32_to_int64(a: f32) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_float32_to_isize(a: f32) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_float32_to_float(a: f32) -> f64 { a as f64 }
#[no_mangle] pub extern "C" fn lean_float_add(a: f64, b: f64) -> f64 { a + b }
#[no_mangle] pub extern "C" fn lean_float_sub(a: f64, b: f64) -> f64 { a - b }
#[no_mangle] pub extern "C" fn lean_float_mul(a: f64, b: f64) -> f64 { a * b }
#[no_mangle] pub extern "C" fn lean_float_div(a: f64, b: f64) -> f64 { if b == 0.0 { 0.0 } else { a / b } }
#[no_mangle] pub extern "C" fn lean_float_negate(a: f64) -> f64 { -a }
#[no_mangle] pub extern "C" fn lean_float_beq(a: f64, b: f64) -> u8 { if a == b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_float_decLe(a: f64, b: f64) -> u8 { if a <= b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_float_decLt(a: f64, b: f64) -> u8 { if a < b { 1 } else { 0 } }
#[no_mangle] pub extern "C" fn lean_float_to_uint8(a: f64) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_float_to_uint16(a: f64) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_float_to_uint32(a: f64) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_float_to_uint64(a: f64) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_float_to_usize(a: f64) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_float_to_int8(a: f64) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_float_to_int16(a: f64) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_float_to_int32(a: f64) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_float_to_int64(a: f64) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_float_to_isize(a: f64) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_float_to_float32(a: f64) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_bool_to_uint8(a: u8) -> u8 { a as u8 }
#[no_mangle] pub extern "C" fn lean_bool_to_uint16(a: u8) -> u16 { a as u16 }
#[no_mangle] pub extern "C" fn lean_bool_to_uint32(a: u8) -> u32 { a as u32 }
#[no_mangle] pub extern "C" fn lean_bool_to_uint64(a: u8) -> u64 { a as u64 }
#[no_mangle] pub extern "C" fn lean_bool_to_usize(a: u8) -> usize { a as usize }
#[no_mangle] pub extern "C" fn lean_bool_to_int8(a: u8) -> i8 { a as i8 }
#[no_mangle] pub extern "C" fn lean_bool_to_int16(a: u8) -> i16 { a as i16 }
#[no_mangle] pub extern "C" fn lean_bool_to_int32(a: u8) -> i32 { a as i32 }
#[no_mangle] pub extern "C" fn lean_bool_to_int64(a: u8) -> i64 { a as i64 }
#[no_mangle] pub extern "C" fn lean_bool_to_isize(a: u8) -> isize { a as isize }
#[no_mangle] pub extern "C" fn lean_bool_to_float32(a: u8) -> f32 { a as f32 }
#[no_mangle] pub extern "C" fn lean_bool_to_float(a: u8) -> f64 { a as f64 }
