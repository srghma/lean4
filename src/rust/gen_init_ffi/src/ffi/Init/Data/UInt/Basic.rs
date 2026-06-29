// Generated stub file for Lean FFI imports
// Source: src/Init/Data/UInt/Basic.lean

pub fn lean_uint8_add(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}

pub fn lean_uint8_sub(a: u8, b: u8) -> u8 {
    a.wrapping_sub(b)
}

pub fn lean_uint8_mul(a: u8, b: u8) -> u8 {
    a.wrapping_mul(b)
}

pub fn lean_uint8_div(a: u8, b: u8) -> u8 {
    if b == 0 {
        0
    } else {
        a / b
    }
}

pub fn lean_uint8_mod(a: u8, b: u8) -> u8 {
    if b == 0 {
        a
    } else {
        a % b
    }
}

pub fn lean_uint8_land(a: u8, b: u8) -> u8 {
    a & b
}

pub fn lean_uint8_lor(a: u8, b: u8) -> u8 {
    a | b
}

pub fn lean_uint8_xor(a: u8, b: u8) -> u8 {
    a ^ b
}

pub fn lean_uint8_shift_left(a: u8, b: u8) -> u8 {
    a.wrapping_shl(b as u32)
}

pub fn lean_uint8_shift_right(a: u8, b: u8) -> u8 {
    a.wrapping_shr(b as u32)
}

pub fn lean_uint8_complement(a: u8) -> u8 {
    !a
}

pub fn lean_uint8_neg(a: u8) -> u8 {
    a.wrapping_neg()
}

pub fn lean_bool_to_uint8(value: u8) -> u8 {
    value
}

pub fn lean_uint16_add(a: u16, b: u16) -> u16 {
    a.wrapping_add(b)
}

pub fn lean_uint16_sub(a: u16, b: u16) -> u16 {
    a.wrapping_sub(b)
}

pub fn lean_uint16_mul(a: u16, b: u16) -> u16 {
    a.wrapping_mul(b)
}

pub fn lean_uint16_div(a: u16, b: u16) -> u16 {
    if b == 0 {
        0
    } else {
        a / b
    }
}

pub fn lean_uint16_mod(a: u16, b: u16) -> u16 {
    if b == 0 {
        a
    } else {
        a % b
    }
}

pub fn lean_uint16_land(a: u16, b: u16) -> u16 {
    a & b
}

pub fn lean_uint16_lor(a: u16, b: u16) -> u16 {
    a | b
}

pub fn lean_uint16_xor(a: u16, b: u16) -> u16 {
    a ^ b
}

pub fn lean_uint16_shift_left(a: u16, b: u16) -> u16 {
    a.wrapping_shl(b as u32)
}

pub fn lean_uint16_shift_right(a: u16, b: u16) -> u16 {
    a.wrapping_shr(b as u32)
}

pub fn lean_uint16_complement(a: u16) -> u16 {
    !a
}

pub fn lean_uint16_neg(a: u16) -> u16 {
    a.wrapping_neg()
}

pub fn lean_bool_to_uint16(value: u8) -> u16 {
    value as u16
}

pub fn lean_uint16_dec_lt(a: u16, b: u16) -> u8 {
    (a < b) as u8
}

pub fn lean_uint16_dec_le(a: u16, b: u16) -> u8 {
    (a <= b) as u8
}

pub fn lean_uint32_mul(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}

pub fn lean_uint32_div(a: u32, b: u32) -> u32 {
    if b == 0 {
        0
    } else {
        a / b
    }
}

pub fn lean_uint32_mod(a: u32, b: u32) -> u32 {
    if b == 0 {
        a
    } else {
        a % b
    }
}

pub fn lean_uint32_land(a: u32, b: u32) -> u32 {
    a & b
}

pub fn lean_uint32_lor(a: u32, b: u32) -> u32 {
    a | b
}

pub fn lean_uint32_xor(a: u32, b: u32) -> u32 {
    a ^ b
}

pub fn lean_uint32_shift_left(a: u32, b: u32) -> u32 {
    a.wrapping_shl(b)
}

pub fn lean_uint32_shift_right(a: u32, b: u32) -> u32 {
    a.wrapping_shr(b)
}

pub fn lean_uint32_complement(a: u32) -> u32 {
    !a
}

pub fn lean_uint32_neg(a: u32) -> u32 {
    a.wrapping_neg()
}

pub fn lean_bool_to_uint32(value: u8) -> u32 {
    value as u32
}

pub fn lean_uint64_add(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

pub fn lean_uint64_sub(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

pub fn lean_uint64_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

pub fn lean_uint64_div(a: u64, b: u64) -> u64 {
    if b == 0 {
        0
    } else {
        a / b
    }
}

pub fn lean_uint64_mod(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        a % b
    }
}

pub fn lean_uint64_land(a: u64, b: u64) -> u64 {
    a & b
}

pub fn lean_uint64_lor(a: u64, b: u64) -> u64 {
    a | b
}

pub fn lean_uint64_xor(a: u64, b: u64) -> u64 {
    a ^ b
}

pub fn lean_uint64_shift_left(a: u64, b: u64) -> u64 {
    a.wrapping_shl(b as u32)
}

pub fn lean_uint64_shift_right(a: u64, b: u64) -> u64 {
    a.wrapping_shr(b as u32)
}

pub fn lean_uint64_complement(a: u64) -> u64 {
    !a
}

pub fn lean_uint64_neg(a: u64) -> u64 {
    a.wrapping_neg()
}

pub fn lean_bool_to_uint64(value: u8) -> u64 {
    value as u64
}

pub fn lean_uint64_dec_lt(a: u64, b: u64) -> u8 {
    (a < b) as u8
}

pub fn lean_uint64_dec_le(a: u64, b: u64) -> u8 {
    (a <= b) as u8
}

pub fn lean_usize_mul(a: usize, b: usize) -> usize {
    a.wrapping_mul(b)
}

pub fn lean_usize_div(a: usize, b: usize) -> usize {
    if b == 0 {
        0
    } else {
        a / b
    }
}

pub fn lean_usize_mod(a: usize, b: usize) -> usize {
    if b == 0 {
        a
    } else {
        a % b
    }
}

pub fn lean_usize_land(a: usize, b: usize) -> usize {
    a & b
}

pub fn lean_usize_lor(a: usize, b: usize) -> usize {
    a | b
}

pub fn lean_usize_xor(a: usize, b: usize) -> usize {
    a ^ b
}

pub fn lean_usize_shift_left(a: usize, b: usize) -> usize {
    a.wrapping_shl(b as u32)
}

pub fn lean_usize_shift_right(a: usize, b: usize) -> usize {
    a.wrapping_shr(b as u32)
}

// moved lean_usize_of_nat to ffi/common/lean_usize_of_nat__01__47af9c3b.rs, lean_usize_of_nat__02__bcd68a4e.rs, lean_usize_of_nat__03__47d65975.rs
// original source: Init/Data/UInt/Basic.rs:254-256

pub fn lean_uint8_to_usize(value: u8) -> usize {
    value as usize
}

pub fn lean_usize_to_uint8(value: usize) -> u8 {
    value as u8
}

pub fn lean_uint16_to_usize(value: u16) -> usize {
    value as usize
}

pub fn lean_usize_to_uint16(value: usize) -> u16 {
    value as u16
}

pub fn lean_uint32_to_usize(value: u32) -> usize {
    value as usize
}

pub fn lean_usize_to_uint32(value: usize) -> u32 {
    value as u32
}

pub fn lean_uint64_to_usize(value: u64) -> usize {
    value as usize
}

pub fn lean_usize_to_uint64(value: usize) -> u64 {
    value as u64
}

pub fn lean_usize_complement(value: usize) -> usize {
    !value
}

pub fn lean_usize_neg(value: usize) -> usize {
    value.wrapping_neg()
}

pub fn lean_bool_to_usize(value: u8) -> usize {
    value as usize
}
