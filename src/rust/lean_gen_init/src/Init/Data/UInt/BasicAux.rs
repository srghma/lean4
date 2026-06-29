use crate::leanh::{self, LeanObject};
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/UInt/BasicAux.lean

pub unsafe fn lean_uint8_to_nat(value: u8) -> *mut LeanObject {
    unsafe { leanh::lean_uint8_to_nat(value) }
}

pub unsafe fn lean_uint16_of_nat(value: *mut LeanObject) -> u16 {
    unsafe { leanh::lean_uint16_of_nat(value) }
}

pub unsafe fn lean_uint16_to_nat(value: u16) -> *mut LeanObject {
    unsafe { leanh::lean_uint16_to_nat(value) }
}

pub fn lean_uint16_to_uint8(value: u16) -> u8 {
    value as u8
}

pub fn lean_uint8_to_uint16(value: u8) -> u16 {
    value as u16
}

pub unsafe fn lean_uint32_of_nat(value: *mut LeanObject) -> u32 {
    unsafe { leanh::lean_uint32_of_nat(value) }
}

pub fn lean_uint32_to_uint8(value: u32) -> u8 {
    value as u8
}

pub fn lean_uint32_to_uint16(value: u32) -> u16 {
    value as u16
}

pub fn lean_uint8_to_uint32(value: u8) -> u32 {
    value as u32
}

pub fn lean_uint16_to_uint32(value: u16) -> u32 {
    value as u32
}

pub fn lean_uint32_add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub fn lean_uint32_sub(a: u32, b: u32) -> u32 {
    a.wrapping_sub(b)
}

pub unsafe fn lean_uint64_of_nat(value: *mut LeanObject) -> u64 {
    unsafe { leanh::lean_uint64_of_nat(value) }
}

pub unsafe fn lean_uint64_to_nat(value: u64) -> *mut LeanObject {
    unsafe { leanh::lean_uint64_to_nat(value) }
}

pub fn lean_uint64_to_uint8(value: u64) -> u8 {
    value as u8
}

pub fn lean_uint64_to_uint16(value: u64) -> u16 {
    value as u16
}

pub fn lean_uint64_to_uint32(value: u64) -> u32 {
    value as u32
}

pub fn lean_uint8_to_uint64(value: u8) -> u64 {
    value as u64
}

pub fn lean_uint16_to_uint64(value: u16) -> u64 {
    value as u64
}

pub fn lean_uint32_to_uint64(value: u32) -> u64 {
    value as u64
}

pub unsafe fn lean_usize_of_nat(value: *mut LeanObject) -> usize {
    unsafe { leanh::lean_usize_of_nat(value) }
}

pub unsafe fn lean_usize_to_nat(value: usize) -> *mut LeanObject {
    unsafe { leanh::lean_usize_to_nat(value) }
}

pub unsafe fn lean_usize_add(a: usize, b: usize) -> usize {
    unsafe { leanh::lean_usize_add(a, b) }
}

pub unsafe fn lean_usize_sub(a: usize, b: usize) -> usize {
    unsafe { leanh::lean_usize_sub(a, b) }
}

pub unsafe fn lean_usize_dec_lt(a: usize, b: usize) -> u8 {
    unsafe { leanh::lean_usize_dec_lt(a, b) }
}

pub unsafe fn lean_usize_dec_le(a: usize, b: usize) -> u8 {
    unsafe { leanh::lean_usize_dec_le(a, b) }
}
