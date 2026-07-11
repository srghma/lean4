use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/UInt/BasicAux.lean

// moved lean_uint8_to_nat to ffi/common/lean_uint8_to_nat.rs
// original source: Init/Data/UInt/BasicAux.rs:5-7

// moved lean_uint16_of_nat to ffi/common/lean_uint16_of_nat.rs
// original source: Init/Data/UInt/BasicAux.rs:9-11

// moved lean_uint16_to_nat to ffi/common/lean_uint16_to_nat.rs
// original source: Init/Data/UInt/BasicAux.rs:12-14

pub fn lean_uint16_to_uint8(value: u16) -> u8 {
    value as u8
}

pub fn lean_uint8_to_uint16(value: u8) -> u16 {
    value as u16
}

// moved lean_uint32_of_nat to ffi/common/lean_uint32_of_nat.rs
// original source: Init/Data/UInt/BasicAux.rs:23-25

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

// moved lean_uint64_of_nat to ffi/common/lean_uint64_of_nat.rs
// original source: Init/Data/UInt/BasicAux.rs:50-52

// moved lean_uint64_to_nat to ffi/common/lean_uint64_to_nat.rs
// original source: Init/Data/UInt/BasicAux.rs:53-55

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

// moved lean_usize_of_nat to ffi/common/lean_usize_of_nat.rs
// original source: Init/Data/UInt/BasicAux.rs:79-81

// moved lean_usize_to_nat to ffi/common/lean_usize_to_nat.rs
// original source: Init/Data/UInt/BasicAux.rs:82-84

pub unsafe fn lean_usize_add(a: usize, b: usize) -> usize {
    a.wrapping_add(b)
}

pub unsafe fn lean_usize_sub(a: usize, b: usize) -> usize {
    a.wrapping_sub(b)
}

pub use crate::r#priv::uint_family::lean_usize_dec_le;
pub use crate::r#priv::uint_family::lean_usize_dec_lt;
