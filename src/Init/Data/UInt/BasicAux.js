const MASK8 = 0xFFn;
const MASK16 = 0xFFFFn;
const MASK32 = 0xFFFFFFFFn;
const MASK64 = 0xFFFFFFFFFFFFFFFFn;
const MASK_USIZE = 0xFFFFFFFFFFFFFFFFn;

export function lean_uint8_to_nat(a) { return a; }
export function lean_uint16_of_nat(n) { return BigInt(n) & MASK16; }
export function lean_uint16_to_nat(a) { return a; }
export function lean_uint16_to_uint8(a) { return a & MASK8; }
export function lean_uint8_to_uint16(a) { return a & MASK16; }
export function lean_uint32_of_nat(n) { return BigInt(n) & MASK32; }
export function lean_uint32_to_uint8(a) { return a & MASK8; }
export function lean_uint32_to_uint16(a) { return a & MASK16; }
export function lean_uint8_to_uint32(a) { return a & MASK32; }
export function lean_uint16_to_uint32(a) { return a & MASK32; }
export function lean_uint32_add(a, b) { return (a + b) & MASK32; }
export function lean_uint32_sub(a, b) { return (a - b) & MASK32; }
export function lean_uint64_of_nat(n) { return BigInt(n) & MASK64; }
export function lean_uint64_to_nat(a) { return a; }
export function lean_uint64_to_uint8(a) { return a & MASK8; }
export function lean_uint64_to_uint16(a) { return a & MASK16; }
export function lean_uint64_to_uint32(a) { return a & MASK32; }
export function lean_uint8_to_uint64(a) { return a & MASK64; }
export function lean_uint16_to_uint64(a) { return a & MASK64; }
export function lean_uint32_to_uint64(a) { return a & MASK64; }
export function lean_usize_of_nat(n) { return BigInt(n) & MASK_USIZE; }
export function lean_usize_to_nat(a) { return a; }
export function lean_usize_add(a, b) { return (a + b) & MASK_USIZE; }
export function lean_usize_sub(a, b) { return (a - b) & MASK_USIZE; }
export function lean_usize_dec_lt(a, b) { return a < b; }
export function lean_usize_dec_le(a, b) { return a <= b; }
