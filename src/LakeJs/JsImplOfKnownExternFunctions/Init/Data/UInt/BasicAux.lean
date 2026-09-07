const MASK8 = 0xFFn;
const MASK16 = 0xFFFFn;
const MASK32 = 0xFFFFFFFF;
const MASK64 = 0xFFFFFFFFFFFFFFFFn;
const MASK_USIZE = 0xFFFFFFFF;

const toUInt32 = (a) => Number(a) >>> 0;
const toUSize = (a) => Number(a) >>> 0;

export function lean_uint8_to_nat(a) { return a; }
export function lean_uint16_of_nat(n) { return BigInt(n) & MASK16; }
export function lean_uint16_to_nat(a) { return a; }
export function lean_uint16_to_uint8(a) { return a & MASK8; }
export function lean_uint8_to_uint16(a) { return a & MASK16; }
export function lean_uint32_of_nat(n) { return toUInt32(n); }
export function lean_uint32_to_uint8(a) { return BigInt(toUInt32(a) & 0xFF); }
export function lean_uint32_to_uint16(a) { return BigInt(toUInt32(a) & 0xFFFF); }
export function lean_uint8_to_uint32(a) { return toUInt32(a); }
export function lean_uint16_to_uint32(a) { return toUInt32(a); }
export function lean_uint32_add(a, b) { return (toUInt32(a) + toUInt32(b)) >>> 0; }
export function lean_uint32_sub(a, b) { return (toUInt32(a) - toUInt32(b)) >>> 0; }
export function lean_uint64_of_nat(n) { return BigInt(n) & MASK64; }
export function lean_uint64_to_nat(a) { return a; }
export function lean_uint64_to_uint8(a) { return a & MASK8; }
export function lean_uint64_to_uint16(a) { return a & MASK16; }
export function lean_uint64_to_uint32(a) { return a & MASK32; }
export function lean_uint8_to_uint64(a) { return a & MASK64; }
export function lean_uint16_to_uint64(a) { return a & MASK64; }
export function lean_uint32_to_uint64(a) { return a & MASK64; }
export function lean_usize_of_nat(n) { return toUSize(n); }
export function lean_usize_to_nat(a) { return toUSize(a); }
export function lean_usize_add(a, b) { return (toUSize(a) + toUSize(b)) >>> 0; }
export function lean_usize_sub(a, b) { return (toUSize(a) - toUSize(b)) >>> 0; }
export function lean_usize_dec_lt(a, b) { return toUSize(a) < toUSize(b); }
export function lean_usize_dec_le(a, b) { return toUSize(a) <= toUSize(b); }
