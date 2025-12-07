const MASK8 = 0xFFn;
const MASK16 = 0xFFFFn;
const MASK32 = 0xFFFFFFFFn;
const MASK64 = 0xFFFFFFFFFFFFFFFFn;
const MASK_USIZE = 0xFFFFFFFFFFFFFFFFn;

export function lean_uint8_add(a, b) { return (a + b) & MASK8; }
export function lean_uint8_sub(a, b) { return (a - b) & MASK8; }
export function lean_uint8_mul(a, b) { return (a * b) & MASK8; }
export function lean_uint8_div(a, b) { return a / b; }
export function lean_uint8_mod(a, b) { return a % b; }
export function lean_uint8_land(a, b) { return a & b; }
export function lean_uint8_lor(a, b) { return a | b; }
export function lean_uint8_xor(a, b) { return a ^ b; }
export function lean_uint8_shift_left(a, b) { return (a << b) & MASK8; }
export function lean_uint8_shift_right(a, b) { return a >> b; }
export function lean_uint8_complement(a) { return (~a) & MASK8; }
export function lean_uint8_neg(a) { return (0n - a) & MASK8; }
export function lean_bool_to_uint8(b) { return b ? 1n : 0n; }

export function lean_uint16_add(a, b) { return (a + b) & MASK16; }
export function lean_uint16_sub(a, b) { return (a - b) & MASK16; }
export function lean_uint16_mul(a, b) { return (a * b) & MASK16; }
export function lean_uint16_div(a, b) { return a / b; }
export function lean_uint16_mod(a, b) { return a % b; }
export function lean_uint16_land(a, b) { return a & b; }
export function lean_uint16_lor(a, b) { return a | b; }
export function lean_uint16_xor(a, b) { return a ^ b; }
export function lean_uint16_shift_left(a, b) { return (a << b) & MASK16; }
export function lean_uint16_shift_right(a, b) { return a >> b; }
export function lean_uint16_complement(a) { return (~a) & MASK16; }
export function lean_uint16_neg(a) { return (0n - a) & MASK16; }
