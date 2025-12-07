const MASK8 = 0xFFn;
const MASK16 = 0xFFFFn;
const MASK32 = 0xFFFFFFFFn;
const MASK64 = 0xFFFFFFFFFFFFFFFFn;

function toSigned(n, mask, bits) {
  let val = n & mask;
  if (val & (1n << (bits - 1))) {
    return val - (1n << bits);
  }
  return val;
}

function fromSigned(n, mask) {
  return BigInt(n) & mask;
}

export function lean_int8_of_int(n) { return fromSigned(n, MASK8); }
export function lean_int8_of_nat(n) { return fromSigned(n, MASK8); }
export function lean_int8_to_int(n) { return toSigned(n, MASK8, 8); }
export function lean_int8_neg(n) { return fromSigned(-toSigned(n, MASK8, 8), MASK8); }
export function lean_int8_add(a, b) { return fromSigned(toSigned(a, MASK8, 8) + toSigned(b, MASK8, 8), MASK8); }
export function lean_int8_sub(a, b) { return fromSigned(toSigned(a, MASK8, 8) - toSigned(b, MASK8, 8), MASK8); }
export function lean_int8_mul(a, b) { return fromSigned(toSigned(a, MASK8, 8) * toSigned(b, MASK8, 8), MASK8); }
export function lean_int8_div(a, b) { return fromSigned(toSigned(a, MASK8, 8) / toSigned(b, MASK8, 8), MASK8); }
export function lean_int8_mod(a, b) { return fromSigned(toSigned(a, MASK8, 8) % toSigned(b, MASK8, 8), MASK8); }
export function lean_int8_land(a, b) { return a & b; }
export function lean_int8_lor(a, b) { return a | b; }
export function lean_int8_xor(a, b) { return a ^ b; }
export function lean_int8_shift_left(a, b) { return (a << b) & MASK8; }
export function lean_int8_shift_right(a, b) { return (toSigned(a, MASK8, 8) >> b) & MASK8; }
export function lean_int8_complement(a) { return (~a) & MASK8; }
export function lean_int8_abs(a) {
  let s = toSigned(a, MASK8, 8);
  return fromSigned(s < 0n ? -s : s, MASK8);
}
export function lean_int8_dec_eq(a, b) { return a === b; }
export function lean_bool_to_int8(b) { return b ? 1n : 0n; }
export function lean_int8_dec_lt(a, b) { return toSigned(a, MASK8, 8) < toSigned(b, MASK8, 8); }
export function lean_int8_dec_le(a, b) { return toSigned(a, MASK8, 8) <= toSigned(b, MASK8, 8); }

export function lean_int16_of_int(n) { return fromSigned(n, MASK16); }
export function lean_int16_of_nat(n) { return fromSigned(n, MASK16); }
export function lean_int16_to_int(n) { return toSigned(n, MASK16, 16); }
export function lean_int16_to_int8(n) { return n & MASK8; }
export function lean_int8_to_int16(n) { return n & MASK16; }
export function lean_int16_neg(n) { return fromSigned(-toSigned(n, MASK16, 16), MASK16); }
export function lean_int16_add(a, b) { return fromSigned(toSigned(a, MASK16, 16) + toSigned(b, MASK16, 16), MASK16); }
export function lean_int16_sub(a, b) { return fromSigned(toSigned(a, MASK16, 16) - toSigned(b, MASK16, 16), MASK16); }
export function lean_int16_mul(a, b) { return fromSigned(toSigned(a, MASK16, 16) * toSigned(b, MASK16, 16), MASK16); }
export function lean_int16_div(a, b) { return fromSigned(toSigned(a, MASK16, 16) / toSigned(b, MASK16, 16), MASK16); }
export function lean_int16_mod(a, b) { return fromSigned(toSigned(a, MASK16, 16) % toSigned(b, MASK16, 16), MASK16); }
export function lean_int16_land(a, b) { return a & b; }
export function lean_int16_lor(a, b) { return a | b; }
export function lean_int16_xor(a, b) { return a ^ b; }
export function lean_int16_shift_left(a, b) { return (a << b) & MASK16; }
export function lean_int16_shift_right(a, b) { return (toSigned(a, MASK16, 16) >> b) & MASK16; }
export function lean_int16_complement(a) { return (~a) & MASK16; }
export function lean_int16_abs(a) {
  let s = toSigned(a, MASK16, 16);
  return fromSigned(s < 0n ? -s : s, MASK16);
}
export function lean_int16_dec_eq(a, b) { return a === b; }
export function lean_bool_to_int16(b) { return b ? 1n : 0n; }
export function lean_int16_dec_lt(a, b) { return toSigned(a, MASK16, 16) < toSigned(b, MASK16, 16); }
export function lean_int16_dec_le(a, b) { return toSigned(a, MASK16, 16) <= toSigned(b, MASK16, 16); }

export function lean_int32_of_int(n) { return fromSigned(n, MASK32); }
export function lean_int32_of_nat(n) { return fromSigned(n, MASK32); }
export function lean_int32_to_int(n) { return toSigned(n, MASK32, 32); }
export function lean_int32_to_int8(n) { return n & MASK8; }
export function lean_int32_to_int16(n) { return n & MASK16; }
export function lean_int8_to_int32(n) { return n & MASK32; }
export function lean_int16_to_int32(n) { return n & MASK32; }
export function lean_int32_neg(n) { return fromSigned(-toSigned(n, MASK32, 32), MASK32); }
export function lean_int32_add(a, b) { return fromSigned(toSigned(a, MASK32, 32) + toSigned(b, MASK32, 32), MASK32); }
export function lean_int32_sub(a, b) { return fromSigned(toSigned(a, MASK32, 32) - toSigned(b, MASK32, 32), MASK32); }
export function lean_int32_mul(a, b) { return fromSigned(toSigned(a, MASK32, 32) * toSigned(b, MASK32, 32), MASK32); }
export function lean_int32_div(a, b) { return fromSigned(toSigned(a, MASK32, 32) / toSigned(b, MASK32, 32), MASK32); }
export function lean_int32_mod(a, b) { return fromSigned(toSigned(a, MASK32, 32) % toSigned(b, MASK32, 32), MASK32); }
export function lean_int32_land(a, b) { return a & b; }
export function lean_int32_lor(a, b) { return a | b; }
export function lean_int32_xor(a, b) { return a ^ b; }
export function lean_int32_shift_left(a, b) { return (a << b) & MASK32; }
export function lean_int32_shift_right(a, b) { return (toSigned(a, MASK32, 32) >> b) & MASK32; }
export function lean_int32_complement(a) { return (~a) & MASK32; }
export function lean_int32_abs(a) {
  let s = toSigned(a, MASK32, 32);
  return fromSigned(s < 0n ? -s : s, MASK32);
}
export function lean_int32_dec_eq(a, b) { return a === b; }
export function lean_bool_to_int32(b) { return b ? 1n : 0n; }
export function lean_int32_dec_lt(a, b) { return toSigned(a, MASK32, 32) < toSigned(b, MASK32, 32); }
export function lean_int32_dec_le(a, b) { return toSigned(a, MASK32, 32) <= toSigned(b, MASK32, 32); }

export function lean_int64_of_int(n) { return fromSigned(n, MASK64); }
export function lean_int64_of_nat(n) { return fromSigned(n, MASK64); }
export function lean_int64_to_int_sint(n) { return toSigned(n, MASK64, 64); }
export function lean_int64_to_int8(n) { return n & MASK8; }
export function lean_int64_to_int16(n) { return n & MASK16; }
export function lean_int64_to_int32(n) { return n & MASK32; }
export function lean_int8_to_int64(n) { return n & MASK64; }
export function lean_int16_to_int64(n) { return n & MASK64; }
export function lean_int32_to_int64(n) { return n & MASK64; }
export function lean_int64_neg(n) { return fromSigned(-toSigned(n, MASK64, 64), MASK64); }
export function lean_int64_add(a, b) { return fromSigned(toSigned(a, MASK64, 64) + toSigned(b, MASK64, 64), MASK64); }
export function lean_int64_sub(a, b) { return fromSigned(toSigned(a, MASK64, 64) - toSigned(b, MASK64, 64), MASK64); }
export function lean_int64_mul(a, b) { return fromSigned(toSigned(a, MASK64, 64) * toSigned(b, MASK64, 64), MASK64); }
export function lean_int64_div(a, b) { return fromSigned(toSigned(a, MASK64, 64) / toSigned(b, MASK64, 64), MASK64); }
export function lean_int64_mod(a, b) { return fromSigned(toSigned(a, MASK64, 64) % toSigned(b, MASK64, 64), MASK64); }
export function lean_int64_land(a, b) { return a & b; }
export function lean_int64_lor(a, b) { return a | b; }
export function lean_int64_xor(a, b) { return a ^ b; }
export function lean_int64_shift_left(a, b) { return (a << b) & MASK64; }
export function lean_int64_shift_right(a, b) { return (toSigned(a, MASK64, 64) >> b) & MASK64; }
export function lean_int64_complement(a) { return (~a) & MASK64; }
export function lean_int64_abs(a) {
  let s = toSigned(a, MASK64, 64);
  return fromSigned(s < 0n ? -s : s, MASK64);
}
export function lean_int64_dec_eq(a, b) { return a === b; }
export function lean_bool_to_int64(b) { return b ? 1n : 0n; }
export function lean_int64_dec_lt(a, b) { return toSigned(a, MASK64, 64) < toSigned(b, MASK64, 64); }
export function lean_int64_dec_le(a, b) { return toSigned(a, MASK64, 64) <= toSigned(b, MASK64, 64); }

export function lean_isize_of_int(n) { return fromSigned(n, MASK64); }
export function lean_isize_of_nat(n) { return fromSigned(n, MASK64); }
export function lean_isize_to_int(n) { return toSigned(n, MASK64, 64); }
export function lean_isize_to_int8(n) { return n & MASK8; }
export function lean_isize_to_int16(n) { return n & MASK16; }
export function lean_isize_to_int32(n) { return n & MASK32; }
export function lean_isize_to_int64(n) { return n & MASK64; }
export function lean_int8_to_isize(n) { return n & MASK64; }
