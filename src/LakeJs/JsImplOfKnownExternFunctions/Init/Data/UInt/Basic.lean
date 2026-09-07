const MASK8 = 0xFFn;
const MASK16 = 0xFFFFn;
const MASK32 = 0xFFFFFFFFn;
const MASK64 = 0xFFFFFFFFFFFFFFFFn;
const MASK_USIZE = 0xFFFFFFFFFFFFFFFFn;

const toUInt32 = (a) => Number(a) >>> 0;

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

export function lean_bool_to_uint16(...args) {
  throw new Error('not implemented');
}

export function lean_uint16_dec_lt(...args) {
  throw new Error('not implemented');
}

export function lean_uint16_dec_le(...args) {
  throw new Error('not implemented');
}

export function lean_uint32_mul(a, b) { return Math.imul(toUInt32(a), toUInt32(b)) >>> 0; }

export function lean_uint32_div(a, b) {
  const bb = toUInt32(b);
  return bb === 0 ? 0 : Math.floor(toUInt32(a) / bb) >>> 0;
}

export function lean_uint32_mod(a, b) {
  const aa = toUInt32(a);
  const bb = toUInt32(b);
  return bb === 0 ? aa : aa % bb;
}

export function lean_uint32_land(a, b) { return (toUInt32(a) & toUInt32(b)) >>> 0; }

export function lean_uint32_lor(a, b) { return (toUInt32(a) | toUInt32(b)) >>> 0; }

export function lean_uint32_xor(a, b) { return (toUInt32(a) ^ toUInt32(b)) >>> 0; }

export function lean_uint32_shift_left(a, b) { return (toUInt32(a) << (toUInt32(b) & 31)) >>> 0; }

export function lean_uint32_shift_right(a, b) { return toUInt32(a) >>> (toUInt32(b) & 31); }

export function lean_uint32_complement(a) { return (~toUInt32(a)) >>> 0; }

export function lean_uint32_neg(a) { return (-toUInt32(a)) >>> 0; }

export function lean_bool_to_uint32(b) { return b ? 1 : 0; }

export function lean_uint64_add(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_sub(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_mul(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_div(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_mod(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_land(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_lor(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_xor(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_shift_left(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_shift_right(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_complement(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_neg(...args) {
  throw new Error('not implemented');
}

export function lean_bool_to_uint64(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_dec_lt(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_dec_le(...args) {
  throw new Error('not implemented');
}

export function lean_usize_mul(...args) {
  throw new Error('not implemented');
}

export function lean_usize_div(...args) {
  throw new Error('not implemented');
}

export function lean_usize_mod(...args) {
  throw new Error('not implemented');
}

export function lean_usize_land(...args) {
  throw new Error('not implemented');
}

export function lean_usize_lor(...args) {
  throw new Error('not implemented');
}

export function lean_usize_xor(...args) {
  throw new Error('not implemented');
}

export function lean_usize_shift_left(...args) {
  throw new Error('not implemented');
}

export function lean_usize_shift_right(...args) {
  throw new Error('not implemented');
}

export function lean_usize_of_nat(...args) {
  throw new Error('not implemented');
}

export function lean_uint8_to_usize(...args) {
  throw new Error('not implemented');
}

export function lean_usize_to_uint8(...args) {
  throw new Error('not implemented');
}

export function lean_uint16_to_usize(...args) {
  throw new Error('not implemented');
}

export function lean_usize_to_uint16(...args) {
  throw new Error('not implemented');
}

export function lean_uint32_to_usize(...args) {
  throw new Error('not implemented');
}

export function lean_usize_to_uint32(...args) {
  throw new Error('not implemented');
}

export function lean_uint64_to_usize(...args) {
  throw new Error('not implemented');
}

export function lean_usize_to_uint64(...args) {
  throw new Error('not implemented');
}

export function lean_usize_complement(...args) {
  throw new Error('not implemented');
}

export function lean_usize_neg(...args) {
  throw new Error('not implemented');
}

export function lean_bool_to_usize(...args) {
  throw new Error('not implemented');
}
