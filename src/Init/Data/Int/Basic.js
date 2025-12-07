export function lean_nat_to_int(n) {
  return BigInt(n);
}

export function lean_int_neg_succ_of_nat(n) {
  return -BigInt(n) - 1n;
}

export function lean_int_neg(n) {
  return -n;
}

export function lean_int_add(a, b) {
  return a + b;
}

export function lean_int_mul(a, b) {
  return a * b;
}

export function lean_int_sub(a, b) {
  return a - b;
}

export function lean_int_dec_eq(a, b) {
  return a === b;
}

export function lean_int_dec_nonneg(n) {
  return n >= 0n;
}

export function lean_int_dec_le(a, b) {
  return a <= b;
}

export function lean_int_dec_lt(a, b) {
  return a < b;
}

export function lean_nat_abs(n) {
  return n < 0n ? -n : n;
}
