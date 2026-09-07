export function lean_bitvec_and(x, y, n) {
  return BigInt.asUintN(n, x & y);
}

export function lean_bitvec_or(x, y, n) {
  return BigInt.asUintN(n, x | y);
}

export function lean_bitvec_xor(x, y, n) {
  return BigInt.asUintN(n, x ^ y);
}

export function lean_bitvec_not(x, n) {
  return BigInt.asUintN(n, ~x);
}

export function lean_bitvec_shift_left(x, s, n) {
  return BigInt.asUintN(n, x << s);
}

export function lean_bitvec_ushift_right(x, s, n) {
  return BigInt.asUintN(n, x >> s);
}

export function lean_bitvec_sshift_right(x, s, n) {
  return BigInt.asUintN(n, BigInt.asIntN(n, x) >> s);
}

export function lean_bitvec_rotate_left(x, s, n) {
  const width = BigInt(n);
  const shift = BigInt(s) % width;
  return BigInt.asUintN(n, (x << shift) | (x >> (width - shift)));
}

export function lean_bitvec_rotate_right(x, s, n) {
  const width = BigInt(n);
  const shift = BigInt(s) % width;
  return BigInt.asUintN(n, (x >> shift) | (x << (width - shift)));
}

export function lean_bitvec_append(msbs, lsbs, n, m) {
  return BigInt.asUintN(n + m, (msbs << BigInt(m)) | lsbs);
}

export function lean_bitvec_concat(msbs, lsb, n) {
  const bit = lsb ? 1n : 0n;
  return BigInt.asUintN(n + 1, (msbs << 1n) | bit);
}

export function lean_bitvec_cons(msb, lsbs, n) {
  const bit = msb ? (1n << BigInt(n)) : 0n;
  return BigInt.asUintN(n + 1, bit | lsbs);
}
