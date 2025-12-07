export function lean_uint8_log2(n) {
  if (n === 0n) return 0n;
  return BigInt(n.toString(2).length - 1);
}

export function lean_uint16_log2(n) {
  if (n === 0n) return 0n;
  return BigInt(n.toString(2).length - 1);
}

export function lean_uint32_log2(n) {
  if (n === 0n) return 0n;
  return BigInt(n.toString(2).length - 1);
}

export function lean_uint64_log2(n) {
  if (n === 0n) return 0n;
  return BigInt(n.toString(2).length - 1);
}

export function lean_usize_log2(n) {
  if (n === 0n) return 0n;
  return BigInt(n.toString(2).length - 1);
}
