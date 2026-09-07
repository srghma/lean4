
function clamp(val, min, max) {
  if (isNaN(val)) return 0;
  return Math.max(min, Math.min(max, Math.trunc(val)));
}

export function lean_float_to_int8(f) {
  return clamp(f, -128, 127);
}

export function lean_float_to_int16(f) {
  return clamp(f, -32768, 32767);
}

export function lean_float_to_int32(f) {
  return clamp(f, -2147483648, 2147483647);
}

export function lean_float_to_int64(f) {
  if (isNaN(f)) return 0n;
  const val = BigInt(Math.trunc(f));
  const min = -(2n ** 63n);
  const max = (2n ** 63n) - 1n;
  if (val < min) return min;
  if (val > max) return max;
  return val;
}

export function lean_float_to_isize(f) {
  // Assuming 64-bit ISize for JS environment
  return lean_float_to_int64(f);
}

export function lean_int8_to_float(n) {
  return n;
}

export function lean_int16_to_float(n) {
  return n;
}

export function lean_int32_to_float(n) {
  return n;
}

export function lean_int64_to_float(n) {
  return Number(n);
}

export function lean_isize_to_float(n) {
  return Number(n);
}
