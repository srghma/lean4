const buffer = new ArrayBuffer(8);
const floatView = new Float64Array(buffer);
const uintView = new BigUint64Array(buffer);

export function lean_float_add(a, b) { return a + b; }
export function lean_float_sub(a, b) { return a - b; }
export function lean_float_mul(a, b) { return a * b; }
export function lean_float_div(a, b) { return a / b; }
export function lean_float_negate(a) { return -a; }

export function lean_float_of_bits(bits) {
  uintView[0] = BigInt(bits);
  return floatView[0];
}

export function lean_float_to_bits(f) {
  floatView[0] = f;
  return uintView[0];
}

export function lean_float_beq(a, b) { return a === b; }

export function lean_float_decLt(a, b) {
  return a < b;
}

export function lean_float_decLe(a, b) {
  return a <= b;
}

export function lean_float_to_string(f) {
  return f.toString();
}

export function lean_float_to_uint8(f) {
  if (isNaN(f) || f < 0) return 0;
  return Math.min(255, Math.floor(f));
}

export function lean_float_to_uint16(f) {
  if (isNaN(f) || f < 0) return 0;
  return Math.min(65535, Math.floor(f));
}

export function lean_float_to_uint32(f) {
  if (isNaN(f) || f < 0) return 0;
  return Math.min(4294967295, Math.floor(f));
}

export function lean_float_to_uint64(f) {
  if (isNaN(f) || f < 0) return 0n;
  return BigInt(Math.min(Number.MAX_SAFE_INTEGER, Math.floor(f)));
}

export function lean_float_to_usize(f) {
  return lean_float_to_uint64(f);
}

export function lean_float_isnan(f) { return isNaN(f); }
export function lean_float_isfinite(f) { return isFinite(f); }
export function lean_float_isinf(f) { return !isFinite(f) && !isNaN(f); }

export function lean_float_frexp(f) {
  // JS doesn't have frexp, but we can simulate it
  if (f === 0) return [0, 0];
  const exp = Math.floor(Math.log2(Math.abs(f))) + 1;
  const frac = f / Math.pow(2, exp);
  return [frac, exp];
}

export function lean_uint8_to_float(n) { return Number(n); }
export function lean_uint16_to_float(n) { return Number(n); }
export function lean_uint32_to_float(n) { return Number(n); }
export function lean_uint64_to_float(n) { return Number(n); }
export function lean_usize_to_float(n) { return Number(n); }

export function sin(f) { return Math.sin(f); }
export function cos(f) { return Math.cos(f); }
export function tan(f) { return Math.tan(f); }
export function asin(f) { return Math.asin(f); }
export function acos(f) { return Math.acos(f); }
export function atan(f) { return Math.atan(f); }
export function atan2(y, x) { return Math.atan2(y, x); }
export function sinh(f) { return Math.sinh(f); }
export function cosh(f) { return Math.cosh(f); }
export function tanh(f) { return Math.tanh(f); }
export function asinh(f) { return Math.asinh(f); }
export function acosh(f) { return Math.acosh(f); }
export function atanh(f) { return Math.atanh(f); }
export function exp(f) { return Math.exp(f); }
export function exp2(f) { return Math.pow(2, f); }
export function log(f) { return Math.log(f); }
export function log2(f) { return Math.log2(f); }
export function log10(f) { return Math.log10(f); }
export function pow(a, b) { return Math.pow(a, b); }
export function sqrt(f) { return Math.sqrt(f); }
export function cbrt(f) { return Math.cbrt(f); }
export function ceil(f) { return Math.ceil(f); }
export function floor(f) { return Math.floor(f); }
export function round(f) { return Math.round(f); }
export function fabs(f) { return Math.abs(f); }

export function lean_float_scaleb(x, i) {
  return x * Math.pow(2, Number(i));
}
