
function f32(val) {
  const buf = new Float32Array(1);
  buf[0] = val;
  return buf[0];
}

export function lean_float32_add(a, b) {
  return f32(a + b);
}

export function lean_float32_sub(a, b) {
  return f32(a - b);
}

export function lean_float32_mul(a, b) {
  return f32(a * b);
}

export function lean_float32_div(a, b) {
  return f32(a / b);
}

export function lean_float32_negate(a) {
  return f32(-a);
}

export function lean_float32_of_bits(bits) {
  const buf = new ArrayBuffer(4);
  const view = new DataView(buf);
  view.setUint32(0, bits);
  return view.getFloat32(0);
}

export function lean_float32_to_bits(f) {
  const buf = new ArrayBuffer(4);
  const view = new DataView(buf);
  view.setFloat32(0, f);
  return view.getUint32(0);
}

export function lean_float32_beq(a, b) {
  return a === b;
}

export function lean_float32_to_string(f) {
  return f.toString();
}

export function lean_float32_to_uint8(f) {
  if (isNaN(f) || f < 0) return 0;
  return Math.max(0, Math.min(255, Math.floor(f)));
}

export function lean_float32_to_uint16(f) {
  if (isNaN(f) || f < 0) return 0;
  return Math.max(0, Math.min(65535, Math.floor(f)));
}

export function lean_float32_to_uint32(f) {
  if (isNaN(f) || f < 0) return 0;
  return Math.max(0, Math.min(4294967295, Math.floor(f)));
}

export function lean_float32_to_uint64(f) {
  if (isNaN(f) || f < 0) return 0n;
  return BigInt(Math.max(0, Math.floor(f)));
}

export function lean_float32_to_usize(f) {
  if (isNaN(f) || f < 0) return 0n;
  return BigInt(Math.max(0, Math.floor(f)));
}

export function lean_float32_isnan(f) {
  return isNaN(f);
}

export function lean_float32_isfinite(f) {
  return isFinite(f);
}

export function lean_float32_isinf(f) {
  return !isFinite(f) && !isNaN(f);
}

export function lean_float32_frexp(f) {
  if (f === 0) return [0, 0];
  const buf = new Float32Array(1);
  buf[0] = f;
  const val = buf[0];
  let exp = Math.floor(Math.log2(Math.abs(val))) + 1;
  let mantissa = val / Math.pow(2, exp);
  return [f32(mantissa), exp];
}

export function lean_uint8_to_float32(n) {
  return f32(n);
}

export function lean_uint16_to_float32(n) {
  return f32(n);
}

export function lean_uint32_to_float32(n) {
  return f32(n);
}

export function lean_uint64_to_float32(n) {
  return f32(Number(n));
}

export function lean_usize_to_float32(n) {
  return f32(Number(n));
}

export function sinf(f) {
  return f32(Math.sin(f));
}

export function cosf(f) {
  return f32(Math.cos(f));
}

export function tanf(f) {
  return f32(Math.tan(f));
}

export function asinf(f) {
  return f32(Math.asin(f));
}

export function acosf(f) {
  return f32(Math.acos(f));
}

export function atanf(f) {
  return f32(Math.atan(f));
}

export function atan2f(y, x) {
  return f32(Math.atan2(y, x));
}

export function sinhf(f) {
  return f32(Math.sinh(f));
}

export function coshf(f) {
  return f32(Math.cosh(f));
}

export function tanhf(f) {
  return f32(Math.tanh(f));
}

export function asinhf(f) {
  return f32(Math.asinh(f));
}

export function acoshf(f) {
  return f32(Math.acosh(f));
}

export function atanhf(f) {
  return f32(Math.atanh(f));
}

export function expf(f) {
  return f32(Math.exp(f));
}

export function exp2f(f) {
  return f32(Math.exp2(f));
}

export function logf(f) {
  return f32(Math.log(f));
}

export function log2f(f) {
  return f32(Math.log2(f));
}

export function log10f(f) {
  return f32(Math.log10(f));
}

export function powf(a, b) {
  return f32(Math.pow(a, b));
}

export function sqrtf(f) {
  return f32(Math.sqrt(f));
}

export function cbrtf(f) {
  return f32(Math.cbrt(f));
}

export function ceilf(f) {
  return f32(Math.ceil(f));
}

export function floorf(f) {
  return f32(Math.floor(f));
}

export function roundf(f) {
  return f32(Math.round(f));
}

export function fabsf(f) {
  return f32(Math.abs(f));
}

export function lean_float32_scaleb(f, exp) {
  return f32(f * Math.pow(2, exp));
}

export function lean_float32_to_float(f) {
  return f;
}

export function lean_float_to_float32(f) {
  return f32(f);
}

export function lean_float32_decLt(...args) {
  throw new Error('not implemented');
}

export function lean_float32_decLe(...args) {
  throw new Error('not implemented');
}
