export function lean_int_emod(a, b) {
  a = BigInt(a);
  b = BigInt(b);
  if (b === 0n) return a;
  let r = a % b;
  if (r < 0n) {
    r += (b < 0n ? -b : b);
  }
  return r;
}

export function lean_int_ediv(a, b) {
  a = BigInt(a);
  b = BigInt(b);
  if (b === 0n) return 0n;
  return (a - lean_int_emod(a, b)) / b;
}

export function lean_int_div_exact(a, b) {
  a = BigInt(a);
  b = BigInt(b);
  if (b === 0n) return false;
  return a % b === 0n;
}

export function lean_int_div(a, b) {
  a = BigInt(a);
  b = BigInt(b);
  if (b === 0n) return 0n;
  return a / b;
}

export function lean_int_mod(a, b) {
  a = BigInt(a);
  b = BigInt(b);
  if (b === 0n) return a;
  return a % b;
}
