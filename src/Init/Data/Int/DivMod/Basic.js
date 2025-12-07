export function lean_int_emod(a, b) {
  if (b === 0n) throw new Error("Division by zero");
  let r = a % b;
  if (r < 0n) {
    r += (b < 0n ? -b : b);
  }
  return r;
}

export function lean_int_ediv(a, b) {
  if (b === 0n) throw new Error("Division by zero");
  return (a - lean_int_emod(a, b)) / b;
}

export function lean_int_div_exact(a, b) {
  if (b === 0n) return false;
  return a % b === 0n;
}

export function lean_int_div(a, b) {
  if (b === 0n) throw new Error("Division by zero");
  return a / b;
}

export function lean_int_mod(a, b) {
  if (b === 0n) throw new Error("Division by zero");
  return a % b;
}
