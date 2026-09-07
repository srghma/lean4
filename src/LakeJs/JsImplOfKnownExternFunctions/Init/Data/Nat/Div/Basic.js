export function lean_nat_div_exact(a, b) {
  if (b === 0n) return false;
  return a % b === 0n;
}
