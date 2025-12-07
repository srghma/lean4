export function lean_nat_gcd(a, b) {
  a = BigInt(a);
  b = BigInt(b);
  while (b !== 0n) {
    a %= b;
    [a, b] = [b, a];
  }
  return a;
}
