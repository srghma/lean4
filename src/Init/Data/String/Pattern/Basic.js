const encoder = new TextEncoder();

export function lean_string_memcmp(s1, start1, len1, s2, start2, len2) {
  const b1 = encoder.encode(s1).slice(start1, start1 + len1);
  const b2 = encoder.encode(s2).slice(start2, start2 + len2);
  const minLen = Math.min(b1.length, b2.length);
  for (let i = 0; i < minLen; i++) {
    if (b1[i] !== b2[i]) return b1[i] - b2[i];
  }
  return b1.length - b2.length;
}
