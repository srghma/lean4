export function lean_slice_hash(str, start, len) {
  const s = str.substring(start, start + len);
  let hash = 0;
  for (let i = 0; i < s.length; i++) {
    hash = (hash << 5) - hash + s.charCodeAt(i);
    hash |= 0;
  }
  return hash;
}

export function lean_slice_dec_lt(s1, start1, len1, s2, start2, len2) {
  const sub1 = s1.substring(start1, start1 + len1);
  const sub2 = s2.substring(start2, start2 + len2);
  return sub1 < sub2;
}
