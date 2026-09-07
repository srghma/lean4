const encoder = new TextEncoder();

export function lean_string_to_utf8(str) {
  return encoder.encode(str);
}

export function lean_string_append(s1, s2) {
  return s1 + s2;
}

export function String$intercalate(sep, xs) {
  const parts = [];
  let curr = xs;
  while (curr.tag === "List$cons") {
    parts.push(curr._1);
    curr = curr._2;
  }
  return parts.join(sep);
}
