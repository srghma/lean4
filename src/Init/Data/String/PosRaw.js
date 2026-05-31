const encoder = new TextEncoder();

export function lean_string_get_byte_fast(str, pos) {
  const bytes = encoder.encode(str);
  return bytes[pos] || 0;
}
