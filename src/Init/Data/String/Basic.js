const encoder = new TextEncoder();
const decoder = new TextDecoder();

export function lean_string_validate_utf8(str) {
  try {
    encoder.encode(str);
    return true;
  } catch (e) {
    return false;
  }
}

export function lean_string_data(str) {
  return encoder.encode(str);
}

export function lean_string_length(str) {
  return [...str].length;
}

export function lean_string_dec_lt(s1, s2) {
  return s1 < s2;
}

export function lean_string_is_valid_pos(str, pos) {
  const bytes = encoder.encode(str);
  return pos >= 0 && pos <= bytes.length;
}

export function lean_string_utf8_extract(str, start, len) {
  const bytes = encoder.encode(str);
  return decoder.decode(bytes.slice(start, start + len));
}

export function lean_string_utf8_get_fast(str, pos) {
  const bytes = encoder.encode(str);
  return bytes[pos] || 0;
}

export function lean_string_utf8_next_fast(str, pos) {
  const bytes = encoder.encode(str);
  if (pos >= bytes.length) return { value: null, next: pos };
  const firstByte = bytes[pos];
  let len = 0;
  if (firstByte < 0x80) len = 1;
  else if (firstByte < 0xE0) len = 2;
  else if (firstByte < 0xF0) len = 3;
  else if (firstByte < 0xF8) len = 4;
  else len = 1;
  if (pos + len > bytes.length) len = bytes.length - pos;
  const char = decoder.decode(bytes.slice(pos, pos + len));
  return { value: char, next: pos + len };
}

export function lean_string_utf8_get(str, pos) {
  const bytes = encoder.encode(str);
  return bytes[pos] || 0;
}

export function lean_string_utf8_get_opt(str, pos) {
  const bytes = encoder.encode(str);
  if (pos < 0 || pos >= bytes.length) return null;
  return bytes[pos];
}

export function lean_string_utf8_get_bang(str, pos) {
  const bytes = encoder.encode(str);
  return bytes[pos] || 0;
}

export function lean_string_utf8_next(str, pos) {
  const bytes = encoder.encode(str);
  if (pos >= bytes.length) return { value: null, next: pos };
  const firstByte = bytes[pos];
  let len = 0;
  if (firstByte < 0x80) len = 1;
  else if (firstByte < 0xE0) len = 2;
  else if (firstByte < 0xF0) len = 3;
  else if (firstByte < 0xF8) len = 4;
  else len = 1;
  if (pos + len > bytes.length) len = bytes.length - pos;
  const char = decoder.decode(bytes.slice(pos, pos + len));
  return { value: char, next: pos + len };
}

export function lean_string_utf8_prev(str, pos) {
  const bytes = encoder.encode(str);
  if (pos <= 0) return { value: null, next: pos };
  let i = pos - 1;
  while (i > 0 && (bytes[i] & 0xC0) === 0x80) {
    i--;
  }
  const firstByte = bytes[i];
  let len = 0;
  if (firstByte < 0x80) len = 1;
  else if (firstByte < 0xE0) len = 2;
  else if (firstByte < 0xF0) len = 3;
  else if (firstByte < 0xF8) len = 4;
  else len = 1;
  const char = decoder.decode(bytes.slice(i, i + len));
  return { value: char, next: i };
}

export function lean_string_utf8_at_end(str, pos) {
  const bytes = encoder.encode(str);
  return pos >= bytes.length;
}
