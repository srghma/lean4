const encoder = new TextEncoder();
const decoder = new TextDecoder();

export function lean_string_push(str, char) {
  return str + char;
}

export function lean_string_posof(str, char) {
  const bytes = encoder.encode(str);
  const charBytes = encoder.encode(char);
  for (let i = 0; i <= bytes.length - charBytes.length; i++) {
    let match = true;
    for (let j = 0; j < charBytes.length; j++) {
      if (bytes[i + j] !== charBytes[j]) {
        match = false;
        break;
      }
    }
    if (match) return i;
  }
  return bytes.length;
}

export function lean_string_offsetofpos(str, pos) {
  return pos;
}

export function lean_string_utf8_extract(str, start, len) {
  const bytes = encoder.encode(str);
  return decoder.decode(bytes.slice(start, start + len));
}

export function lean_string_length(str) {
  return [...str].length;
}

export function lean_string_pushn(str, chars) {
  return str + chars.join('');
}

export function lean_string_append(s1, s2) {
  return s1 + s2;
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

export function lean_string_isempty(str) {
  return str.length === 0;
}

export function lean_string_foldl(str, acc, fn) {
  let result = acc;
  for (const char of str) {
    result = fn(result, char);
  }
  return result;
}

export function lean_string_isprefixof(prefix, str) {
  return str.startsWith(prefix);
}

export function lean_string_any(str, fn) {
  for (const char of str) {
    if (fn(char)) return true;
  }
  return false;
}

export function lean_string_contains(str, substr) {
  return str.includes(substr);
}

export function lean_string_utf8_get(str, pos) {
  const bytes = encoder.encode(str);
  return bytes[pos] || 0;
}

export function lean_string_capitalize(str) {
  if (str.length === 0) return str;
  const chars = [...str];
  return chars[0].toUpperCase() + chars.slice(1).join('');
}

export function lean_string_utf8_at_end(str, pos) {
  return pos >= encoder.encode(str).length;
}

export function lean_string_nextwhile(str, pos, fn) {
  const chars = [...str];
  let i = pos;
  while (i < chars.length && fn(chars[i])) {
    i++;
  }
  return i;
}

export function lean_string_trim(str) {
  return str.trim();
}

export function lean_string_intercalate(sep, strs) {
  return strs.join(sep);
}

export function lean_string_front(str) {
  const chars = [...str];
  return chars.length > 0 ? chars[0] : '';
}

export function lean_string_drop(str, n) {
  const chars = [...str];
  return chars.slice(n).join('');
}

export function lean_string_dropright(str, n) {
  const chars = [...str];
  return chars.slice(0, chars.length - n).join('');
}

export function lean_string_get_byte_fast(str, pos) {
  const bytes = encoder.encode(str);
  return bytes[pos] || 0;
}

export function lean_string_mk(chars) {
  return chars.join('');
}

export function lean_substring_tostring(str, start, len) {
  const bytes = encoder.encode(str);
  return decoder.decode(bytes.slice(start, start + len));
}

export function lean_substring_drop(str, start, len, n) {
  return { str: str, start: start + n, len: len - n };
}

export function lean_substring_front(str, start, len) {
  const bytes = encoder.encode(str);
  if (start >= bytes.length) return '';
  const firstByte = bytes[start];
  let l = 0;
  if (firstByte < 0x80) l = 1;
  else if (firstByte < 0xE0) l = 2;
  else if (firstByte < 0xF0) l = 3;
  else if (firstByte < 0xF8) l = 4;
  else l = 1;
  return decoder.decode(bytes.slice(start, start + l));
}

export function lean_substring_takewhile(str, start, len, fn) {
  const bytes = encoder.encode(str);
  let current = start;
  while (current < start + len) {
    const firstByte = bytes[current];
    let l = 0;
    if (firstByte < 0x80) l = 1;
    else if (firstByte < 0xE0) l = 2;
    else if (firstByte < 0xF0) l = 3;
    else if (firstByte < 0xF8) l = 4;
    else l = 1;
    const char = decoder.decode(bytes.slice(current, current + l));
    if (!fn(char)) break;
    current += l;
  }
  return { str: str, start: start, len: current - start };
}

export function lean_substring_extract(str, start, len) {
  const bytes = encoder.encode(str);
  return decoder.decode(bytes.slice(start, start + len));
}

export function lean_substring_all(str, start, len) {
  return { str: str, start: start, len: len };
}

export function lean_substring_beq(s1, start1, len1, s2, start2, len2) {
  if (len1 !== len2) return false;
  const b1 = encoder.encode(s1).slice(start1, start1 + len1);
  const b2 = encoder.encode(s2).slice(start2, start2 + len2);
  if (b1.length !== b2.length) return false;
  for (let i = 0; i < b1.length; i++) {
    if (b1[i] !== b2[i]) return false;
  }
  return true;
}

export function lean_substring_isempty(str, start, len) {
  return len === 0;
}

export function lean_substring_get(str, start, len, pos) {
  const bytes = encoder.encode(str);
  return bytes[start + pos] || 0;
}

export function lean_substring_prev(str, start, len, pos) {
  return { str: str, start: start, len: len, pos: pos - 1 };
}

export function lean_string_pos_sub(pos, n) {
  return pos - n;
}

export function lean_string_pos_min(pos1, pos2) {
  return Math.min(pos1, pos2);
}
