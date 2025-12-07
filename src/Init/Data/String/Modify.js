const encoder = new TextEncoder();
const decoder = new TextDecoder();

export function lean_string_utf8_set(str, pos, char) {
  const bytes = encoder.encode(str);
  const charBytes = encoder.encode(char);
  if (pos < 0 || pos >= bytes.length) return str;

  let len = 0;
  const firstByte = bytes[pos];
  if (firstByte < 0x80) len = 1;
  else if (firstByte < 0xE0) len = 2;
  else if (firstByte < 0xF0) len = 3;
  else if (firstByte < 0xF8) len = 4;
  else len = 1;

  const resultBytes = new Uint8Array(bytes.length - len + charBytes.length);
  resultBytes.set(bytes.subarray(0, pos));
  resultBytes.set(charBytes, pos);
  resultBytes.set(bytes.subarray(pos + len));
  
  return decoder.decode(resultBytes);
}
