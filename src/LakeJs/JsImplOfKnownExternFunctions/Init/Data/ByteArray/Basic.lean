export function lean_sarray_dec_eq(arr1, arr2) {
  if (arr1.length !== arr2.length) return false;
  for (let i = 0; i < arr1.length; i++) {
    if (arr1[i] !== arr2[i]) return false;
  }
  return true;
}

export function lean_sarray_size(arr) {
  return arr.length;
}

export function lean_byte_array_uget(arr, idx) {
  return arr[idx];
}

export function lean_byte_array_get(arr, idx) {
  return arr[idx];
}

export function lean_byte_array_fget(arr, idx) {
  return arr[idx];
}

export function lean_byte_array_set(arr, idx, val) {
  arr[idx] = val;
  return arr;
}

export function lean_byte_array_fset(arr, idx, val) {
  arr[idx] = val;
  return arr;
}

export function lean_byte_array_uset(arr, idx, val) {
  arr[idx] = val;
  return arr;
}

export function lean_byte_array_hash(arr) {
  let hash = 0;
  for (let i = 0; i < arr.length; i++) {
    hash = ((hash << 5) - hash) + arr[i];
    hash |= 0; // Convert to 32bit integer
  }
  return hash;
}

export function lean_byte_array_copy_slice(dst, dstOff, src, srcOff, len) {
  const subarray = src.subarray(srcOff, srcOff + len);
  dst.set(subarray, dstOff);
  return dst;
}
