export function lean_array_size(arr) {
  return arr.length;
}

export function lean_array_uget(arr, idx) {
  return arr[idx];
}

export function lean_array_uget_borrowed(arr, idx) {
  return arr[idx];
}

export function lean_array_uset(arr, idx, val) {
  arr[idx] = val;
  return arr;
}

export function lean_array_pop(arr) {
  arr.pop();
  return arr;
}

export function lean_mk_array(elements) {
  return Array.from(elements);
}

export function lean_array_fswap(arr, idx1, idx2) {
  const tmp = arr[idx1];
  arr[idx1] = arr[idx2];
  arr[idx2] = tmp;
  return arr;
}

export function lean_array_swap(arr, idx1, idx2) {
  const tmp = arr[idx1];
  arr[idx1] = arr[idx2];
  arr[idx2] = tmp;
  return arr;
}
