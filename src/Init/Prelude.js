function mkListNil() {
  return { tag: "List$nil" };
}

function mkListCons(head, tail) {
  return { tag: "List$cons", _1: head, _2: tail };
}

function arrayToList(arr) {
  let out = mkListNil();
  for (let i = arr.length - 1; i >= 0; i--) {
    out = mkListCons(arr[i], out);
  }
  return out;
}

function listToArray(list) {
  const out = [];
  let curr = list;
  while (curr.tag === "List$cons") {
    out.push(curr._1);
    curr = curr._2;
  }
  return out;
}

export function Function$comp(f, g, x) {
  return f(g(x));
}

export function lean_array_push(arr, value) {
  const out = arr.slice();
  out.push(value);
  return out;
}

export function lean_array_to_list(arr) {
  return arrayToList(arr);
}

export function lean_array_mk(list) {
  return listToArray(list);
}

export function lean_array_get(defaultValue, arr, idx) {
  return idx < arr.length ? arr[idx] : defaultValue;
}

export function lean_array_get_borrowed(defaultValue, arr, idx) {
  return idx < arr.length ? arr[idx] : defaultValue;
}

export function lean_array_fget_borrowed(arr, idx) {
  return arr[idx];
}

export function lean_uint32_to_nat(n) {
  return n >>> 0;
}

export function lean_uint32_dec_eq(a, b) {
  return (a >>> 0) === (b >>> 0);
}

export function lean_uint32_dec_lt(a, b) {
  return (a >>> 0) < (b >>> 0);
}

export function lean_uint32_dec_le(a, b) {
  return (a >>> 0) <= (b >>> 0);
}

export function lean_string_dec_eq(a, b) {
  return a === b;
}

export function lean_panic_fn_borrowed(_, msg) {
  throw new Error(String(msg));
}

// ByteArray → UInt8 → ByteArray
export function lean_byte_array_push(a, b) {
  const newArr = new Uint8Array(a.length + 1);
  newArr.set(a);
  newArr[a.length] = b;
  return newArr;
}
