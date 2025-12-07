
export function lean_float_array_mk(data) {
  return { data: new Float64Array(data) };
}

export function lean_float_array_data(fa) {
  return fa.data;
}

export function lean_mk_empty_float_array(capacity) {
  return { data: new Float64Array(0) };
}

export function lean_float_array_push(fa, val) {
  const newData = new Float64Array(fa.data.length + 1);
  newData.set(fa.data);
  newData[fa.data.length] = val;
  return { data: newData };
}

export function lean_float_array_size(fa) {
  return fa.data.length;
}

export function lean_float_array_uget(fa, i, proof) {
  return fa.data[i];
}

export function lean_float_array_fget(fa, i, proof) {
  return fa.data[i];
}

export function lean_float_array_get(fa, i) {
  if (i < 0 || i >= fa.data.length) return NaN;
  return fa.data[i];
}

export function lean_float_array_uset(fa, i, val, proof) {
  const newData = new Float64Array(fa.data);
  newData[i] = val;
  return { data: newData };
}

export function lean_float_array_fset(fa, i, val, proof) {
  const newData = new Float64Array(fa.data);
  newData[i] = val;
  return { data: newData };
}

export function lean_float_array_set(fa, i, val) {
  if (i < 0 || i >= fa.data.length) return fa;
  const newData = new Float64Array(fa.data);
  newData[i] = val;
  return { data: newData };
}
