export function lean_void_mk(a) {
  return a;
}

export function lean_st_mk_ref(a) {
  return { value: a };
}

export function lean_st_ref_get(ref) {
  return ref.value;
}

export function lean_st_ref_set(ref, a) {
  ref.value = a;
  return null;
}

export function lean_st_ref_swap(ref, a) {
  const old = ref.value;
  ref.value = a;
  return old;
}

export function lean_st_ref_take(ref) {
  const old = ref.value;
  ref.value = undefined;
  return old;
}

export function lean_st_ref_ptr_eq(ref1, ref2) {
  return ref1 === ref2;
}
