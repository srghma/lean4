export const lean_dbg_trace = (s, f) => {
  console.log(s);
  return f();
};

export const lean_dbg_trace_if_shared = (s, a) => {
  return a;
};

export const lean_dbg_stack_trace = (f) => {
  console.trace();
  return f();
};

export const lean_dbg_stack_trace_if = (cond, f) => {
  if (cond) {
    console.trace();
  }
  return f();
};

export function lean_dbg_sleep(...args) {
  throw new Error('not implemented');
}

export function lean_ptr_addr(...args) {
  throw new Error('not implemented');
}

export function lean_is_exclusive_obj(...args) {
  throw new Error('not implemented');
}

export function mkPanicMessageWithDecl(modName, declName, line, col, msg) {
  return `${modName}:${declName}:${line}:${col}: ${msg}`;
}
