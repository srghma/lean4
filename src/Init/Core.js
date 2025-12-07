// Thunk implementation
export function lean_mk_thunk(fn) {
  let cached = null;
  let evaluated = false;
  return {
    get: () => {
      if (!evaluated) {
        cached = fn();
        evaluated = true;
      }
      return cached;
    }
  };
}

export function lean_thunk_pure(val) {
  return {
    get: () => val
  };
}

export function lean_thunk_get_own(thunk) {
  return thunk.get();
}

// Task implementation
export function lean_task_pure(val) {
  return Promise.resolve(val);
}

export function lean_task_get_own(task) {
  // In JS, this would be an 'await', but since this is a synchronous 
  // call in Lean's runtime, we might need to use a synchronous 
  // wait or assume the task is already resolved for the simplified version.
  // For now, we'll return the promise.
  return task; 
}

export function lean_task_spawn(fn, prio = 0) {
  return Promise.resolve().then(() => fn());
}

export function lean_task_map(f, task, prio = 0, sync = false) {
  return task.then(f);
}

export function lean_task_bind(task, f, prio = 0, sync = false) {
  return task.then(val => f(val));
}

// Boolean operators
export function lean_strict_or(b1, b2) {
  return b1 || b2;
}

export function lean_strict_and(b1, b2) {
  return b1 && b2;
}
