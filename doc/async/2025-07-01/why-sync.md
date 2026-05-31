- **`sync := true`**: The task is executed synchronously if its dependency (the input task `t` or `x`) has already completed (i.e., `t->m_value` is non-null). In this case, the function `f` is applied immediately to the result of the completed task, and a new `Task` is created with the result wrapped in `lean_task_pure`. If the dependency is not yet complete, the task is enqueued with a special priority (`LEAN_SYNC_PRIO`), indicating it should be treated as a high-priority task that runs as soon as its dependency resolves, but still asynchronously in the task manager.

The `sync` flag is used to optimize task execution when the dependency is already resolved, avoiding unnecessary task creation and queuing overhead. However, it comes with constraints, as noted in the `wait_for` function: calling `Task.get` from a task with `sync := true` is forbidden because it could lead to deadlocks or thread pool exhaustion, as synchronous tasks are expected to be "cheap" (non-blocking).

### Code Analysis

#### `lean_task_map_core`

```cpp
extern "C" LEAN_EXPORT obj_res lean_task_map_core(obj_arg f, obj_arg t, unsigned prio,
      bool sync, bool keep_alive) {
    if (!g_task_manager || (sync && lean_to_task(t)->m_value)) {
        return lean_task_pure(apply_1(f, lean_task_get_own(t)));
    } else {
        lean_task_object * new_task = alloc_task(mk_closure_3_2(task_map_fn, f, t), sync ? LEAN_SYNC_PRIO : prio, keep_alive);
        g_task_manager->add_dep(lean_to_task(t), new_task);
        return (lean_object*)new_task;
    }
}
```

- **When `sync := true`**: If the task manager is absent (`!g_task_manager`) or the input task `t` has already completed (`lean_to_task(t)->m_value`), the function `f` is applied immediately to the result of `t` (via `lean_task_get_own(t)`), and the result is wrapped in a `Task` using `lean_task_pure`. This avoids creating a new task in the task manager.
- **When `sync := false`**: A new task is created with the closure `task_map_fn` (which applies `f` to `t`’s result when `t` completes) and enqueued with the specified `prio`. The new task is added as a dependency of `t` via `add_dep`.

#### `lean_task_bind_core`

```cpp
extern "C" LEAN_EXPORT obj_res lean_task_bind_core(obj_arg x, obj_arg f, unsigned prio,
      bool sync, bool keep_alive) {
    if (!g_task_manager || (sync && lean_to_task(x)->m_value)) {
        return apply_1(f, lean_task_get_own(x));
    } else {
        lean_task_object * new_task = alloc_task(mk_closure_3_2(task_bind_fn1, x, f), sync ? LEAN_SYNC_PRIO : prio, keep_alive);
        g_task_manager->add_dep(lean_to_task(x), new_task);
        return (lean_object*)new_task;
    }
}
```

- Similar to `lean_task_map_core`, but for binding. When `sync := true` and the input task `x` is complete, `f` is applied directly to `x`’s result. Otherwise, a new task is created and enqueued with `LEAN_SYNC_PRIO` if `sync` is true.

### Why `sync := true` in `Promise.result!`?

The `Promise.result!` function is defined as:

```lean
def Promise.result! (promise : @& Promise α) : Task α :=
  let _ : Nonempty α := promise.h
  promise.result?.map (sync := true) Option.getOrBlock!
```

- **Why `sync := true`?**:
  - **Immediate Execution**: If the promise’s result task (`promise.result?`) is already resolved (i.e., the promise has been fulfilled with a value), `sync := true` ensures that `Option.getOrBlock!` is applied immediately to the `Option α` result, producing a `Task α` with the value. This avoids unnecessary task creation and queuing.
  - **High Priority**: If the promise’s result task is not yet resolved, setting `sync := true` assigns `LEAN_SYNC_PRIO` (maximum priority) to the mapped task, ensuring it runs as soon as the promise resolves. This is appropriate for `Promise.result!`, which is expected to deliver the result as quickly as possible without waiting in a lower-priority queue.

If `sync := false` were used:

- Even if the promise’s result task is already resolved, a new task would be created and enqueued with default or specified priority, introducing unnecessary overhead.
- The task would compete with other tasks in the queue, potentially delaying the delivery of the promise’s result, which contradicts the expectation of `Promise.result!` to provide the result as soon as it’s available.
