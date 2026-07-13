Yes — `rc` is exactly the free trigger. Here's the full chain:

---

## The free chain, step by step

### Step 1 — `lean_dec_ref` (inline fast path, `lean.h:574`)

```c
static inline void lean_dec_ref(lean_object * o) {
    if (LEAN_LIKELY(o->m_rc > 1)) {
        o->m_rc--;          // rc was 3→2, 2→2 etc — still alive, done
    } else if (o->m_rc != 0) {
        lean_dec_ref_cold(o); // rc was 1 (ST) or rc < 0 (MT) — might free
    }
    // rc == 0 → persistent → no-op, falls through
}
```

The `LEAN_LIKELY(rc > 1)` branch is the common case — almost free (one non-atomic decrement). `lean_dec_ref_cold` is the slow path, called only when rc is 1 or negative (MT).

---

### Step 2 — `lean_dec_ref_cold` (`object.cpp:443`)

```c
void lean_dec_ref_cold(lean_object * o) {
    if (o->m_rc == 1                                               // ST: last reference
        || atomic_fetch_add(lean_get_rc_mt_addr(o), 1) == -1) {   // MT: was -1, now 0 → last ref
        // This object is now unreachable. Delete it.
        object * todo = nullptr;
        while (true) {
            lean_del_core(o, todo);   // delete o, push its children onto todo
            if (todo == nullptr) return;
            o = pop_back(todo);       // pick next child to delete
        }
    }
    // else: MT, rc was e.g. -3 → now -2, still alive
}
```

The `atomic_fetch_add(..., 1)` is counterintuitive: MT objects use **negative** rc. Incrementing by +1 moves it toward 0. When it was `-1` (one reference left), after `+1` it becomes `0` — meaning the object is unreachable, free it.

The `todo` list is the key: instead of recursive calls (which would overflow the stack for long chains like `List 1000000`), deletion is **iterative**. Dead children are pushed onto a linked list and freed in a loop.

---

### Step 3 — `lean_del_core` (`object.cpp:431`) — type-dispatch destructor

```c
static void lean_del_core(object * o, object * & todo) {
    uint8 tag = lean_ptr_tag(o);
    if (LEAN_LIKELY(tag <= LeanMaxCtorTag)) {          // Ctor (most common)
        object ** it  = lean_ctor_obj_cptr(o);         // pointer fields
        object ** end = it + lean_ctor_num_objs(o);
        for (; it != end; ++it) dec(*it, todo);        // dec each child
        lean_free_small_object(o);                     // free the ctor itself
    } else {
        lean_del_core_other(o, tag, todo);             // String/Array/Closure/etc.
    }
}
```

`dec(child, todo)` — the inner child decrement:
```c
static inline void dec(lean_object * o, lean_object * & todo) {
    if (lean_is_scalar(o)) return;          // unboxed int → skip
    if (LEAN_LIKELY(o->m_rc > 1)) {
        o->m_rc--;                          // still alive
    } else if (o->m_rc == 1) {
        push_back(todo, o);                 // ST last ref → queue for deletion
    } else if (o->m_rc == 0) {
        return;                             // persistent → skip
    } else if (atomic_fetch_add(lean_get_rc_mt_addr(o), 1) == -1) {
        push_back(todo, o);                 // MT last ref → queue for deletion
    }
}
```

Dead children go onto `todo`; the outer `while` loop in `lean_dec_ref_cold` picks them up.

---

### Step 4 — `lean_del_core_other` (`object.cpp:381`) — type-specific cleanup

```c
case LeanString:
    lean_dealloc(o, lean_string_byte_size(o));    // just free(), no children
    break;

case LeanArray:
    for each element: dec(element, todo);          // dec all lean_object* elements
    lean_dealloc(o, lean_array_byte_size(o));
    break;

case LeanClosure:
    for each captured arg: dec(arg, todo);
    lean_dealloc(o, lean_closure_byte_size(o));
    break;

case LeanThunk:
    if (closure) dec(closure, todo);
    if (value)   dec(value,   todo);
    lean_free_small_object(o);
    break;

case LeanRef:
    dec(stored_value, todo);
    lean_free_small_object(o);
    break;

case LeanExternal:
    o->m_class->m_finalize(o->m_data);   // call user-registered finalizer first
    lean_free_small_object(o);
    break;

case LeanMPZ:
    mpz_value.~mpz();                    // GMP destructor for the big integer
    lean_free_small_object(o);
    break;

case LeanScalarArray:
    lean_dealloc(o, lean_sarray_byte_size(o));   // raw bytes, no children
    break;
```

---

### Step 5 — the actual `free()`

```c
static inline void lean_dealloc(lean_object * o, size_t sz) {
    mi_free_size(o, sz);   // mimalloc (or free_sized / dealloc for other backends)
}

static inline void lean_free_small_object(lean_object * o) {
    mi_free(o);            // mimalloc for "small" objects (no size hint needed)
}
```

---

## Applied to the `v_foobar_` example

```
lean_io_println(v_foobar_)
  → borrows v_foobar_ for printing
  → calls lean_dec_ref(v_foobar_) when done

lean_dec_ref(v_foobar_):
  rc was 1 (ST exclusive, freshly allocated)
  → LEAN_LIKELY(rc > 1) is FALSE
  → rc != 0 → calls lean_dec_ref_cold(v_foobar_)

lean_dec_ref_cold(v_foobar_):
  rc == 1 → this is the last reference
  todo = nullptr
  lean_del_core(v_foobar_, todo):
    tag == LeanString (249) → lean_del_core_other
    case LeanString:
      lean_dealloc(v_foobar_, lean_string_byte_size(v_foobar_))
      → mi_free_size(v_foobar_, sizeof(lean_string_object) + capacity)
      ← heap allocation freed ✓
    todo still nullptr → return
```

`v_foo_` (the `.rodata` persistent string) is **never touched** — `lean_dec_ref` sees `rc == 0` and returns immediately without entering the cold path at all.

---

## Summary

| rc value             | `lean_dec_ref` result                             |
| -------------------- | ------------------------------------------------- |
| `> 1`                | `rc--`, done (fast path, no call)                 |
| `== 1` (ST last ref) | call `lean_dec_ref_cold` → delete                 |
| `== 0` (persistent)  | no-op, falls through                              |
| `< 0` (MT)           | `lean_dec_ref_cold` → atomic check → maybe delete |

The actual `free()` is always one of:
- `lean_dealloc(o, sz)` → `mi_free_size` / `free_sized` — for variable-size objects (String, Array, ScalarArray, Closure)
- `lean_free_small_object(o)` → `mi_free` — for fixed-size objects (Ctor, Ref, Thunk, Task, External, MPZ)

And deletion is **iterative**, not recursive — the `todo` linked list encodes the work using the object's own `m_rc`/`m_cs_sz` header bits as the next-pointer (the 48-bit packing trick).
