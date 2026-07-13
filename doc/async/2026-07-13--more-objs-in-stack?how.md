❯ lean team told they want to make more types stack-allocated to improve speed                                                                                                        
                                                                                                                                                                                      
  what and how they will do

-------
# ⚡ Lean Team Plan: Stack-Allocated Types

The Lean team wants to make more types stack-allocated to improve speed. Here is the analysis of the current scaffolding in the `origin-master` source.

---

## 🏗️ What and how: $\color{cyan}{\text{IRType.struct}}$ and $\color{orange}{\text{IRType.union}}$

The plan is already **partially built** — the IR types are defined, the linearity rules are documented, and the emitters have stubs — but the actual code generation is not yet implemented.

### 💡 The core idea

Today, every `Option T`, `Prod A B`, `Except E A`, etc. is **$\color{red}{\text{heap-allocated}}$** as a `lean_ctor_object` with a full header:

```text
lean_alloc_ctor(tag, num_objs, scalar_sz)
  → malloc(sizeof(lean_ctor_object) + n*ptr + scalar_bytes)
  → sets m_rc = 1, m_tag = ..., m_other = n
```

That's a `malloc` + refcount overhead for every `Option`, every `Result`, every pair.

The goal: **return these small types on the $\color{green}{\text{stack}}$ as a plain C struct with no header, no malloc, no refcount**.

---

### 🔍 The IR already has the types: `Basic.lean:77-84`

```lean
inductive IRType where
  | float | uint8 | uint16 | uint32 | uint64 | usize
  | erased | object | tobject
  | float32
  | struct (leanTypeName : Option Name) (types : Array IRType)  -- ← stack value
  | union  (leanTypeName : Name)         (types : Array IRType) -- ← tagged stack value
  | tagged
  | void
```

The **design comment** (IR/Basic.lean:58-75):

```text
- `struct` and `union` are used to return small values (e.g., `Option`, `Prod`,
   `Except`) on the stack.

Since values of type `struct` and `union` are only used to return values,
we assume they must be used/consumed "linearly" — used exactly once:
  1. only at a single `ret x` — returned
  2. only at a single `ctor` — stored into another struct
  3. we project every single field exactly once — consumed field-by-field
```

**$\color{magenta}{\text{Linear}}$ = no reference counting needed at all.** A struct value on the stack is owned, not shared, so there is no RC header.

---

### 🛠️ What EmitC / EmitLLVM would generate

For `Option T` today (heap):
```c
// def foo := some x
lean_object* r = lean_alloc_ctor(1, 1, 0);   // malloc!
lean_ctor_set(r, 0, x);
return r;                                      // heap pointer, rc=1
```

With `IRType.struct` for `Option T` on stack (planned):
```c
// struct { uint8_t tag; lean_object* val; }
typedef struct { uint8_t _tag; lean_object* _0; } lean_Option_obj;

lean_Option_obj r;
r._tag = 1;   // .some
r._0   = x;
return r;     // returned in registers (two words), zero malloc
```

The caller immediately decomposes it:
```c
if (r._tag == 0) { /* none */ }
else { use(r._0); lean_dec(r._0); }  // dec the object, not the struct (struct has no header)
```

---

### 🚦 Status in the emitters

**EmitLLVM.lean:344-345** — the stub is literally:
```lean
| IRType.struct _ _ => panic! "not implemented yet"
| IRType.union _ _  => panic! "not implemented yet"
```

**`@[unbox]` attribute** — `UnboxResult.lean:13-31`:
```lean
-- "compiler tries to unbox result values if their types are tagged with `[unbox]`"
builtin_initialize unboxAttr : TagAttribute ← ...
-- ...
-- This attribute currently has no effect.
```

The attribute is registered and can be parsed, but the pass that would actually perform the transformation doesn't exist yet.

---

### ⚖️ `struct` vs `union`: two different cases

**`struct`** — when all constructors have the same shape or only one constructor:
```text
-- Prod A B  →  struct [object, object]
-- generated C: struct { lean_object* fst; lean_object* snd; }
```

**`union`** — when the tag (constructor index) matters for dispatch:
```text
-- Option T  →  union Option_T_t [object]
--   ctor 0 = none  (no fields)
--   ctor 1 = some  (one field)
-- generated C: struct { uint8_t tag; union { lean_object* some; } data; }
--    or just: struct { uint8_t tag; lean_object* val; }
```

The `proj` IR instruction also does double duty — for `union`, it's a **cast** between union arms (since the tag tells you which arm is live). For `struct`, it's a plain **field projection** (`x._0`, `x._1`).

---

### 📦 The `LeanStructArray` tag (247) — the other direction

There is also `LeanStructArray` (tag 247) in `lean.h:96`, which is a separate plan: arrays where each **element** is an unboxed struct rather than a heap pointer. Currently barely used (no accessor functions defined, only appears in one place in `compact.cpp`). This would avoid per-element `malloc` for arrays of `Prod Float Float` etc.

---

### 🛡️ Why the linearity constraint makes it safe

Heap objects need RC because they can be aliased (shared across multiple variables). A `struct` value returned on the stack/in registers **cannot be aliased** — it's moved, not cloned. So:

- No `m_rc` field
- No `lean_inc` / `lean_dec` on the struct itself
- The **contained** `lean_object*` fields still need their own RC (they're separate heap objects), but the **wrapper struct** has zero overhead

This is exactly why the rule says "used exactly once" — it enforces move semantics statically.

---

### 📝 Summary

| What | Status | How |
| :--- | :--- | :--- |
| `IRType.struct`/`.union` in IR | **defined** | `Basic.lean:81-82` |
| Linearity rules | **documented** | `Basic.lean:67-75` |
| `@[unbox]` attribute | **registered, no effect** | `UnboxResult.lean` |
| C code generation | **not implemented** | `EmitC.lean_` has no struct case |
| LLVM code generation | **not implemented** | `panic! "not implemented yet"` |
| `LeanStructArray` | **tag reserved only** | `lean.h:96` |

The machinery is scaffolded. The missing piece is the compiler passes that (1) decide which types qualify for `IRType.struct`/`.union`, (2) verify linearity, and (3) emit the actual C struct / LLVM aggregate return code.


---------------------
----------------------


# 🔍 LCNF EmitC Implementation Status

Reading the actual LCNF EmitC code from the file, here is an accurate breakdown of what is currently implemented in `origin-master`.

---

## ✅ What's already $\color{green}{\text{implemented}}$ in upstream/master

### 1. Static $\color{magenta}{\text{.rodata}}$ for ground/static constants — `emitGroundDecl` 💎

This is the biggest win. For any `isSimpleGroundDecl` (a closed expression with no runtime deps), the emitter outputs a C static initializer instead of a heap allocation:

```c
// Option.some (a constant string) — no malloc, lives in .rodata
static const lean_string_object l_foo___closed__0_value =
  {.m_header = {.m_rc = 0, .m_cs_sz = 3, .m_other = 0, .m_tag = 249},
   .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "foo"};
static const lean_object* l_foo___closed__0 = (const lean_object*)&l_foo___closed__0_value;
```

This covers `.string`, `.ctor`, `.pap`, `.array`, `.byteArray` — each gets a `static const <type> ... = {...}` in C. **Zero malloc** at runtime for these. The `mkHeader` / `LEAN_SCALAR_PTR_LITERAL` helpers encode header fields directly.

### 2. Lazy `lean_once_cell_t` for non-ground/dynamic/heap-or-stack closed terms ⏳

For terms that can't be expressed as static initializers (need computation), `emitFnDeclClosed` emits:
```c
static lean_once_cell_t l_foo_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_foo;
// ...
// at call site:
lean_obj_once(&l_foo, &l_foo_once, _init_l_foo);
```
Computed once, stored, returned on subsequent calls — no repeated allocation.

### 3. Reset/reuse optimization — `emitReset` / `emitReuse` ♻️

The "Counting Immutable Beans" optimization is implemented:
```c
if (lean_is_exclusive(x)) {
    lean_ctor_release(x, 0);  // drop fields
    result = x;               // reuse the block
} else {
    lean_dec_ref(x);
    result = lean_box(0);
}
```
For `emitReuse`: if the old object is exclusive, overwrite its tag and fields in-place instead of calling `lean_alloc_ctor`.

### 4. Tail-call via `goto _start` ➰

Self-recursive tail calls don't allocate stack frames:
```c
_start:
  // ... body ...
  x = arg; goto _start;   // tail call → loop
```
`emitTailCall` handles the parameter overwrite with temporaries to avoid clobber, then emits `goto _start`.

### 5. Stack array for large applies 📚

```c
// when args.size > closureMaxArgs:
lean_object* _aargs[] = {a0, a1, ..., aN};
result = lean_apply_m(f, N, _aargs);
```
The argument array is **stack-allocated**, not heap-allocated.

### 6. Scalar unboxing throughout 🔢

`uint8_t`, `uint16_t`, `uint32_t`, `uint64_t`, `double`, `float`, `size_t` — all passed as plain C values. No boxing unless crossing a `lean_object*` boundary. `emitBox`/`emitUnbox` are explicit IR operations.

---

## ❌ What is $\color{red}{\text{NOT yet done}}$

`IRType.struct` and `IRType.union` both fall through to $\color{orange}{\text{unreachable!}}$ in `toCType`:

```lean
def Lean.Expr.toCType : Expr → String
  | float   => "double"
  | uint8   => "uint8_t"
  ...
  | void    => "lean_object*"
  | _       => unreachable!   -- ← struct and union land here
```

So `Option T`, `Prod A B`, `Except E A` returned as stack structs — **still not implemented**. All non-ground constructors still go through `lean_alloc_ctor`. The `unreachable!` means the IR pipeline won't actually produce these types yet (they'd crash), not that it silently falls back.

---

## 📊 Summary Table

| Optimization | Status | Mechanism |
| :--- | :--- | :--- |
| **Constants in $\color{magenta}{\text{.rodata}}$** | **Done** | `isSimpleGroundDecl` → `static const` |
| **Lazy closed terms** | **Done** | `lean_once_cell_t` |
| **Reset/reuse blocks** | **Done** | `emitReset` / `emitReuse` |
| **Tail recursion → loop** | **Done** | `goto _start` |
| **Scalar unboxing** | **Done** | `uint8_t` / `double` etc. in params |
| **Tagged pointer Nats** | **Done** | `lean_box(n)` for small scalars |
| **`struct`/`union` returns** | $\color{red}{\text{Not Done}}$ | $\color{orange}{\text{unreachable!}}$ |

The **rodata static initializer** approach is the largest real "stack/no-heap" win already shipped. The `struct`/`union` return value optimization (for `Option`, `Prod`, `Except`) is the remaining major unimplemented piece.
