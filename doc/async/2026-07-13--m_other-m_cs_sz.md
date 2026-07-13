# 📦 Lean Object Memory Layout

The shared header embedded at the start of every heap/non-heap Lean object.

### 🧵 **m_rc** — reference count / threading sentinel
* `> 0` single-threaded (ST): non-atomic inc/dec
* `< 0` multi-threaded (MT): atomic inc/dec
* `== 0` persistent (immortal): no refcounting at all
* **Note:** During deallocation on 64-bit: m_rc + m_cs_sz together hold the low 48 bits of the "next" pointer in the deletion TODO list.

### 📏 **m_cs_sz** — meaning depends on context (16 bits)
* **Non-heap / persistent objects (rc == 0):**
    * "Small" objects (ctor, ref, mpz, task, thunk, promise, external): stores the object's total byte size so `lean_object_byte_size()` works without allocator page lookups.
    * "Big" objects (array, sarray, string, closure): set to 1 (sentinel meaning "big/variable-size; compute size from own fields").
    * **NOTE:** generated static constants for strings/arrays set `m_cs_sz=0` (not 1) because `lean_object_byte_size()` has explicit cases for them that use their own `m_capacity` / `m_num_fixed` fields regardless.
* **Heap objects (rc != 0):**
    * With mimalloc or small-allocator: stores the allocated slot size (set by `lean_alloc_small_object`) so `lean_small_object_size()` works.
    * Without those allocators: unused (= 0); size is stored in the word immediately before the allocation pointer.
    * **Warning:** During deallocation: repurposed as the low 16 bits of the "next" deletion-list pointer — do NOT read it as a size at that point.

### 📂 **m_other** — type-specific 8-bit field; see each struct below.

### 🏷️ **m_tag** — object type discriminant (0–243 = ctor tag, 244–255 = special).

```c
typedef struct {
    int      m_rc;
    unsigned m_cs_sz : 16;
    unsigned m_other : 8;
    unsigned m_tag   : 8;
} lean_object;
```

---

## 🏗️ Object Types

### 📥 tag 0–243 (**LeanMaxCtorTag**)
**m_cs_sz**: byte size of the whole object (for non-heap/persistent ctors).
* Heap ctors: from allocator page / m_cs_sz slot.
* Computed as: `sizeof(lean_ctor_object) + num_objs*sizeof(void*) + scalar_sz`

**m_other**: num_objs — the number of `lean_object*` pointer fields in `m_objs[]`.
* Scalar fields (u8/u32/u64/etc.) are packed after the pointer array; their total byte size is NOT stored here — it's implied by the object's total size minus the pointer area.
* Accessor: `lean_ctor_num_objs(o)`

```c
typedef struct {
    lean_object   m_header;
    lean_object * m_objs[];  /* [0..num_objs-1] pointers, then scalar bytes */
} lean_ctor_object;
```

### 🚀 tag **LeanArray** = 246
**m_cs_sz**: 0 for heap; 1 for non-heap (size computed from m_capacity).
**m_other**: unused, always 0.

```c
typedef struct {
    lean_object   m_header;
    size_t        m_size;      /* number of live elements */
    size_t        m_capacity;  /* allocated slots */
    lean_object * m_data[];    /* flexible array of lean_object* */
} lean_array_object;
```

### 🔗 tag **LeanStructArray** = 247 
*(reserved/future; not yet used in practice)*
**m_cs_sz**: 0 for heap; 1 for non-heap.
**m_other**: unused, always 0.
*(shares the same struct layout as lean_array_object)*

### 🔢 tag **LeanScalarArray** = 248
**m_cs_sz**: 0 for heap; 1 for non-heap (size computed from elem_size*capacity).
**m_other**: elem_size — byte size of each scalar element:
* `1` = u8 (ByteArray / UInt8Array)
* `2` = u16
* `4` = u32 / Float32Array
* `8` = u64 / FloatArray
* Accessor: `lean_sarray_elem_size(o)` — used to compute byte offsets and total allocation size (`sizeof(lean_sarray_object) + elem_size*capacity`).

```c
typedef struct {
    lean_object m_header;
    size_t      m_size;      /* number of live elements */
    size_t      m_capacity;  /* allocated slots */
    uint8_t     m_data[];    /* raw bytes; stride = m_other */
} lean_sarray_object;
```

### 🧵 tag **LeanString** = 249
**m_cs_sz**: 0 for heap; 0 or 1 for non-heap (size computed from m_capacity).
* Static const string literals in generated C set `m_cs_sz=0` even for non-heap — `lean_string_byte_size()` uses m_capacity so it works.

**m_other**: unused, always 0.
* String length and byte size are in the struct's own fields.

```c
typedef struct {
    lean_object m_header;
    size_t      m_size;      /* byte length including '\0' terminator */
    size_t      m_capacity;  /* allocated byte capacity */
    size_t      m_length;    /* number of Unicode code points (UTF-8 chars) */
    char        m_data[];    /* UTF-8 bytes; always NUL-terminated */
} lean_string_object;
```

### 🧪 tag **LeanClosure** = 245
**m_cs_sz**: 0 for heap; `sizeof(lean_closure_object)+num_fixed*sizeof(void*)` for non-heap (but `lean_closure_byte_size()` always recomputes from m_num_fixed, so this field is informational in the non-heap case).
**m_other**: unused, always 0.
* Arity and captured-count are in the struct's own uint16_t fields.

```c
typedef struct {
    lean_object   m_header;
    void *        m_fun;       /* function pointer: (arg0, ..., argN-1) -> result */
    uint16_t      m_arity;     /* total arguments m_fun expects */
    uint16_t      m_num_fixed; /* how many captured args already applied (= len of m_objs) */
    lean_object * m_objs[];    /* captured arguments [0..m_num_fixed-1] */
} lean_closure_object;
```

### 📍 tag **LeanRef** = 253
**m_cs_sz**: byte size of lean_ref_object (for non-heap); allocator size (for heap).
**m_other**: unused, always 0.

```c
typedef struct {
    lean_object   m_header;
    lean_object * m_value;   /* the currently stored value (ST.Ref / IO.Ref) */
} lean_ref_object;
```

### 💤 tag **LeanThunk** = 251
**m_cs_sz**: byte size of lean_thunk_object (for non-heap); allocator size (for heap).
**m_other**: unused, always 0.

```c
typedef struct {
    lean_object            m_header;
    _Atomic(lean_object *) m_value;    /* result once forced; null = not yet forced */
    _Atomic(lean_object *) m_closure;  /* closure to force; null once forced */
} lean_thunk_object;
```

### 👷 tag **LeanTask** = 252
**m_cs_sz**: byte size of lean_task_object (for non-heap); allocator size (for heap).
**m_other**: unused, always 0.

```c
typedef struct lean_task {
    lean_object            m_header;
    _Atomic(lean_object *) m_value;  /* result; non-null means Finished */
    lean_task_imp *        m_imp;    /* execution state; null once Finished */
} lean_task_object;
```

### 🤝 tag **LeanPromise** = 244
**m_cs_sz**: byte size of lean_promise_object (for non-heap); allocator size (for heap).
**m_other**: unused, always 0.

```c
typedef struct lean_promise {
    lean_object        m_header;
    lean_task_object * m_result;  /* the backing task (same layout as lean_task_object) */
} lean_promise_object;
```

### 🧮 tag **LeanMPZ** = 250
**m_cs_sz**: byte size of lean_mpz_object (for non-heap); allocator size (for heap).
**m_other**: unused, always 0.
* GMP stores its own size/sign/limb-count inside the mpz_t.
*(lean_mpz_object defined in runtime — contains lean_object header + mpz_t)*

### 🔌 tag **LeanExternal** = 254
**m_cs_sz**: sizeof(lean_external_object) — always "small", always from allocator.
**m_other**: unused, always 0.
* The external class pointer carries the finalize/foreach vtable.

```c
typedef struct {
    lean_object           m_header;
    lean_external_class * m_class;  /* vtable: finalize(data), foreach(data, visitor) */
    void *                m_data;   /* opaque payload managed by the external class */
} lean_external_object;
```

---

## 📊 Quick Reference Table

| Type | m_other | m_cs_sz (non-heap) | m_cs_sz (heap) |
| :--- | :--- | :--- | :--- |
| **Ctor 0–243** | `num_objs` (pointer field count) | full byte size | allocator slot size |
| **ScalarArray 248** | `elem_size` (1/2/4/8 bytes) | 1 (big sentinel) | allocator slot size |
| **Array 246** | 0 | 1 (big sentinel) | 0 or alloc size |
| **String 249** | 0 | 0 (static) or 1 | 0 or alloc size |
| **Closure 245** | 0 | full byte size | 0 |
| **Ref/Thunk/Task/Promise/External/MPZ** | 0 | full byte size | alloc slot size |

> The only types that actually USE m_other at runtime are Ctor (lean_ctor_num_objs) and ScalarArray (lean_sarray_elem_size). Everything else always writes and reads 0.
