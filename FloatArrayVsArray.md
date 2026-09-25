When comparing **`FloatArray`** and **`Array`**, unlike `ByteArray` (which has specialized features like `copySlice`, `hash`, and UTF-8 string decoders), **`FloatArray` provides almost no unique operations**. It is designed as a specialized, unboxed scalar array (`double[]` in C) rather than an array of boxed object pointers (`lean_object*[]`).

---

### 1. APIs that `FloatArray` has which `Array` does not

The only APIs unique to `FloatArray` are the **packing and unpacking functions** to convert between unboxed floats and boxed `Array Float`:

| `FloatArray` API | C Runtime Primitive | Type | Description |
| :--- | :--- | :--- | :--- |
| **`FloatArray.mk`** | `lean_float_array_mk` | `Array Float → FloatArray` | Packs a boxed `Array Float` into a contiguous unboxed `double[]` buffer. |
| **`FloatArray.data`** | `lean_float_array_data` | `FloatArray → Array Float` | Converts the unboxed `FloatArray` back into a standard boxed `Array Float`. |

*(In `Array`, `Array.mk` takes a `List α`, whereas `FloatArray.mk` takes an `Array Float`.)*

---

### 2. 1-to-1 Corresponding APIs

Every other function in `FloatArray` has an exact direct equivalent in `Array`:

| `FloatArray` (Unboxed `Float`) | C Primitive | `Array` (Generic `α`) | C Primitive |
| :--- | :--- | :--- | :--- |
| `FloatArray.size` | `lean_float_array_size` | `Array.size` | `lean_array_get_size` |
| `FloatArray.usize` | `lean_sarray_size` | `Array.usize` | `lean_array_size` |
| `FloatArray.emptyWithCapacity` | `lean_mk_empty_float_array`| `Array.emptyWithCapacity` | `lean_mk_empty_array_with_capacity` |
| `FloatArray.push` | `lean_float_array_push` | `Array.push` | `lean_array_push` |
| `FloatArray.get` | `lean_float_array_fget` | `Array.get` (`getInternal`) | `lean_array_fget` |
| `FloatArray.get!` | `lean_float_array_get` | `Array.get!` (`get!Internal`) | `lean_array_get` |
| `FloatArray.uget` | `lean_float_array_uget` | `Array.uget` | `lean_array_uget` |
| `FloatArray.set` | `lean_float_array_fset` | `Array.set` | `lean_array_fset` |
| `FloatArray.set!` | `lean_float_array_set` | `Array.set!` | `lean_array_set` |
| `FloatArray.uset` | `lean_float_array_uset` | `Array.uset` | `lean_array_uset` |

---

### 3. What `Array` has that `FloatArray` is missing

`FloatArray` is a minimal type. Compared to `Array`, it lacks several primitives:

* **`pop`**: `Array.pop` exists (`lean_array_pop`), but `FloatArray` has no runtime pop primitive.
* **`swap`**: `Array.swap` and `Array.swapIfInBounds` (`lean_array_fswap`, `lean_array_swap`).
* **`replicate` / `mkArray`**: Initializing an array with repeated values (`lean_mk_array`).
* **Borrowed getters**: `Array.getInternalBorrowed`, `Array.ugetBorrowed` (not needed for unboxed floats since primitive numbers copy cheaply without reference counting).
* **`copySlice` / `hash`**: Unlike `ByteArray`, `FloatArray` has neither `copySlice` (memcpy) nor a runtime `hash` primitive (since IEEE-754 `NaN != NaN` makes raw-memory float hashing complex).

---

### Summary

* **`FloatArray` has no algorithmic APIs that `Array` lacks.**
* The only unique APIs are **`FloatArray.mk`** and **`FloatArray.data`**, which convert between boxed `Array Float` and unboxed `FloatArray`.
* Its purpose is purely **performance/memory layout** (a flat C-style `double[]` buffer without heap-allocated boxed float objects).
