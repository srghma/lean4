Based on the provided tables and Lean’s implementation, here are the APIs and runtime primitives that **`ByteArray`** has which generic **`Array`** does not have:

---

### 1. Memory / Buffer Operations
* **`ByteArray.copySlice` (`lean_byte_array_copy_slice`)**
  * **Type:** `(@& ByteArray) → Nat → ByteArray → Nat → Nat → optParam Bool Bool.true → ByteArray`
  * **What it does:** Copies a range of bytes from one byte array into another at a specified destination offset. Under the hood, this compiles to an efficient raw memory copy (`memcpy`). Generic `Array` only provides slicing via `extract` (creating a new array), not a direct in-place/buffer slice-copying primitive.

---

### 2. Primitive Hashing and Scalar Equality
* **`ByteArray.hash` (`lean_byte_array_hash`)**
  * **Type:** `(@& ByteArray) → UInt64`
  * **What it does:** A specialized, fast C runtime hashing primitive over raw contiguous memory bytes. `Array` does not have a single dedicated C runtime hashing primitive (`lean_array_hash`); instead, array hashing is done generically via the `Hashable` typeclass iterating over elements.
* **`ByteArray.beq` (`lean_sarray_dec_eq`)**
  * Generic `Array` equality (`Array.isEqv` / `==`) iterates element-by-element calling `BEq.beq`. Because `ByteArray` is a scalar array (`sarray`), it uses `lean_sarray_dec_eq` (an optimized `memcmp` over raw memory).

---

### 3. UTF-8 & String Interoperability
Because Lean strings are UTF-8 encoded byte sequences internally, `ByteArray` has dedicated APIs for bridging to and from `String`:
* **`ByteArray.validateUTF8` (`lean_string_validate_utf8`)**
  * **Type:** `(@& ByteArray) → Bool`
  * Validates whether the byte sequence contains valid UTF-8 data.
* **`String.ofByteArray` (`lean_string_from_utf8_unchecked`)**
  * **Type:** `(toByteArray : ByteArray) → (isValidUTF8 : toByteArray.IsValidUTF8) → String`
  * Zero-cost / fast construction of a `String` from verified raw bytes.
* **`String.toByteArray` / `String.toUTF8` (`lean_string_to_utf8`)**
  * Converts a `String` directly to its raw `ByteArray` representation.
* **`String.decodeChar` (`lean_string_utf8_get_fast`) / `ByteArray.utf8DecodeChar?`**
  * Decodes Unicode `Char` codepoints directly from byte offsets inside byte arrays.

---

### 4. Representation Conversion
* **`ByteArray.mk` (`lean_byte_array_mk`)** and **`ByteArray.data` (`lean_byte_array_data`)**
  * Converts between unboxed scalar bytes (`ByteArray`) and boxed object pointers (`Array UInt8`).

---

### Summary
| Feature | `ByteArray` | `Array` |
| :--- | :--- | :--- |
| **Slice Copying** | `copySlice` (C-level `memcpy`) | None (only `extract`) |
| **Raw Buffer Hash** | `lean_byte_array_hash` (C primitive) | Generic `Hashable` loop |
| **Raw Buffer Equality**| `lean_sarray_dec_eq` (`memcmp`) | Generic element-wise `BEq` |
| **UTF-8 Validation & String Conversion** | `validateUTF8`, `String.ofByteArray`, `String.toUTF8` | None |
