analyze cpp code in origin-master-src and EmitC

suppose I have lean program

def foo : String := "foo"

def main(arg
  let foobar = foo + arg[0]
  println foobar

so foo should be written like how in cpp?

const foo = ...??

and it should be in .rodata, right?

and then main func will copy from rodata to heap and concat, right?

show me code

--------------------

## How `def foo : String := "foo"` compiles to C

### 1. The string lives in `.rodata` as a `static const` struct

```c
// The string object itself — in .rodata.  rc=0 → persistent/immortal.
// m_data[] is a flexible array member; GCC/Clang let you initialize it with a
// string literal in a compound initializer (not standard C, but supported extension).
// The string bytes sit INLINE inside the struct, no separate heap allocation.
static const lean_string_object l_foo___closed__0_value = {
    .m_header = {
        .m_rc    = 0,    // ← rc=0 = PERSISTENT. Not 1, not -1. Zero means immortal.
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag   = 249   // LeanString tag
    },
    .m_size     = 4,     // byte length including '\0' → "foo\0" = 4
    .m_capacity = 4,
    .m_length   = 3,     // UTF-8 char count
    .m_data     = "foo"  // ← inline in .rodata, not on heap
};

// Pointer to it — also .rodata
static const lean_object* l_foo___closed__0 =
    (const lean_object*)&l_foo___closed__0_value;

// Exported top-level binding
LEAN_EXPORT const lean_object* l_foo =
    (const lean_object*)&l_foo___closed__0_value;
```

The `lean_string_object` struct:
```c
typedef struct {
    lean_object_header  m_header;  // rc, tag, etc.
    size_t              m_size;    // byte length including '\0'
    size_t              m_capacity;
    size_t              m_length;  // UTF-8 length
    char                m_data[];  // flexible array — bytes inline after header
} lean_string_object;
```

`"foo"` bytes live at the end of the struct in `.rodata`. No heap pointer.

---

### 2. What `lean_inc_ref` / `lean_dec_ref` do to `rc=0`

```c
// lean_inc_ref — from lean.h:535-570
static inline void lean_inc_ref_n(lean_object * o, size_t n) { // * in arg adds typesafety: if I call this func with `l_foo___closed__0_value` it will `error: incompatible type passing 'lean_string_object' to parameter of type 'lean_object *'`
    if (LEAN_LIKELY(lean_is_st(o))) {   // rc > 0 → ST, non-atomic ++
        o->m_rc += n;
    // NOTE: o->m_rc is exactly the same as (*o).m_rc. * as operator dereferences
    } else if (o->m_rc != 0) {          // rc < 0 → MT, atomic --
        atomic_fetch_sub(lean_get_rc_mt_addr(o), n, ...);
    }
    // rc == 0 → falls through, does NOTHING
}

// lean_dec_ref — from lean.h:574-580
static inline void lean_dec_ref(lean_object * o) {
    if (LEAN_LIKELY(o->m_rc > 1)) {    // ST shared: just decrement
        o->m_rc--;
    } else if (o->m_rc != 0) {         // rc==1 (free it) or MT (atomic dec)
        lean_dec_ref_cold(o);
    }
    // rc == 0 → falls through, does NOTHING
}
```

Both are **no-ops** for `foo`. No atomic, no branch taken.


<details>

```cpp
// The Object (a struct)
static const lean_string_object l_foo_value = { ... };

// The Function (expects a pointer)
void lean_inc_ref(lean_object * o);

// Scenario A: Correct
// You might notice something strange. foo is a lean_string_object, but the function takes a lean_object *. Why does that work?
// Lean uses a clever trick called Header Compatibility
lean_inc_ref((lean_object*)&l_foo_value); // Passing the address - OK

// Scenario B: Incorrect
lean_inc_ref(l_foo_value); // ERROR!
```

```cpp
#include <iostream>

// 1. The "Base Class" (The Header)
struct lean_object {
    size_t m_rc;      // Ref count: 0 = immortal, 1 = exclusive, >1 = shared
    int m_tag;        // 249 for String, etc.
};

// 2. The "Derived Class" (The String)
struct lean_string_object {
    lean_object m_header; // Header MUST be first for the pointer trick to work
    int m_size;
    const char* m_data;
};

// 3. The Function (Expects a POINTER to the header)
void lean_inc_ref(lean_object* o) {
    std::cout << "Checking refcount at address: " << o << std::endl;

    if (o->m_rc == 0) {
        std::cout << "  RC is 0: This is a persistent object. Doing nothing.\n" << std::endl;
    } else {
        o->m_rc++;
        std::cout << "  RC incremented to: " << o->m_rc << "\n" << std::endl;
    }
}

// 4. Create the string in .rodata (static const)
static const lean_string_object l_foo_value = {
    {0, 249}, // m_rc = 0 (immortal), m_tag = 249 (String)
    4,        // size
    "foo"     // data
};

int main() {
    // --- SCENARIO A: The Correct Way (Passing the Address) ---
    // We take the address of our struct (&) and cast it to a generic object pointer
    std::cout << "Calling with pointer:" << std::endl;
    lean_inc_ref((lean_object*)&l_foo_value);

    // --- SCENARIO B: The Incorrect Way (Passing the Value) ---
    // UNCOMMENT the line below to see the compiler error:
    // lean_inc_ref(l_foo_value);

    /*
       Why Scenario B fails:
       Error: cannot convert 'lean_string_object' to 'lean_object*'

       Reason: A 'house' (the struct) cannot fit into an 'envelope' (the pointer).
       The function wants a 64-bit address, not 32 bytes of raw data.
    */

    // --- SCENARIO C: A Heap Object (rc > 0) ---
    std::cout << "Calling with a heap object (rc=1):" << std::endl;
    lean_object* heap_obj = new lean_object{1, 249};
    lean_inc_ref(heap_obj);

    delete heap_obj;
    return 0;
}
```

</details>

---

### 3. `lean_string_append(foo, arg0)` — from `object.cpp:2084`

```c
object * lean_string_append(object * s1,        // lean_obj_arg = takes ownership of s1
                             object * s2) {      // b_lean_obj_arg = borrows s2
    size_t sz1 = lean_string_size(s1);           // 4 ("foo\0")
    size_t sz2 = lean_string_size(s2);           // len(arg0)+1
    // ...
    // lean_is_exclusive checks rc==1 (it is single threaded and used only once)
    if (!lean_is_exclusive(s1)) {
        // if used in some other func too
        //   foo has rc=0 → → NOT exclusive → takes this branch
        r = lean_alloc_string(new_sz, mk_capacity(new_sz), new_len); // XXX: lean_alloc_object will call mimalloc to allocate in heap, mimalloc uses linked list + binary trees to not allocate always. mmap uses -1 to allow virtual page with zeros but can with file content
        //   ^ malloc on heap, sets r->m_rc = 1 (new ST object)
        std::memcpy(w_string_cstr(r), lean_string_cstr(s1), sz1 - 1);
        //   ^ XXX: copies "foo" bytes from .rodata into the new heap allocation
        dec_ref(s1);
        //   ^ lean_dec_ref(foo): rc==0 → no-op
    } else {
        // exclusive and Single Threaded (rc==1): mutate s1 in place, no alloc
        r = string_ensure_capacity(s1, sz2-1);
    }
    memcpy(w_string_cstr(r) + sz1 - 1, lean_string_cstr(s2), sz2 - 1);
    // ^ appends arg0 bytes after "foo"
    lean_to_string(r)->m_size   = new_sz;
    lean_to_string(r)->m_length = new_len;
    w_string_cstr(r)[new_sz - 1] = 0;
    return r;   // new heap object, rc=1 (ST exclusive)
}
```

---

### 4. Generated code for `main`

```c
// "foo" string — in .rodata, rc=0, no refcount ever
static const lean_string_object l_foo___closed__0_value = { ..., .m_data = "foo" };
static const lean_object* l_foo___closed__0 = (const lean_object*)&l_foo___closed__0_value;

LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_) {
    lean_object* v_foo_;
    lean_object* v_arg0_;
    lean_object* v_foobar_;

    // Load foo — cast from .rodata pointer, no inc_ref needed (rc=0 = no-op)
    v_foo_ = ((lean_object*)(l_foo___closed__0));

    // Get arg[0] — some inc_ref from args array, borrowed here
    v_arg0_ = lean_array_get(v_args_, lean_box(0));

    // String append:
    //   s1 = v_foo_ (passed as owned; lean_inc_ref was no-op, lean_dec_ref inside is no-op)
    //   s2 = v_arg0_ (borrowed)
    // Result: NEW heap allocation, rc=1, contains "foo" + arg[0]
    v_foobar_ = lean_string_append(v_foo_, v_arg0_);

    // v_foobar_ is now an ST exclusive heap object (rc=1)
    // println will borrow it, then dec_ref → frees it
    return lean_io_println(v_foobar_);
}
```

---

### The complete memory flow

```
.rodata:
  l_foo___closed__0_value  { rc=0, "foo\0" }  ← never touched by GC
       ↓
lean_string_append() sees rc=0 → NOT exclusive
       ↓
malloc(sizeof(lean_string_object) + len("foo"+arg))  ← heap
  memcpy("foo" from .rodata)
  memcpy(arg[0] bytes)
  set rc=1   ← new ST exclusive heap object
       ↓
println borrows foobar, then dec_ref → rc goes 1→0 → lean_dec_ref_cold → free()
```

**The `.rodata` string is never modified, never freed, never refcounted. The exclusive fast-path in `lean_string_append` only fires when `s1` is a fresh heap string with `rc==1` — never for a persistent `.rodata` constant.**


------

```asm
section .rodata

; --- The lean_string_object for "foo" ---
l_foo___closed__0_value:
    dq 0                 ; m_rc (8 bytes). 0 = Persistent
    dw 0                 ; m_cs_sz (2 bytes)
    db 0                 ; m_other (1 byte)
    db 249               ; m_tag (1 byte) - 249 is Lean's String Tag
    dq 4                 ; m_size (8 bytes) - "foo\0" is 4 bytes
    dq 4                 ; m_capacity (8 bytes)
    dq 3                 ; m_length (8 bytes) - 3 UTF-8 chars
    db "foo", 0          ; m_data (4 bytes) - The actual bytes. Quadword (8 bytes / 64 bits). This is used for Pointers and size_t (unsigned integer data). 0 is Null Terminator. Define bytes = Lay these bytes out one after another, exactly as they are.

; --- The Pointer to that object ---
l_foo___closed__0:
    dq l_foo___closed__0_value  ; This is the 8-byte address of the object above

; -----------------------------------------------------
section .text
global _lean_main
extern lean_array_get
extern lean_string_append
extern lean_io_println
extern lean_box

_lean_main:
    push rbp            ; Setup stack frame
    mov rbp, rsp
    push rbx            ; Save registers we will use
    mov rbx, rdi        ; rbx = v_args (save the pointer to args)

    ; 1. Get arg[0] from the array
    ; lean_array_get(v_args, lean_box(0))
    mov rdi, rbx        ; Arg 1: the array
    mov rsi, 1          ; Arg 2: lean_box(0) is represented as 1 in Lean's small-integer tagging
    call lean_array_get ; Result (arg0) is now in %rax
    mov r12, rax        ; r12 = v_arg0

    ; 2. Load "foo" pointer
    ; v_foo = l_foo___closed__0
    mov rdi, [rel l_foo___closed__0] ; Get the address of the .rodata string.
    ; BUT COULD ALSO USE INSTEAD `lea rdi, [rel l_foo___closed__0_value]`
    ; Riscv doesnt have mov/lea (only as pseudo-instructions have). RISC-V may do a lot of "little populate 64bit Program Counter -> shift -> repeat" to form 64-bit jump addresses


    ; 3. Call lean_string_append(v_foo, v_arg0)
    ; Note: lean_string_append takes ownership of rdi (foo)
    mov rsi, r12        ; Arg 2: v_arg0 (borrowed)
    call lean_string_append
    ; The result (foobar) is now in %rax (a new heap address)

    ; 4. Call lean_io_println(v_foobar)
    mov rdi, rax        ; Move the new heap string into the first argument
    call lean_io_println

    ; Cleanup and return
    pop rbx
    pop rbp
    ret
```
