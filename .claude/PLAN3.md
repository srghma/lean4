lets finish implemening gen_init_ffi

e.g

==== FILE: src/rust/gen_init_ffi/src/ffi/common/lean_string_mk.rs ====
// Generated duplicate-function bucket
// source: Init/Prelude.rs:279-282
// exact-text variant: no

use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};

#[inline]
pub unsafe fn lean_string_mk(chars: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_string_mk(chars) }
}


leanh is now split on leanh_l1 leanh_l1_initializers and leanh_l2 (which probably will be removed and merged into runtime)

gen_init_ffi can import only leanh_l1 and leanh_l1_initializers

since this func is defined in src/rust/runtime/src/runtime_object_string.rs

we cut the insides from runtime, remove, and put inside of gen_init_ffi

we import lean_is_scalar and others what can

result is

```rs
// Generated duplicate-function bucket
// source: Init/Prelude.rs:279-282
// exact-text variant: no

use std::ffi::c_char;

use leanh_l1::{
    datatypes::{LeanObject, LeanScalarArray, LeanStringObject},
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_dec::lean_dec,
        lean_mk_string_unchecked::lean_mk_string_unchecked, lean_unbox_uint32::lean_unbox_uint32,
    },
};

use crate::Init::Prelude::lean_is_scalar;

#[inline]
pub unsafe fn lean_string_mk(chars: *mut LeanObject) -> *mut LeanObject {
    let mut buf: Vec<u8> = Vec::new();
    let mut o = chars;
    let mut len: usize = 0;
    while !lean_is_scalar(o) {
        let cp = lean_unbox_uint32(lean_ctor_get(o, 0));
        let start = buf.len();
        buf.resize(start + 4, 0);
        let consumed =
            lean_runtime_push_unicode_scalar(buf.as_mut_ptr().add(start) as *mut c_char, cp)
                as usize;
        buf.truncate(start + consumed);
        o = lean_ctor_get(o, 1);
        len += 1;
    }
    lean_dec(chars);
    lean_mk_string_unchecked(buf.as_ptr() as *const c_char, buf.len(), len)
}
```

with errors

At:     while !lean_is_scalar(o) {
  mismatched types
expected `bool`, found `u8`

At:             lean_runtime_push_unicode_scalar(buf.as_mut_ptr().add(start) as *mut c_char, cp)
  cannot find function `lean_runtime_push_unicode_scalar` in this scope
not found in this scope


yes, bool is expected (we want to be more rusty), even if rn in /home/srghma/projects/lean4/src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs

#[inline]
pub unsafe fn lean_is_scalar(obj: *mut LeanObject) -> u8 {
    leanh::lean_is_scalar(obj)
}


this func is in src/rust/leanh_l1/src/emitted/lean_is_scalar.rs

so we should change

#[inline]
pub unsafe fn lean_is_scalar(obj: *mut LeanObject) -> bool {
    leanh::lean_is_scalar(obj)
}


to

#[inline]
pub unsafe fn lean_is_scalar(obj: *mut LeanObject) -> bool {
    leanh_l1::emitted::lean_is_scalar::lean_is_scalar(obj)
}


but this is bad bc reexport is better (this func is needed in /home/srghma/projects/lean4/src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs bc for EmitRust)

so now its

pub use leanh_l1::emitted::lean_is_scalar::lean_is_scalar;

or should be pub use leanh_l1::emitted::lean_is_scalar::lean_is_scalar as lean_is_scalar;

so how about

At:             lean_runtime_push_unicode_scalar(buf.as_mut_ptr().add(start) as *mut c_char, cp)
  cannot find function `lean_runtime_push_unicode_scalar` in this scope
not found in this scope

it is in /home/srghma/projects/lean4/src/rust/runtime/src/base.rs

this time lets use ~/projects/lean4/srghmascripts/move_rust_fn_to_gen_init_ffi.ts lean_runtime_push_unicode_scalar (should be preffered bc I want to check original implementation in ~/projects/lean4-rust)

I do git add --all before and then this command

```sh
~/projects/lean4  ↱ rust-rewrite ✚  ~/projects/lean4/srghmascripts/move_rust_fn_to_gen_init_ffi.ts lean_runtime_push_unicode_scalar

Current tree bodies: 1
- src/rust/runtime/src/base.rs:1228-1273
Current tree decls: 0

Original tree: 1
- ../lean4-rust/src/rust/lean_runtime/src/lib.rs:2867-2916

Destination: src/rust/gen_init_ffi/src/priv
Distinct bodies: 2
- body #1: 1 occurrence(s)
  - ../lean4-rust/src/rust/lean_runtime/src/lib.rs:2867-2916
- body #2: 1 occurrence(s)
  - src/rust/runtime/src/base.rs:1228-1273

Wrote lean_runtime_push_unicode_scalar into src/rust/gen_init_ffi/src/priv/lean_runtime_push_unicode_scalar.rs and removed current-tree bodies/declarations outside src/rust/gen_init_ffi/src.
```

it have cut out original from lean4-rust and created new file

```rs
==== FILE: src/rust/gen_init_ffi/src/priv/lean_runtime_push_unicode_scalar.rs ====
use leanh_l1::datatypes::{
    LeanExternalObject, LeanObject, LeanScalarArray, LeanStringObject,
};
use std::ffi::c_void;

// appended by move_rust_fn_to_gen_init_ffi.ts from ../lean4-rust/src/rust/lean_runtime/src/lib.rs:2867-2916

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_push_unicode_scalar(
    dst: *mut c_char,
    code: c_uint,
) -> c_uint {
    const TAG_CONT: c_uint = 0b10000000;
    const TAG_TWO_B: c_uint = 0b11000000;
    const TAG_THREE_B: c_uint = 0b11100000;
    const TAG_FOUR_B: c_uint = 0b11110000;

    let bytes = if code < 0x80 {
        [code, 0, 0, 0]
    } else if code < 0x800 {
        [
            ((code >> 6) & 0x1F) | TAG_TWO_B,
            (code & 0x3F) | TAG_CONT,
            0,
            0,
        ]
    } else if code < 0x10000 {
        [
            ((code >> 12) & 0x0F) | TAG_THREE_B,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
            0,
        ]
    } else {
        [
            ((code >> 18) & 0x07) | TAG_FOUR_B,
            ((code >> 12) & 0x3F) | TAG_CONT,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
        ]
    };

    let len = if code < 0x80 {
        1
    } else if code < 0x800 {
        2
    } else if code < 0x10000 {
        3
    } else {
        4
    };
    for i in 0..len {
        *dst.add(i) = bytes[i] as c_char;
    }
    len as c_uint
}

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/base.rs:1228-1273

pub unsafe fn lean_runtime_push_unicode_scalar(dst: *mut c_char, code: c_uint) -> c_uint {
    const TAG_CONT: c_uint = 0b10000000;
    const TAG_TWO_B: c_uint = 0b11000000;
    const TAG_THREE_B: c_uint = 0b11100000;
    const TAG_FOUR_B: c_uint = 0b11110000;

    let bytes = if code < 0x80 {
        [code, 0, 0, 0]
    } else if code < 0x800 {
        [
            ((code >> 6) & 0x1F) | TAG_TWO_B,
            (code & 0x3F) | TAG_CONT,
            0,
            0,
        ]
    } else if code < 0x10000 {
        [
            ((code >> 12) & 0x0F) | TAG_THREE_B,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
            0,
        ]
    } else {
        [
            ((code >> 18) & 0x07) | TAG_FOUR_B,
            ((code >> 12) & 0x3F) | TAG_CONT,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
        ]
    };

    let len = if code < 0x80 {
        1
    } else if code < 0x800 {
        2
    } else if code < 0x10000 {
        3
    } else {
        4
    };
    for i in 0..len {
        *dst.add(i) = bytes[i] as c_char;
    }
    len as c_uint
}
```

seems like they are equal so I will change to


```rs
==== FILE: src/rust/gen_init_ffi/src/priv/lean_runtime_push_unicode_scalar.rs ====
use std::ffi::{c_char, c_uint};

pub unsafe fn lean_runtime_push_unicode_scalar(dst: *mut c_char, code: c_uint) -> c_uint {
    const TAG_CONT: c_uint = 0b10000000;
    const TAG_TWO_B: c_uint = 0b11000000;
    const TAG_THREE_B: c_uint = 0b11100000;
    const TAG_FOUR_B: c_uint = 0b11110000;

    let bytes = if code < 0x80 {
        [code, 0, 0, 0]
    } else if code < 0x800 {
        [
            ((code >> 6) & 0x1F) | TAG_TWO_B,
            (code & 0x3F) | TAG_CONT,
            0,
            0,
        ]
    } else if code < 0x10000 {
        [
            ((code >> 12) & 0x0F) | TAG_THREE_B,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
            0,
        ]
    } else {
        [
            ((code >> 18) & 0x07) | TAG_FOUR_B,
            ((code >> 12) & 0x3F) | TAG_CONT,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
        ]
    };

    let len = if code < 0x80 {
        1
    } else if code < 0x800 {
        2
    } else if code < 0x10000 {
        3
    } else {
        4
    };
    for i in 0..len {
        *dst.add(i) = bytes[i] as c_char;
    }
    len as c_uint
}
```


so resulting code is

```rs
// Generated duplicate-function bucket
// source: Init/Prelude.rs:279-282
// exact-text variant: no

use std::ffi::c_char;

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_dec::lean_dec,
        lean_mk_string_unchecked::lean_mk_string_unchecked, lean_unbox_uint32::lean_unbox_uint32,
    },
};

use crate::{
    Init::Prelude::lean_is_scalar,
    r#priv::lean_runtime_push_unicode_scalar::lean_runtime_push_unicode_scalar,
};

#[inline]
pub unsafe fn lean_string_mk(chars: *mut LeanObject) -> *mut LeanObject {
    let mut buf: Vec<u8> = Vec::new();
    let mut o = chars;
    let mut len: usize = 0;
    while !lean_is_scalar(o) {
        let cp = lean_unbox_uint32(lean_ctor_get(o, 0));
        let start = buf.len();
        buf.resize(start + 4, 0);
        let consumed =
            lean_runtime_push_unicode_scalar(buf.as_mut_ptr().add(start) as *mut c_char, cp)
                as usize;
        buf.truncate(start + consumed);
        o = lean_ctor_get(o, 1);
        len += 1;
    }
    lean_dec(chars);
    lean_mk_string_unchecked(buf.as_ptr() as *const c_char, buf.len(), len)
}
```

I do commit `gaa && gc -m 'lean_string_mk'`

and continue with next small function

Rules:
- we dont use u8 anymore where bool should be, we use bool
- we dont want leanh
- we dont want the glob imports `use xxx::*`
- prepend rtk to every shell command . e.g. `rtk cargo check`
- You should CUT OUT function implementation from runtime or leanh_l2 to gen_init_ffi AS IS!!! dont change. CUT OUT ONE BY ONE AS NEEDED.
- if You are trying to implement `src/rust/gen_init_ffi/src/ffi/common/**/*.rs` or `~/projects/lean4/src/rust/gen_init_ffi/src/ffi/Init/**/*.rs` then just CUT OUT. ELSE - use `~/projects/lean4/srghmascripts/move_rust_fn_to_gen_init_ffi.ts fn1 fn2` tool so that functions that are exported not from `src/rust/gen_init_ffi/src/ffi/common/**/*.rs` or `~/projects/lean4/src/rust/gen_init_ffi/src/ffi/Init/**/*.rs` live in `priv` dir


e.g. to implement next func `lean_string_to_utf8` I have called

```sh

 ~/projects/lean4/src/rust/gen_init_ffi  ↱ rust-rewrite ±  ~/projects/lean4/srghmascripts/move_rust_fn_to_gen_init_ffi.ts lean_alloc_sarray

Forbidden bodies in leanh_l1 / leanh_l1_initializers: 1
- src/rust/leanh_l1_initializers/src/priv/lean_alloc_sarray.rs:7-28
Forbidden decls in leanh_l1 / leanh_l1_initializers: 0
94 |   );
95 |   if (forbiddenBodies.length === 0 && forbiddenDecls.length === 0) return;
96 |
97 |   await printOccurrences("Forbidden bodies in leanh_l1 / leanh_l1_initializers", forbiddenBodies);
98 |   await printOccurrences("Forbidden decls in leanh_l1 / leanh_l1_initializers", forbiddenDecls);
99 |   throw new Error(
                 ^
error: refusing to move lean_alloc_sarray: it already exists in leanh_l1 or leanh_l1_initializers, so it must not be moved into gen_init_ffi
      at assertNotInForbiddenRoots (/home/srghma/projects/lean4/srghmascripts/move_rust_fn_to_gen_init_ffi.ts:99:13)
      at async main (/home/srghma/projects/lean4/srghmascripts/move_rust_fn_to_gen_init_ffi.ts:135:11)


$ ~/projects/lean4/srghmascripts/move_rust_fn_to_gen_init_ffi.ts lean_sarray_mut_cptr
Current tree bodies: 2
- src/rust/runtime/src/runtime_object_string.rs:24-28
- src/rust/runtime/src/runtime_object_array.rs:31-35
Current tree decls: 0

Original tree: 2
- ../lean4-rust/src/rust/lean_runtime/src/runtime_object_string.rs:35-39
- ../lean4-rust/src/rust/lean_runtime/src/runtime_object_array.rs:67-71

Destination: src/rust/gen_init_ffi/src/priv
Distinct bodies: 2
- body #1: 2 occurrence(s)
  - ../lean4-rust/src/rust/lean_runtime/src/runtime_object_string.rs:35-39
  - src/rust/runtime/src/runtime_object_string.rs:24-28
- body #2: 2 occurrence(s)
  - ../lean4-rust/src/rust/lean_runtime/src/runtime_object_array.rs:67-71
  - src/rust/runtime/src/runtime_object_array.rs:31-35

Wrote lean_sarray_mut_cptr into src/rust/gen_init_ffi/src/priv/lean_sarray_mut_cptr.rs and removed current-tree bodies/declarations outside src/rust/gen_init_ffi/src.
```


so I changed

```
pub(crate) unsafe fn lean_alloc_sarray(
    elem_size: c_uint,
    size: usize,
    capacity: usize,
) -> *mut LeanObject {
```

to pub

then imported

and very good that I used tool for `lean_sarray_mut_cptr` bc it identified that it was duplicated in `runtime`, so it cut out both occurences.

I got

```rs
use leanh_l1::datatypes::{
    LeanExternalObject, LeanObject, LeanScalarArray, LeanStringObject, usize,
};
use std::ffi::c_void;

// appended by move_rust_fn_to_gen_init_ffi.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_string.rs:35-39 and from src/rust/runtime/src/runtime_object_string.rs:24-28

#[inline]
pub(crate) unsafe fn lean_sarray_mut_cptr(o: *mut LeanObject) -> *mut u8 {
    (o as *mut u8).add(size_of::<LeanScalarArray>())
}

// appended by move_rust_fn_to_gen_init_ffi.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_array.rs:67-71 and from src/rust/runtime/src/runtime_object_array.rs:31-35

#[inline]
pub(crate) unsafe fn lean_sarray_mut_cptr(o: *mut LeanObject) -> *mut u8 {
    (o as *mut u8).add(core::mem::size_of::<LeanScalarArray>())
}
```

and fixed it to

```rs
use leanh_l1::datatypes::{LeanObject, LeanScalarArray};

#[inline]
pub(crate) unsafe fn lean_sarray_mut_cptr(o: *mut LeanObject) -> *mut u8 {
    (o as *mut u8).add(core::mem::size_of::<LeanScalarArray<0>>())
}
```


so I did the last ` ~/projects/lean4/src/rust/gen_init_ffi  ↱ rust-rewrite ±✚  rustfmt --edition=2024 --style-edition=2024 --unstable-features ./**/*.rs`

and comitted

Continue like me.

gen_init_ffi may have some functions already implemented. Especially in `src/rust/gen_init_ffi/src/ffi/Init`. These implementations are most probably dont match original implementation in `lean4-rust`, which is the truth and should be preffered to everything else.
