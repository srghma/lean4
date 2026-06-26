/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

// Port of src/runtime/apply.cpp.

pub(crate) mod runtime_apply_impl {
    use super::*;

    const LEAN_CLOSURE_TAG: u8 = 245;

    extern "C" {
        fn lean_free_object(obj: *mut LeanObject);
    }

    #[inline]
    unsafe fn closure_fun(f: *mut LeanObject) -> *mut c_void {
        (*(f as *mut LeanClosureObject)).fun
    }

    #[inline]
    unsafe fn closure_arity(f: *mut LeanObject) -> u32 {
        (*(f as *mut LeanClosureObject)).arity as u32
    }

    #[inline]
    unsafe fn closure_num_fixed(f: *mut LeanObject) -> u32 {
        (*(f as *mut LeanClosureObject)).num_fixed as u32
    }

    #[inline]
    unsafe fn closure_arg_cptr(f: *mut LeanObject) -> *mut *mut LeanObject {
        (*(f as *mut LeanClosureObject)).data.as_mut_ptr()
    }

    #[inline]
    unsafe fn fx(f: *mut LeanObject, i: u32) -> *mut LeanObject {
        *closure_arg_cptr(f).add(i as usize)
    }

    #[inline]
    unsafe fn lean_is_exclusive(obj: *mut LeanObject) -> bool {
        (*obj).rc == 1
    }

    #[inline]
    pub(crate) unsafe fn lean_alloc_closure(
        fun: *mut c_void,
        arity: u32,
        num_fixed: u32,
    ) -> *mut LeanObject {
        debug_assert!(arity > 0);
        debug_assert!(num_fixed < arity);
        let byte_size = core::mem::size_of::<LeanClosureObject>()
            .checked_add(
                core::mem::size_of::<*mut LeanObject>()
                    .checked_mul(num_fixed as usize)
                    .expect("closure allocation overflow"),
            )
            .expect("closure allocation overflow");
        let obj = lean_alloc_object(byte_size) as *mut LeanClosureObject;
        (*obj).header.rc = 1;
        (*obj).header.cs_size = 0;
        (*obj).header.other = 0;
        (*obj).header.tag = LEAN_CLOSURE_TAG;
        (*obj).fun = fun;
        (*obj).arity = arity as u16;
        (*obj).num_fixed = num_fixed as u16;
        obj as *mut LeanObject
    }

    unsafe fn fix_args(
        f: *mut LeanObject,
        n: u32,
        as_ptr: *const *mut LeanObject,
    ) -> *mut LeanObject {
        let arity = closure_arity(f);
        let fixed = closure_num_fixed(f);
        let new_fixed = fixed + n;
        debug_assert!(new_fixed < arity);

        let r = lean_alloc_closure(closure_fun(f), arity, new_fixed);
        let source = closure_arg_cptr(f);
        let target = closure_arg_cptr(r);

        if lean_is_exclusive(f) {
            for i in 0..fixed as usize {
                target.add(i).write(source.add(i).read());
            }
            lean_free_object(f);
        } else {
            for i in 0..fixed as usize {
                let v = source.add(i).read();
                lean_inc(v);
                target.add(i).write(v);
            }
            lean_dec_ref(f);
        }

        for i in 0..n as usize {
            target.add(fixed as usize + i).write(as_ptr.add(i).read());
        }
        r
    }

    unsafe fn curry_raw(fun: *mut c_void, n: u32, as_ptr: *mut *mut LeanObject) -> *mut LeanObject {
        macro_rules! call {
            ($fn_ty:ty, $($idx:expr),*) => {{
                let f: $fn_ty = core::mem::transmute(fun);
                f($(*as_ptr.add($idx),)*)
            }};
        }
        match n {
            0 => core::hint::unreachable_unchecked(),
            1 => call!(unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject, 0),
            2 => call!(
                unsafe extern "C" fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject,
                0,
                1
            ),
            3 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2
            ),
            4 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3
            ),
            5 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4
            ),
            6 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5
            ),
            7 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6
            ),
            8 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7
            ),
            9 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8
            ),
            10 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8,
                9
            ),
            11 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8,
                9,
                10
            ),
            12 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8,
                9,
                10,
                11
            ),
            13 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8,
                9,
                10,
                11,
                12
            ),
            14 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8,
                9,
                10,
                11,
                12,
                13
            ),
            15 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8,
                9,
                10,
                11,
                12,
                13,
                14
            ),
            16 => call!(
                unsafe extern "C" fn(
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                    *mut LeanObject,
                ) -> *mut LeanObject,
                0,
                1,
                2,
                3,
                4,
                5,
                6,
                7,
                8,
                9,
                10,
                11,
                12,
                13,
                14,
                15
            ),
            _ => {
                let f: unsafe extern "C" fn(*mut *mut LeanObject) -> *mut LeanObject =
                    core::mem::transmute(fun);
                f(as_ptr)
            }
        }
    }

    unsafe fn call_exact(f: *mut LeanObject, new_args: &[*mut LeanObject]) -> *mut LeanObject {
        let arity = closure_arity(f);
        let fixed = closure_num_fixed(f);
        let mut args = vec![core::ptr::null_mut::<LeanObject>(); arity as usize];
        if lean_is_exclusive(f) {
            for i in 0..fixed as usize {
                args[i] = fx(f, i as u32);
            }
            for (i, &a) in new_args.iter().enumerate() {
                args[fixed as usize + i] = a;
            }
            let r = curry_raw(closure_fun(f), arity, args.as_mut_ptr());
            lean_free_object(f);
            r
        } else {
            for i in 0..fixed as usize {
                let v = fx(f, i as u32);
                lean_inc(v);
                args[i] = v;
            }
            for (i, &a) in new_args.iter().enumerate() {
                args[fixed as usize + i] = a;
            }
            let r = curry_raw(closure_fun(f), arity, args.as_mut_ptr());
            lean_dec_ref(f);
            r
        }
    }

    unsafe fn apply_generic(
        f: *mut LeanObject,
        n: u32,
        as_ptr: *mut *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(f) {
            for i in 0..n as usize {
                lean_dec(as_ptr.add(i).read());
            }
            return f;
        }

        let arity = closure_arity(f);
        let fixed = closure_num_fixed(f);
        let new_args = core::slice::from_raw_parts(as_ptr, n as usize);

        if arity == fixed + n {
            call_exact(f, new_args)
        } else if arity < fixed + n {
            let take = (arity - fixed) as usize;
            let mut args = vec![core::ptr::null_mut::<LeanObject>(); arity as usize];
            for i in 0..fixed as usize {
                let v = fx(f, i as u32);
                lean_inc(v);
                args[i] = v;
            }
            for i in 0..take {
                args[fixed as usize + i] = new_args[i];
            }
            let new_f = curry_raw(closure_fun(f), arity, args.as_mut_ptr());
            lean_dec_ref(f);
            let remain = n - (arity - fixed);
            lean_apply_n(new_f, remain, as_ptr.add(take))
        } else {
            fix_args(f, n, as_ptr)
        }
    }

    macro_rules! export_apply {
        ($name:ident, $n:expr, $($arg:ident),+) => {
            #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
            pub unsafe extern "C" fn $name(f: *mut LeanObject, $($arg: *mut LeanObject),+) -> *mut LeanObject {
                let mut args = [$($arg),+];
                apply_generic(f, $n, args.as_mut_ptr())
            }
        };
    }

    export_apply!(lean_apply_1, 1, a1);
    export_apply!(lean_apply_2, 2, a1, a2);
    export_apply!(lean_apply_3, 3, a1, a2, a3);
    export_apply!(lean_apply_4, 4, a1, a2, a3, a4);
    export_apply!(lean_apply_5, 5, a1, a2, a3, a4, a5);
    export_apply!(lean_apply_6, 6, a1, a2, a3, a4, a5, a6);
    export_apply!(lean_apply_7, 7, a1, a2, a3, a4, a5, a6, a7);
    export_apply!(lean_apply_8, 8, a1, a2, a3, a4, a5, a6, a7, a8);
    export_apply!(lean_apply_9, 9, a1, a2, a3, a4, a5, a6, a7, a8, a9);
    export_apply!(lean_apply_10, 10, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
    export_apply!(
        lean_apply_11,
        11,
        a1,
        a2,
        a3,
        a4,
        a5,
        a6,
        a7,
        a8,
        a9,
        a10,
        a11
    );
    export_apply!(
        lean_apply_12,
        12,
        a1,
        a2,
        a3,
        a4,
        a5,
        a6,
        a7,
        a8,
        a9,
        a10,
        a11,
        a12
    );
    export_apply!(
        lean_apply_13,
        13,
        a1,
        a2,
        a3,
        a4,
        a5,
        a6,
        a7,
        a8,
        a9,
        a10,
        a11,
        a12,
        a13
    );
    export_apply!(
        lean_apply_14,
        14,
        a1,
        a2,
        a3,
        a4,
        a5,
        a6,
        a7,
        a8,
        a9,
        a10,
        a11,
        a12,
        a13,
        a14
    );
    export_apply!(
        lean_apply_15,
        15,
        a1,
        a2,
        a3,
        a4,
        a5,
        a6,
        a7,
        a8,
        a9,
        a10,
        a11,
        a12,
        a13,
        a14,
        a15
    );
    export_apply!(
        lean_apply_16,
        16,
        a1,
        a2,
        a3,
        a4,
        a5,
        a6,
        a7,
        a8,
        a9,
        a10,
        a11,
        a12,
        a13,
        a14,
        a15,
        a16
    );

    #[inline]
    pub(crate) unsafe fn lean_apply_m(
        f: *mut LeanObject,
        n: u32,
        as_ptr: *mut *mut LeanObject,
    ) -> *mut LeanObject {
        debug_assert!(n > 16);
        apply_generic(f, n, as_ptr)
    }

    #[inline]
    pub(crate) unsafe fn lean_apply_n(
        f: *mut LeanObject,
        n: u32,
        as_ptr: *mut *mut LeanObject,
    ) -> *mut LeanObject {
        match n {
            0 => core::hint::unreachable_unchecked(),
            1 => lean_apply_1(f, *as_ptr.add(0)),
            2 => lean_apply_2(f, *as_ptr.add(0), *as_ptr.add(1)),
            3 => lean_apply_3(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2)),
            4 => lean_apply_4(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
            ),
            5 => lean_apply_5(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
            ),
            6 => lean_apply_6(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
            ),
            7 => lean_apply_7(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
            ),
            8 => lean_apply_8(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
            ),
            9 => lean_apply_9(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
                *as_ptr.add(8),
            ),
            10 => lean_apply_10(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
                *as_ptr.add(8),
                *as_ptr.add(9),
            ),
            11 => lean_apply_11(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
                *as_ptr.add(8),
                *as_ptr.add(9),
                *as_ptr.add(10),
            ),
            12 => lean_apply_12(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
                *as_ptr.add(8),
                *as_ptr.add(9),
                *as_ptr.add(10),
                *as_ptr.add(11),
            ),
            13 => lean_apply_13(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
                *as_ptr.add(8),
                *as_ptr.add(9),
                *as_ptr.add(10),
                *as_ptr.add(11),
                *as_ptr.add(12),
            ),
            14 => lean_apply_14(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
                *as_ptr.add(8),
                *as_ptr.add(9),
                *as_ptr.add(10),
                *as_ptr.add(11),
                *as_ptr.add(12),
                *as_ptr.add(13),
            ),
            15 => lean_apply_15(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
                *as_ptr.add(8),
                *as_ptr.add(9),
                *as_ptr.add(10),
                *as_ptr.add(11),
                *as_ptr.add(12),
                *as_ptr.add(13),
                *as_ptr.add(14),
            ),
            16 => lean_apply_16(
                f,
                *as_ptr.add(0),
                *as_ptr.add(1),
                *as_ptr.add(2),
                *as_ptr.add(3),
                *as_ptr.add(4),
                *as_ptr.add(5),
                *as_ptr.add(6),
                *as_ptr.add(7),
                *as_ptr.add(8),
                *as_ptr.add(9),
                *as_ptr.add(10),
                *as_ptr.add(11),
                *as_ptr.add(12),
                *as_ptr.add(13),
                *as_ptr.add(14),
                *as_ptr.add(15),
            ),
            _ => lean_apply_m(f, n, as_ptr),
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean5curryEPvjPP11lean_object"
    )]
    #[allow(dead_code)]
    pub unsafe extern "C" fn curry(
        fun: *mut c_void,
        n: u32,
        as_ptr: *mut *mut LeanObject,
    ) -> *mut LeanObject {
        curry_raw(fun, n, as_ptr)
    }
}

pub(crate) use runtime_apply_impl::{lean_alloc_closure, lean_apply_1, lean_apply_2};
