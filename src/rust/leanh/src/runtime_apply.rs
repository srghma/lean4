use core::ffi::c_void;

use crate::datatypes::{LeanClosureObject, LeanObject};
use crate::in_emit_rust::{
    lean_alloc_closure, lean_dec, lean_dec_ref, lean_inc, lean_is_exclusive,
};
use crate::not_in_emit_rust::lean_is_scalar_bool;
use crate::runtime_object_rc::lean_free_object;

#[inline]
fn closure_fun(f: *mut LeanObject) -> *mut core::ffi::c_void {
    let clo = f as *mut LeanClosureObject<0>;
    unsafe { (*clo).m_fun }
}

#[inline]
fn closure_arity(f: *mut LeanObject) -> u32 {
    let clo = f as *mut LeanClosureObject<0>;
    unsafe { (*clo).m_arity as u32 }
}

#[inline]
fn closure_num_fixed(f: *mut LeanObject) -> u32 {
    let clo = f as *mut LeanClosureObject<0>;
    unsafe { (*clo).m_num_fixed as u32 }
}

#[inline]
fn closure_arg_cptr(f: *mut LeanObject) -> *mut *mut LeanObject {
    let clo = f as *mut LeanClosureObject<0>;
    unsafe { (*clo).m_objs.as_mut_ptr() }
}

#[inline]
fn fx(f: *mut LeanObject, i: u32) -> *mut LeanObject {
    let p = closure_arg_cptr(f);
    unsafe { *p.add(i as usize) }
}

type CurryFn1 = unsafe fn(*mut LeanObject) -> *mut LeanObject;
type CurryFn2 = unsafe fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject;
type CurryFn3 = unsafe fn(*mut LeanObject, *mut LeanObject, *mut LeanObject) -> *mut LeanObject;
type CurryFn4 = unsafe fn(
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
) -> *mut LeanObject;
type CurryFn5 = unsafe fn(
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
) -> *mut LeanObject;
type CurryFn6 = unsafe fn(
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
) -> *mut LeanObject;
type CurryFn7 = unsafe fn(
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
) -> *mut LeanObject;
type CurryFn8 = unsafe fn(
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
) -> *mut LeanObject;
type CurryFn9 = unsafe fn(
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
    *mut LeanObject,
) -> *mut LeanObject;
type CurryFn10 = unsafe fn(
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
) -> *mut LeanObject;
type CurryFn11 = unsafe fn(
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
) -> *mut LeanObject;
type CurryFn12 = unsafe fn(
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
) -> *mut LeanObject;
type CurryFn13 = unsafe fn(
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
) -> *mut LeanObject;
type CurryFn14 = unsafe fn(
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
) -> *mut LeanObject;
type CurryFn15 = unsafe fn(
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
) -> *mut LeanObject;
type CurryFn16 = unsafe fn(
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
) -> *mut LeanObject;

unsafe fn fix_args(f: *mut LeanObject, n: u32, as_ptr: *const *mut LeanObject) -> *mut LeanObject {
    let arity = closure_arity(f);
    let fixed = closure_num_fixed(f);
    let new_fixed = fixed + n;
    debug_assert!(new_fixed < arity);

    let r = unsafe { lean_alloc_closure(closure_fun(f), arity, new_fixed) };
    let source = closure_arg_cptr(f);
    let target = closure_arg_cptr(r);

    if unsafe { lean_is_exclusive(f) } {
        unsafe { core::ptr::copy(source, target, fixed as usize) };
        unsafe { lean_free_object(f) };
    } else {
        for i in 0..fixed as usize {
            let v = unsafe { *source.add(i) };
            lean_inc(v);
            unsafe { *target.add(i) = v };
        }
        unsafe { lean_dec_ref(f) };
    }

    for i in 0..n as usize {
        unsafe { *target.add(fixed as usize + i) = *as_ptr.add(i) };
    }
    r
}

fn curry(fun: *mut c_void, n: u32, as_ptr: *mut *mut LeanObject) -> *mut LeanObject {
    macro_rules! call {
        ($fn_ty:ty, $($idx:expr),*) => {{
            let f: $fn_ty = unsafe { core::mem::transmute(fun) };
            unsafe { f($(*as_ptr.add($idx),)*) }
        }};
    }
    match n {
        0 => unsafe { core::hint::unreachable_unchecked() },
        1 => call!(CurryFn1, 0),
        2 => call!(CurryFn2, 0, 1),
        3 => call!(CurryFn3, 0, 1, 2),
        4 => call!(CurryFn4, 0, 1, 2, 3),
        5 => call!(CurryFn5, 0, 1, 2, 3, 4),
        6 => call!(CurryFn6, 0, 1, 2, 3, 4, 5),
        7 => call!(CurryFn7, 0, 1, 2, 3, 4, 5, 6),
        8 => call!(CurryFn8, 0, 1, 2, 3, 4, 5, 6, 7),
        9 => call!(CurryFn9, 0, 1, 2, 3, 4, 5, 6, 7, 8),
        10 => call!(CurryFn10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9),
        11 => call!(CurryFn11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10),
        12 => call!(CurryFn12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11),
        13 => call!(CurryFn13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12),
        14 => call!(CurryFn14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13),
        15 => call!(CurryFn15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14),
        16 => call!(
            CurryFn16, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
        ),
        _ => {
            let f: unsafe fn(*mut *mut LeanObject) -> *mut LeanObject =
                unsafe { core::mem::transmute(fun) };
            unsafe { f(as_ptr) }
        }
    }
}

unsafe fn call_exact(f: *mut LeanObject, new_args: &[*mut LeanObject]) -> *mut LeanObject {
    let arity = closure_arity(f);
    let fixed = closure_num_fixed(f);
    let mut args = vec![core::ptr::null_mut::<LeanObject>(); arity as usize];
    if unsafe { lean_is_exclusive(f) } {
        for (i, slot) in args.iter_mut().enumerate().take(fixed as usize) {
            *slot = fx(f, i as u32);
        }
        for (slot, &a) in args.iter_mut().skip(fixed as usize).zip(new_args.iter()) {
            *slot = a;
        }
        let r = curry(closure_fun(f), arity, args.as_mut_ptr());
        unsafe { lean_free_object(f) };
        r
    } else {
        for (i, slot) in args.iter_mut().enumerate().take(fixed as usize) {
            let v = fx(f, i as u32);
            lean_inc(v);
            *slot = v;
        }
        for (slot, &a) in args.iter_mut().skip(fixed as usize).zip(new_args.iter()) {
            *slot = a;
        }
        let r = curry(closure_fun(f), arity, args.as_mut_ptr());
        unsafe { lean_dec_ref(f) };
        r
    }
}

unsafe fn apply_generic(
    f: *mut LeanObject,
    n: u32,
    as_ptr: *mut *mut LeanObject,
) -> *mut LeanObject {
    if lean_is_scalar_bool(f) {
        for i in 0..n as usize {
            unsafe { lean_dec(as_ptr.add(i).read()) };
        }
        return f;
    }

    let arity = closure_arity(f);
    let fixed = closure_num_fixed(f);
    let new_args = unsafe { core::slice::from_raw_parts(as_ptr, n as usize) };

    if arity == fixed + n {
        unsafe { call_exact(f, new_args) }
    } else if arity < fixed + n {
        let take = (arity - fixed) as usize;
        let mut args = vec![core::ptr::null_mut::<LeanObject>(); arity as usize];
        for (i, slot) in args.iter_mut().enumerate().take(fixed as usize) {
            let v = fx(f, i as u32);
            lean_inc(v);
            *slot = v;
        }
        for (slot, &a) in args.iter_mut().skip(fixed as usize).zip(new_args.iter()) {
            *slot = a;
        }
        let new_f = curry(closure_fun(f), arity, args.as_mut_ptr());
        unsafe { lean_dec_ref(f) };
        let remain = n - (arity - fixed);
        unsafe { lean_apply_n(new_f, remain, as_ptr.add(take)) }
    } else {
        unsafe { fix_args(f, n, as_ptr) }
    }
}

macro_rules! export_apply {
    ($name:ident, $n:expr, $($arg:ident),+) => {
        #[allow(clippy::too_many_arguments)]
        pub unsafe fn $name(f: *mut LeanObject, $($arg: *mut LeanObject),+) -> *mut LeanObject {
            let mut args = [$($arg),+];
            unsafe { apply_generic(f, $n, args.as_mut_ptr()) }
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
pub unsafe fn lean_apply_m(
    f: *mut LeanObject,
    n: u32,
    as_ptr: *mut *mut LeanObject,
) -> *mut LeanObject {
    debug_assert!(n > 16);
    unsafe { apply_generic(f, n, as_ptr) }
}

unsafe fn lean_apply_n(
    f: *mut LeanObject,
    n: u32,
    as_ptr: *mut *mut LeanObject,
) -> *mut LeanObject {
    unsafe {
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
}
