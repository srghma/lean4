/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of src/runtime/apply.cpp
// DO NOT EDIT manually — regenerate from apply.lean if arity changes.



// Closure layout helpers (mirror lean.h):
//   lean_closure_fun(f)       -> *mut c_void  (the function pointer)
//   lean_closure_arity(f)     -> u32
//   lean_closure_num_fixed(f) -> u32
//   lean_closure_arg_cptr(f)  -> *mut *mut LeanObject  (pointer to fixed args array)

unsafe fn closure_fun(f: *mut LeanObject) -> *mut c_void {
    (*(f as *mut LeanClosureObject)).m_fun
}

unsafe fn closure_arity(f: *mut LeanObject) -> u32 {
    (*(f as *mut LeanClosureObject)).m_arity as u32
}

unsafe fn closure_num_fixed(f: *mut LeanObject) -> u32 {
    (*(f as *mut LeanClosureObject)).m_num_fixed as u32
}

unsafe fn closure_arg_cptr(f: *mut LeanObject) -> *mut *mut LeanObject {
    let base = f as *mut u8;
    // fixed args start right after the LeanClosureObject header
    base.add(core::mem::size_of::<LeanClosureObject>()) as *mut *mut LeanObject
}

unsafe fn fx(f: *mut LeanObject, i: u32) -> *mut LeanObject {
    *closure_arg_cptr(f).add(i as usize)
}

// Allocate a new partially-applied closure, copying fixed args from `f`
// and appending `n` new args from `as_ptr`.
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
        // Transfer ownership: copy pointers without inc, then free the header only
        for i in 0..fixed as usize {
            target.add(i).write(source.add(i).read());
        }
        lean_free_object(f);
    } else {
        // Shared: inc each fixed arg, then dec the closure ref
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

// Call a function pointer with `n` args from `as_ptr` (n <= 16).
// For n > 16 the varargs ("fnn") convention is used.
unsafe fn curry_raw(fun: *mut c_void, n: u32, as_ptr: *mut *mut LeanObject) -> *mut LeanObject {
    macro_rules! call {
        ($fn_ty:ty, $($idx:expr),*) => {{
            let f: $fn_ty = core::mem::transmute(fun);
            f($(*as_ptr.add($idx),)*)
        }};
    }
    match n {
        1  => call!(unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject, 0),
        2  => call!(unsafe extern "C" fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject, 0,1),
        3  => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2),
        4  => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3),
        5  => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4),
        6  => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5),
        7  => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6),
        8  => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7),
        9  => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7,8),
        10 => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7,8,9),
        11 => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7,8,9,10),
        12 => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7,8,9,10,11),
        13 => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7,8,9,10,11,12),
        14 => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7,8,9,10,11,12,13),
        15 => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14),
        16 => call!(unsafe extern "C" fn(*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject,*mut LeanObject) -> *mut LeanObject, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15),
        _ => {
            // varargs ("fnn") convention: fn(*mut *mut LeanObject) -> *mut LeanObject
            let f: unsafe extern "C" fn(*mut *mut LeanObject) -> *mut LeanObject =
                core::mem::transmute(fun);
            f(as_ptr)
        }
    }
}

// Build the full args array [fixed..., new_args...] and call.
// Exclusive path: reuse pointers directly and free the closure header.
// Shared path: inc each fixed arg, then dec_ref the closure.
unsafe fn call_exact_exclusive(f: *mut LeanObject, new_args: &[*mut LeanObject]) -> *mut LeanObject {
    let arity = closure_arity(f);
    let fixed = closure_num_fixed(f);
    let mut args = vec![core::ptr::null_mut::<LeanObject>(); arity as usize];
    for i in 0..fixed as usize {
        args[i] = fx(f, i as u32);
    }
    for (i, &a) in new_args.iter().enumerate() {
        args[fixed as usize + i] = a;
    }
    let r = curry_raw(closure_fun(f), arity, args.as_mut_ptr());
    lean_free_object(f);
    r
}

unsafe fn call_exact_shared(f: *mut LeanObject, new_args: &[*mut LeanObject]) -> *mut LeanObject {
    let arity = closure_arity(f);
    let fixed = closure_num_fixed(f);
    let mut args = vec![core::ptr::null_mut::<LeanObject>(); arity as usize];
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

// The core generic apply: f applied to `n` new args in `as_ptr`.
// This is lean_apply_n generalized.
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
    let new_args: &[*mut LeanObject] =
        core::slice::from_raw_parts(as_ptr, n as usize);

    if arity == fixed + n {
        // Exact application
        if arity <= 16 && lean_is_exclusive(f) {
            call_exact_exclusive(f, new_args)
        } else {
            call_exact_shared(f, new_args)
        }
    } else if arity < fixed + n {
        // Over-application: call with exactly (arity - fixed) args, then apply remainder
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
        // Apply remaining args
        let remain = n - (arity - fixed);
        lean_apply_n(new_f, remain, as_ptr.add(take))
    } else {
        // Under-application: build a new partial closure
        fix_args(f, n, as_ptr)
    }
}

// ─── Public exported functions ───────────────────────────────────────────────

#[no_mangle]
pub unsafe extern "C" fn lean_apply_1(f: *mut LeanObject, a1: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1];
    apply_generic(f, 1, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_2(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2];
    apply_generic(f, 2, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_3(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3];
    apply_generic(f, 3, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_4(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4];
    apply_generic(f, 4, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_5(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5];
    apply_generic(f, 5, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_6(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6];
    apply_generic(f, 6, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_7(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7];
    apply_generic(f, 7, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_8(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8];
    apply_generic(f, 8, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_9(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject, a9: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8, a9];
    apply_generic(f, 9, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_10(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject, a9: *mut LeanObject, a10: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10];
    apply_generic(f, 10, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_11(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject, a9: *mut LeanObject, a10: *mut LeanObject, a11: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11];
    apply_generic(f, 11, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_12(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject, a9: *mut LeanObject, a10: *mut LeanObject, a11: *mut LeanObject, a12: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12];
    apply_generic(f, 12, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_13(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject, a9: *mut LeanObject, a10: *mut LeanObject, a11: *mut LeanObject, a12: *mut LeanObject, a13: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13];
    apply_generic(f, 13, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_14(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject, a9: *mut LeanObject, a10: *mut LeanObject, a11: *mut LeanObject, a12: *mut LeanObject, a13: *mut LeanObject, a14: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14];
    apply_generic(f, 14, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_15(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject, a9: *mut LeanObject, a10: *mut LeanObject, a11: *mut LeanObject, a12: *mut LeanObject, a13: *mut LeanObject, a14: *mut LeanObject, a15: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15];
    apply_generic(f, 15, args.as_mut_ptr())
}

#[no_mangle]
pub unsafe extern "C" fn lean_apply_16(f: *mut LeanObject, a1: *mut LeanObject, a2: *mut LeanObject, a3: *mut LeanObject, a4: *mut LeanObject, a5: *mut LeanObject, a6: *mut LeanObject, a7: *mut LeanObject, a8: *mut LeanObject, a9: *mut LeanObject, a10: *mut LeanObject, a11: *mut LeanObject, a12: *mut LeanObject, a13: *mut LeanObject, a14: *mut LeanObject, a15: *mut LeanObject, a16: *mut LeanObject) -> *mut LeanObject {
    let mut args = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16];
    apply_generic(f, 16, args.as_mut_ptr())
}

/// lean_apply_m: n > 16 args, passed via pointer array
#[no_mangle]
pub unsafe extern "C" fn lean_apply_m(
    f: *mut LeanObject,
    n: u32,
    as_ptr: *mut *mut LeanObject,
) -> *mut LeanObject {
    debug_assert!(n > 16);
    apply_generic(f, n, as_ptr)
}

/// lean_apply_n: dispatch by count, 1..=16 use typed functions, >16 uses lean_apply_m
#[no_mangle]
pub unsafe extern "C" fn lean_apply_n(
    f: *mut LeanObject,
    n: u32,
    as_ptr: *mut *mut LeanObject,
) -> *mut LeanObject {
    match n {
        0 => core::hint::unreachable_unchecked(),
        1 => lean_apply_1(f, *as_ptr.add(0)),
        2 => lean_apply_2(f, *as_ptr.add(0), *as_ptr.add(1)),
        3 => lean_apply_3(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2)),
        4 => lean_apply_4(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3)),
        5 => lean_apply_5(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4)),
        6 => lean_apply_6(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5)),
        7 => lean_apply_7(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6)),
        8 => lean_apply_8(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7)),
        9 => lean_apply_9(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7), *as_ptr.add(8)),
        10 => lean_apply_10(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7), *as_ptr.add(8), *as_ptr.add(9)),
        11 => lean_apply_11(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7), *as_ptr.add(8), *as_ptr.add(9), *as_ptr.add(10)),
        12 => lean_apply_12(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7), *as_ptr.add(8), *as_ptr.add(9), *as_ptr.add(10), *as_ptr.add(11)),
        13 => lean_apply_13(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7), *as_ptr.add(8), *as_ptr.add(9), *as_ptr.add(10), *as_ptr.add(11), *as_ptr.add(12)),
        14 => lean_apply_14(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7), *as_ptr.add(8), *as_ptr.add(9), *as_ptr.add(10), *as_ptr.add(11), *as_ptr.add(12), *as_ptr.add(13)),
        15 => lean_apply_15(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7), *as_ptr.add(8), *as_ptr.add(9), *as_ptr.add(10), *as_ptr.add(11), *as_ptr.add(12), *as_ptr.add(13), *as_ptr.add(14)),
        16 => lean_apply_16(f, *as_ptr.add(0), *as_ptr.add(1), *as_ptr.add(2), *as_ptr.add(3), *as_ptr.add(4), *as_ptr.add(5), *as_ptr.add(6), *as_ptr.add(7), *as_ptr.add(8), *as_ptr.add(9), *as_ptr.add(10), *as_ptr.add(11), *as_ptr.add(12), *as_ptr.add(13), *as_ptr.add(14), *as_ptr.add(15)),
        _ => lean_apply_m(f, n, as_ptr),
    }
}

/// lean_curry: called from C++ (apply.h), takes a raw function pointer + args
#[no_mangle]
pub unsafe extern "C" fn lean_runtime_curry(
    fun: *mut c_void,
    n: u32,
    as_ptr: *mut *mut LeanObject,
) -> *mut LeanObject {
    curry_raw(fun, n, as_ptr)
}

#[cfg(test)]
mod runtime_apply_tests {
    use super::*;

    unsafe extern "C" fn fnn_observe_first_arg_rc(args: *mut *mut LeanObject) -> *mut LeanObject {
        let first = *args;
        let rc = (*first).m_rc as usize;
        for i in 0..17 {
            lean_dec(*args.add(i));
        }
        lean_box(rc)
    }

    unsafe extern "C" fn fnn_sum_forty(args: *mut *mut LeanObject) -> *mut LeanObject {
        let mut sum = 0;
        for i in 0..40 {
            let arg = *args.add(i);
            sum += lean_unbox(arg);
        }
        lean_box(sum)
    }

    #[test]
    fn exact_application_above_sixteen_uses_shared_fixed_args() {
        unsafe {
            let captured = lean_alloc_ctor(0, 0, 0);
            let closure = lean_alloc_closure(
                fnn_observe_first_arg_rc as *mut c_void,
                17,
                10,
            );
            let fixed = closure_arg_cptr(closure);
            fixed.write(captured);
            for i in 1..10 {
                fixed.add(i).write(lean_box(i));
            }

            let result = lean_apply_7(
                closure,
                lean_box(10),
                lean_box(11),
                lean_box(12),
                lean_box(13),
                lean_box(14),
                lean_box(15),
                lean_box(16),
            );

            assert_eq!(lean_unbox(result), 2);
        }
    }

    #[test]
    fn exact_application_above_stack_buffer_size_uses_arity_sized_args() {
        unsafe {
            let closure = lean_alloc_closure(fnn_sum_forty as *mut c_void, 40, 37);
            let fixed = closure_arg_cptr(closure);
            for i in 0..37 {
                fixed.add(i).write(lean_box(i));
            }

            let result = lean_apply_3(closure, lean_box(37), lean_box(38), lean_box(39));

            assert_eq!(lean_unbox(result), (0..40).sum::<usize>());
        }
    }
}
