/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Rust kernel type-checker support.

This file starts the Result-based replacement for the C++ kernel exception
boundary.  The actual checker is ported into this module incrementally; all
public entry points return `Except Kernel.Exception _` values instead of
throwing C++ exceptions.
*/

#[cfg(feature = "export-runtime-ffi")]
#[allow(dead_code)]
mod kernel_type_checker_impl {
    use super::*;
    use core::ptr;
    use core::sync::atomic::{AtomicPtr, Ordering};

    type KernelResult<T> = Result<T, KernelError>;

    const EXCEPT_ERROR_TAG: usize = 0;
    const EXCEPT_OK_TAG: usize = 1;

    const KEX_UNKNOWN_CONSTANT_TAG: usize = 0;
    const KEX_ALREADY_DECLARED_TAG: usize = 1;
    const KEX_DECL_TYPE_MISMATCH_TAG: usize = 2;
    const KEX_DECL_HAS_MVARS_TAG: usize = 3;
    const KEX_DECL_HAS_FVARS_TAG: usize = 4;
    const KEX_FUN_EXPECTED_TAG: usize = 5;
    const KEX_TYPE_EXPECTED_TAG: usize = 6;
    const KEX_LET_TYPE_MISMATCH_TAG: usize = 7;
    const KEX_EXPR_TYPE_MISMATCH_TAG: usize = 8;
    const KEX_APP_TYPE_MISMATCH_TAG: usize = 9;
    const KEX_INVALID_PROJ_TAG: usize = 10;
    const KEX_THM_TYPE_IS_NOT_PROP_TAG: usize = 11;
    const KEX_OTHER_TAG: usize = 12;
    const KEX_DETERMINISTIC_TIMEOUT_SCALAR: usize = 13;
    const KEX_EXCESSIVE_MEMORY_SCALAR: usize = 14;
    const KEX_DEEP_RECURSION_SCALAR: usize = 15;
    const KEX_INTERRUPTED_SCALAR: usize = 16;

    const DECL_AXIOM_TAG: u8 = 0;
    const DECL_DEFINITION_TAG: u8 = 1;
    const DECL_THEOREM_TAG: u8 = 2;
    const DECL_OPAQUE_TAG: u8 = 3;
    const DECL_QUOT_TAG: u8 = 4;
    const DECL_MUTUAL_DEFINITION_TAG: u8 = 5;
    const DECL_INDUCTIVE_TAG: u8 = 6;

    const CONST_INFO_AXIOM_TAG: u8 = 0;
    const CONST_INFO_DEFINITION_TAG: u8 = 1;
    const CONST_INFO_THEOREM_TAG: u8 = 2;
    const CONST_INFO_OPAQUE_TAG: u8 = 3;
    const CONST_INFO_QUOT_TAG: u8 = 4;
    const CONST_INFO_INDUCTIVE_TAG: u8 = 5;
    const CONST_INFO_CONSTRUCTOR_TAG: u8 = 6;
    const CONST_INFO_RECURSOR_TAG: u8 = 7;

    const CONSTANT_VAL_NAME_FIELD: usize = 0;
    const CONSTANT_VAL_LEVEL_PARAMS_FIELD: usize = 1;
    const CONSTANT_VAL_TYPE_FIELD: usize = 2;

    const DECL_VAL_FIELD: usize = 0;
    const EXTENDS_CONSTANT_VAL_FIELD: usize = 0;
    const VALUE_VAL_VALUE_FIELD: usize = 1;
    const DEFINITION_VAL_HINTS_FIELD: usize = 2;
    const INDUCTIVE_DECL_LEVEL_PARAMS_FIELD: usize = 0;
    const INDUCTIVE_DECL_NUM_PARAMS_FIELD: usize = 1;
    const INDUCTIVE_DECL_TYPES_FIELD: usize = 2;
    const INDUCTIVE_TYPE_NAME_FIELD: usize = 0;
    const INDUCTIVE_TYPE_TYPE_FIELD: usize = 1;
    const INDUCTIVE_TYPE_CTORS_FIELD: usize = 2;

    const DEFINITION_SAFETY_UNSAFE: u8 = 0;
    const DEFINITION_SAFETY_SAFE: u8 = 1;
    const DEFINITION_SAFETY_PARTIAL: u8 = 2;

    static G_KERNEL_FRESH: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
    static G_DONT_CARE: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
    static G_BOOL_TRUE: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
    static G_EAGER_REDUCE: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());

    extern "C" {
        fn lean_cxx_kernel_is_def_eq(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
            b: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_kernel_whnf(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_kernel_check(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
        fn lean_name_mk_numeral(prefix: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_const(n: *mut LeanObject, us: *mut LeanObject) -> *mut LeanObject;

        fn lean_environment_find(env: *mut LeanObject, name: *mut LeanObject) -> *mut LeanObject;
        fn lean_environment_add(env: *mut LeanObject, cinfo: *mut LeanObject) -> *mut LeanObject;

        fn lean_mk_axiom_val(
            name: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            is_unsafe: u8,
        ) -> *mut LeanObject;
        fn lean_axiom_val_is_unsafe(v: *mut LeanObject) -> u8;
        fn lean_mk_definition_val(
            name: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            value: *mut LeanObject,
            hints: *mut LeanObject,
            safety: u8,
            all: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_definition_val_get_safety(v: *mut LeanObject) -> u8;
        fn lean_mk_theorem_val(
            name: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            value: *mut LeanObject,
            all: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_mk_opaque_val(
            name: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            value: *mut LeanObject,
            is_unsafe: u8,
            all: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_opaque_val_is_unsafe(v: *mut LeanObject) -> u8;
        fn lean_mk_quot_val(
            name: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            kind: u8,
        ) -> *mut LeanObject;
        fn lean_mk_inductive_val(
            name: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            nparams: *mut LeanObject,
            nindices: *mut LeanObject,
            all: *mut LeanObject,
            cnstrs: *mut LeanObject,
            nnested: *mut LeanObject,
            is_rec: u8,
            is_unsafe: u8,
            is_reflexive: u8,
        ) -> *mut LeanObject;
        fn lean_inductive_val_is_unsafe(v: *mut LeanObject) -> u8;
        fn lean_mk_constructor_val(
            name: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            induct: *mut LeanObject,
            cidx: *mut LeanObject,
            nparams: *mut LeanObject,
            nfields: *mut LeanObject,
            is_unsafe: u8,
        ) -> *mut LeanObject;
        fn lean_constructor_val_is_unsafe(v: *mut LeanObject) -> u8;
        fn lean_mk_recursor_val(
            name: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            all: *mut LeanObject,
            nparams: *mut LeanObject,
            nindices: *mut LeanObject,
            nmotives: *mut LeanObject,
            nminors: *mut LeanObject,
            rules: *mut LeanObject,
            k: u8,
            is_unsafe: u8,
        ) -> *mut LeanObject;
        fn lean_recursor_is_unsafe(v: *mut LeanObject) -> u8;
        fn lean_is_unsafe_inductive_decl(d: *mut LeanObject) -> u8;
    }

    #[derive(Debug)]
    enum KernelError {
        UnknownConstant { env: *mut LeanObject, name: *mut LeanObject },
        AlreadyDeclared { env: *mut LeanObject, name: *mut LeanObject },
        DeclTypeMismatch { env: *mut LeanObject, decl: *mut LeanObject, given_type: *mut LeanObject },
        DeclHasMVars { env: *mut LeanObject, name: *mut LeanObject, expr: *mut LeanObject },
        DeclHasFVars { env: *mut LeanObject, name: *mut LeanObject, expr: *mut LeanObject },
        FunExpected { env: *mut LeanObject, lctx: *mut LeanObject, expr: *mut LeanObject },
        TypeExpected { env: *mut LeanObject, lctx: *mut LeanObject, expr: *mut LeanObject },
        LetTypeMismatch {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            name: *mut LeanObject,
            given_type: *mut LeanObject,
            expected_type: *mut LeanObject,
        },
        ExprTypeMismatch {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            expr: *mut LeanObject,
            expected_type: *mut LeanObject,
        },
        AppTypeMismatch {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            app: *mut LeanObject,
            fun_type: *mut LeanObject,
            arg_type: *mut LeanObject,
        },
        InvalidProj { env: *mut LeanObject, lctx: *mut LeanObject, proj: *mut LeanObject },
        ThmTypeIsNotProp { env: *mut LeanObject, name: *mut LeanObject, type_: *mut LeanObject },
        Other { msg: *mut LeanObject },
        DeterministicTimeout,
        ExcessiveMemory,
        DeepRecursion,
        Interrupted,
    }

    impl Drop for KernelError {
        fn drop(&mut self) {
            unsafe {
                match self {
                    KernelError::UnknownConstant { env, name }
                    | KernelError::AlreadyDeclared { env, name } => {
                        lean_dec(*env);
                        lean_dec(*name);
                    }
                    KernelError::DeclTypeMismatch { env, decl, given_type } => {
                        lean_dec(*env);
                        lean_dec(*decl);
                        lean_dec(*given_type);
                    }
                    KernelError::DeclHasMVars { env, name, expr }
                    | KernelError::DeclHasFVars { env, name, expr } => {
                        lean_dec(*env);
                        lean_dec(*name);
                        lean_dec(*expr);
                    }
                    KernelError::FunExpected { env, lctx, expr }
                    | KernelError::TypeExpected { env, lctx, expr }
                    | KernelError::InvalidProj { env, lctx, proj: expr } => {
                        lean_dec(*env);
                        lean_dec(*lctx);
                        lean_dec(*expr);
                    }
                    KernelError::LetTypeMismatch { env, lctx, name, given_type, expected_type } => {
                        lean_dec(*env);
                        lean_dec(*lctx);
                        lean_dec(*name);
                        lean_dec(*given_type);
                        lean_dec(*expected_type);
                    }
                    KernelError::ExprTypeMismatch { env, lctx, expr, expected_type } => {
                        lean_dec(*env);
                        lean_dec(*lctx);
                        lean_dec(*expr);
                        lean_dec(*expected_type);
                    }
                    KernelError::AppTypeMismatch { env, lctx, app, fun_type, arg_type } => {
                        lean_dec(*env);
                        lean_dec(*lctx);
                        lean_dec(*app);
                        lean_dec(*fun_type);
                        lean_dec(*arg_type);
                    }
                    KernelError::ThmTypeIsNotProp { env, name, type_ } => {
                        lean_dec(*env);
                        lean_dec(*name);
                        lean_dec(*type_);
                    }
                    KernelError::Other { msg } => lean_dec(*msg),
                    KernelError::DeterministicTimeout
                    | KernelError::ExcessiveMemory
                    | KernelError::DeepRecursion
                    | KernelError::Interrupted => {}
                }
            }
        }
    }

    unsafe fn mk_except_ok(value: *mut LeanObject) -> *mut LeanObject {
        let r = lean_runtime_alloc_ctor(EXCEPT_OK_TAG as u32, 1, 0);
        lean_runtime_ctor_set(r, 0, value);
        r
    }

    unsafe fn mk_except_error(error: *mut LeanObject) -> *mut LeanObject {
        let r = lean_runtime_alloc_ctor(EXCEPT_ERROR_TAG as u32, 1, 0);
        lean_runtime_ctor_set(r, 0, error);
        r
    }

    unsafe fn mk_kernel_exception_ctor(tag: usize, fields: &[*mut LeanObject]) -> *mut LeanObject {
        let r = lean_runtime_alloc_ctor(tag as u32, fields.len() as u32, 0);
        for (idx, field) in fields.iter().enumerate() {
            lean_inc(*field);
            lean_runtime_ctor_set(r, idx as u32, *field);
        }
        r
    }

    unsafe fn kernel_error_to_lean_except(error: KernelError) -> *mut LeanObject {
        let exception = match &error {
            KernelError::UnknownConstant { env, name } =>
                mk_kernel_exception_ctor(KEX_UNKNOWN_CONSTANT_TAG, &[*env, *name]),
            KernelError::AlreadyDeclared { env, name } =>
                mk_kernel_exception_ctor(KEX_ALREADY_DECLARED_TAG, &[*env, *name]),
            KernelError::DeclTypeMismatch { env, decl, given_type } =>
                mk_kernel_exception_ctor(KEX_DECL_TYPE_MISMATCH_TAG, &[*env, *decl, *given_type]),
            KernelError::DeclHasMVars { env, name, expr } =>
                mk_kernel_exception_ctor(KEX_DECL_HAS_MVARS_TAG, &[*env, *name, *expr]),
            KernelError::DeclHasFVars { env, name, expr } =>
                mk_kernel_exception_ctor(KEX_DECL_HAS_FVARS_TAG, &[*env, *name, *expr]),
            KernelError::FunExpected { env, lctx, expr } =>
                mk_kernel_exception_ctor(KEX_FUN_EXPECTED_TAG, &[*env, *lctx, *expr]),
            KernelError::TypeExpected { env, lctx, expr } =>
                mk_kernel_exception_ctor(KEX_TYPE_EXPECTED_TAG, &[*env, *lctx, *expr]),
            KernelError::LetTypeMismatch { env, lctx, name, given_type, expected_type } =>
                mk_kernel_exception_ctor(KEX_LET_TYPE_MISMATCH_TAG, &[*env, *lctx, *name, *given_type, *expected_type]),
            KernelError::ExprTypeMismatch { env, lctx, expr, expected_type } =>
                mk_kernel_exception_ctor(KEX_EXPR_TYPE_MISMATCH_TAG, &[*env, *lctx, *expr, *expected_type]),
            KernelError::AppTypeMismatch { env, lctx, app, fun_type, arg_type } =>
                mk_kernel_exception_ctor(KEX_APP_TYPE_MISMATCH_TAG, &[*env, *lctx, *app, *fun_type, *arg_type]),
            KernelError::InvalidProj { env, lctx, proj } =>
                mk_kernel_exception_ctor(KEX_INVALID_PROJ_TAG, &[*env, *lctx, *proj]),
            KernelError::ThmTypeIsNotProp { env, name, type_ } =>
                mk_kernel_exception_ctor(KEX_THM_TYPE_IS_NOT_PROP_TAG, &[*env, *name, *type_]),
            KernelError::Other { msg } =>
                mk_kernel_exception_ctor(KEX_OTHER_TAG, &[*msg]),
            KernelError::DeterministicTimeout => lean_box(KEX_DETERMINISTIC_TIMEOUT_SCALAR),
            KernelError::ExcessiveMemory => lean_box(KEX_EXCESSIVE_MEMORY_SCALAR),
            KernelError::DeepRecursion => lean_box(KEX_DEEP_RECURSION_SCALAR),
            KernelError::Interrupted => lean_box(KEX_INTERRUPTED_SCALAR),
        };
        mk_except_error(exception)
    }

    unsafe fn into_lean_except<T>(result: KernelResult<*mut LeanObject>) -> *mut LeanObject {
        let _ = core::marker::PhantomData::<T>;
        match result {
            Ok(value) => mk_except_ok(value),
            Err(error) => kernel_error_to_lean_except(error),
        }
    }

    unsafe fn mk_name(text: &[u8]) -> *mut LeanObject {
        debug_assert!(text.last() == Some(&0));
        let s = lean_mk_string(text.as_ptr().cast());
        lean_name_mk_string(lean_box(0), s)
    }

    unsafe fn init_global_name(slot: &AtomicPtr<LeanObject>, text: &[u8]) {
        let value = mk_name(text);
        slot.store(value, Ordering::Release);
    }

    unsafe fn init_global_const(slot: &AtomicPtr<LeanObject>, text: &[u8]) {
        let name = mk_name(text);
        let value = lean_expr_mk_const(name, lean_box(0));
        slot.store(value, Ordering::Release);
    }

    unsafe fn finalize_global(slot: &AtomicPtr<LeanObject>) {
        let value = slot.swap(ptr::null_mut(), Ordering::AcqRel);
        if !value.is_null() {
            lean_dec(value);
        }
    }

    #[inline]
    unsafe fn borrowed_field(obj: *mut LeanObject, field: usize) -> *mut LeanObject {
        lean_ctor_get(obj, field)
    }

    #[inline]
    unsafe fn owned_field(obj: *mut LeanObject, field: usize) -> *mut LeanObject {
        let value = borrowed_field(obj, field);
        lean_inc(value);
        value
    }

    #[inline]
    unsafe fn mk_unary_ctor(tag: u8, value: *mut LeanObject) -> *mut LeanObject {
        let r = lean_runtime_alloc_ctor(tag as u32, 1, 0);
        lean_runtime_ctor_set(r, 0, value);
        r
    }

    #[inline]
    unsafe fn constant_val_of_extended(v: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(v, EXTENDS_CONSTANT_VAL_FIELD)
    }

    #[inline]
    unsafe fn constant_val_name(v: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(v, CONSTANT_VAL_NAME_FIELD)
    }

    #[inline]
    unsafe fn constant_val_lparams(v: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(v, CONSTANT_VAL_LEVEL_PARAMS_FIELD)
    }

    #[inline]
    unsafe fn constant_val_type(v: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(v, CONSTANT_VAL_TYPE_FIELD)
    }

    #[inline]
    unsafe fn extended_name(v: *mut LeanObject) -> *mut LeanObject {
        constant_val_name(constant_val_of_extended(v))
    }

    #[inline]
    unsafe fn extended_lparams(v: *mut LeanObject) -> *mut LeanObject {
        constant_val_lparams(constant_val_of_extended(v))
    }

    #[inline]
    unsafe fn extended_type(v: *mut LeanObject) -> *mut LeanObject {
        constant_val_type(constant_val_of_extended(v))
    }

    #[inline]
    unsafe fn value_val_value(v: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(v, VALUE_VAL_VALUE_FIELD)
    }

    #[inline]
    unsafe fn definition_val_hints(v: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(v, DEFINITION_VAL_HINTS_FIELD)
    }

    #[inline]
    unsafe fn axiom_val_is_unsafe(v: *mut LeanObject) -> bool {
        lean_inc(v);
        lean_axiom_val_is_unsafe(v) != 0
    }

    #[inline]
    unsafe fn definition_val_safety(v: *mut LeanObject) -> u8 {
        lean_inc(v);
        lean_definition_val_get_safety(v)
    }

    #[inline]
    unsafe fn definition_val_is_unsafe(v: *mut LeanObject) -> bool {
        definition_val_safety(v) == DEFINITION_SAFETY_UNSAFE
    }

    #[inline]
    unsafe fn definition_val_is_partial(v: *mut LeanObject) -> bool {
        definition_val_safety(v) == DEFINITION_SAFETY_PARTIAL
    }

    #[inline]
    unsafe fn opaque_val_is_unsafe(v: *mut LeanObject) -> bool {
        lean_inc(v);
        lean_opaque_val_is_unsafe(v) != 0
    }

    #[inline]
    unsafe fn inductive_val_is_unsafe(v: *mut LeanObject) -> bool {
        lean_inc(v);
        lean_inductive_val_is_unsafe(v) != 0
    }

    #[inline]
    unsafe fn constructor_val_is_unsafe(v: *mut LeanObject) -> bool {
        lean_inc(v);
        lean_constructor_val_is_unsafe(v) != 0
    }

    #[inline]
    unsafe fn recursor_val_is_unsafe(v: *mut LeanObject) -> bool {
        lean_inc(v);
        lean_recursor_is_unsafe(v) != 0
    }

    #[inline]
    unsafe fn declaration_tag(decl: *mut LeanObject) -> u8 {
        lean_obj_tag(decl)
    }

    #[inline]
    unsafe fn declaration_val(decl: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(decl, DECL_VAL_FIELD)
    }

    #[inline]
    unsafe fn inductive_decl_lparams(decl: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(decl, INDUCTIVE_DECL_LEVEL_PARAMS_FIELD)
    }

    #[inline]
    unsafe fn inductive_decl_nparams(decl: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(decl, INDUCTIVE_DECL_NUM_PARAMS_FIELD)
    }

    #[inline]
    unsafe fn inductive_decl_types(decl: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(decl, INDUCTIVE_DECL_TYPES_FIELD)
    }

    #[inline]
    unsafe fn inductive_decl_is_unsafe(decl: *mut LeanObject) -> bool {
        lean_inc(decl);
        lean_is_unsafe_inductive_decl(decl) != 0
    }

    #[inline]
    unsafe fn inductive_type_name(ind_type: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(ind_type, INDUCTIVE_TYPE_NAME_FIELD)
    }

    #[inline]
    unsafe fn inductive_type_type(ind_type: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(ind_type, INDUCTIVE_TYPE_TYPE_FIELD)
    }

    #[inline]
    unsafe fn inductive_type_ctors(ind_type: *mut LeanObject) -> *mut LeanObject {
        borrowed_field(ind_type, INDUCTIVE_TYPE_CTORS_FIELD)
    }

    unsafe fn mk_axiom_decl_from_val(val: *mut LeanObject) -> *mut LeanObject {
        lean_inc(val);
        mk_unary_ctor(DECL_AXIOM_TAG, val)
    }

    unsafe fn mk_definition_decl_from_val(val: *mut LeanObject) -> *mut LeanObject {
        lean_inc(val);
        mk_unary_ctor(DECL_DEFINITION_TAG, val)
    }

    unsafe fn mk_theorem_decl_from_val(val: *mut LeanObject) -> *mut LeanObject {
        lean_inc(val);
        mk_unary_ctor(DECL_THEOREM_TAG, val)
    }

    unsafe fn mk_opaque_decl_from_val(val: *mut LeanObject) -> *mut LeanObject {
        lean_inc(val);
        mk_unary_ctor(DECL_OPAQUE_TAG, val)
    }

    unsafe fn mk_mutual_definition_decl(defs: *mut LeanObject) -> *mut LeanObject {
        lean_inc(defs);
        mk_unary_ctor(DECL_MUTUAL_DEFINITION_TAG, defs)
    }

    unsafe fn mk_constant_info_from_val(tag: u8, val: *mut LeanObject) -> *mut LeanObject {
        lean_inc(val);
        mk_unary_ctor(tag, val)
    }

    unsafe fn mk_constant_info_from_declaration(decl: *mut LeanObject) -> Option<*mut LeanObject> {
        match declaration_tag(decl) {
            DECL_AXIOM_TAG | DECL_DEFINITION_TAG | DECL_THEOREM_TAG | DECL_OPAQUE_TAG => {
                lean_inc(decl);
                Some(decl)
            }
            _ => None,
        }
    }

    unsafe fn mk_quot_info(
        name: *mut LeanObject,
        lparams: *mut LeanObject,
        type_: *mut LeanObject,
        kind: u8,
    ) -> *mut LeanObject {
        lean_inc(name);
        lean_inc(lparams);
        lean_inc(type_);
        let val = lean_mk_quot_val(name, lparams, type_, kind);
        mk_constant_info_from_val(CONST_INFO_QUOT_TAG, val)
    }

    unsafe fn mk_inductive_info(
        name: *mut LeanObject,
        lparams: *mut LeanObject,
        type_: *mut LeanObject,
        nparams: *mut LeanObject,
        nindices: *mut LeanObject,
        all: *mut LeanObject,
        cnstrs: *mut LeanObject,
        nnested: *mut LeanObject,
        is_rec: bool,
        is_unsafe: bool,
        is_reflexive: bool,
    ) -> *mut LeanObject {
        lean_inc(name);
        lean_inc(lparams);
        lean_inc(type_);
        lean_inc(nparams);
        lean_inc(nindices);
        lean_inc(all);
        lean_inc(cnstrs);
        lean_inc(nnested);
        let val = lean_mk_inductive_val(
            name,
            lparams,
            type_,
            nparams,
            nindices,
            all,
            cnstrs,
            nnested,
            is_rec as u8,
            is_unsafe as u8,
            is_reflexive as u8,
        );
        mk_constant_info_from_val(CONST_INFO_INDUCTIVE_TAG, val)
    }

    unsafe fn environment_find(env: *mut LeanObject, name: *mut LeanObject) -> Option<*mut LeanObject> {
        lean_inc(env);
        lean_inc(name);
        let opt = lean_environment_find(env, name);
        if lean_is_scalar(opt) {
            None
        } else {
            let value = owned_field(opt, 0);
            lean_dec(opt);
            Some(value)
        }
    }

    unsafe fn environment_add_info(env: *mut LeanObject, info: *mut LeanObject) -> *mut LeanObject {
        lean_inc(env);
        lean_inc(info);
        lean_environment_add(env, info)
    }

    unsafe fn declaration_name(decl: *mut LeanObject) -> Option<*mut LeanObject> {
        match declaration_tag(decl) {
            DECL_AXIOM_TAG | DECL_DEFINITION_TAG | DECL_THEOREM_TAG | DECL_OPAQUE_TAG => {
                Some(extended_name(declaration_val(decl)))
            }
            DECL_INDUCTIVE_TAG => {
                let types = inductive_decl_types(decl);
                if lean_is_scalar(types) {
                    None
                } else {
                    Some(inductive_type_name(borrowed_field(types, 0)))
                }
            }
            _ => None,
        }
    }

    unsafe fn declaration_is_unsafe(decl: *mut LeanObject) -> bool {
        match declaration_tag(decl) {
            DECL_AXIOM_TAG => axiom_val_is_unsafe(declaration_val(decl)),
            DECL_DEFINITION_TAG => definition_val_is_unsafe(declaration_val(decl)),
            DECL_THEOREM_TAG | DECL_QUOT_TAG => false,
            DECL_OPAQUE_TAG => opaque_val_is_unsafe(declaration_val(decl)),
            DECL_MUTUAL_DEFINITION_TAG => true,
            DECL_INDUCTIVE_TAG => inductive_decl_is_unsafe(decl),
            _ => false,
        }
    }

    unsafe fn constant_info_is_unsafe(info: *mut LeanObject) -> bool {
        match lean_obj_tag(info) {
            CONST_INFO_AXIOM_TAG => axiom_val_is_unsafe(declaration_val(info)),
            CONST_INFO_DEFINITION_TAG => definition_val_is_unsafe(declaration_val(info)),
            CONST_INFO_THEOREM_TAG | CONST_INFO_QUOT_TAG => false,
            CONST_INFO_OPAQUE_TAG => opaque_val_is_unsafe(declaration_val(info)),
            CONST_INFO_INDUCTIVE_TAG => inductive_val_is_unsafe(declaration_val(info)),
            CONST_INFO_CONSTRUCTOR_TAG => constructor_val_is_unsafe(declaration_val(info)),
            CONST_INFO_RECURSOR_TAG => recursor_val_is_unsafe(declaration_val(info)),
            _ => false,
        }
    }

    unsafe fn kernel_is_def_eq_impl(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_is_def_eq(env, lctx, a, b)
    }

    unsafe fn kernel_whnf_impl(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_whnf(env, lctx, a)
    }

    unsafe fn kernel_check_impl(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_check(env, lctx, a)
    }

    unsafe fn lean_kernel_is_def_eq_result_bridge(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> *mut LeanObject {
        kernel_is_def_eq_impl(env, lctx, a, b)
    }

    unsafe fn lean_kernel_whnf_result_bridge(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        kernel_whnf_impl(env, lctx, a)
    }

    unsafe fn lean_kernel_check_result_bridge(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        kernel_check_impl(env, lctx, a)
    }

    fn initialize_type_checker_rust() {
        unsafe {
            init_global_name(&G_KERNEL_FRESH, b"_kernel_fresh\0");
            init_global_const(&G_DONT_CARE, b"_kernel.dontCare\0");
            init_global_name(&G_BOOL_TRUE, b"Bool.true\0");
            init_global_name(&G_EAGER_REDUCE, b"eagerReduce\0");
        }
    }

    fn finalize_type_checker_rust() {
        unsafe {
            finalize_global(&G_KERNEL_FRESH);
            finalize_global(&G_DONT_CARE);
            finalize_global(&G_BOOL_TRUE);
            finalize_global(&G_EAGER_REDUCE);
        }
    }

}
