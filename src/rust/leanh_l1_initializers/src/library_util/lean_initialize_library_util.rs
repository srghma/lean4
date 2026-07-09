use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicPtr, Ordering};
use leanh_l1::datatypes::LeanObject;
use leanh_l1::emitted::lean_box::lean_box;
use leanh_l1::emitted::lean_mark_persistent::lean_mark_persistent;

use crate::library_constants::{get_bool_false_name, get_bool_true_name};
use crate::r#priv::initialize_constructions_module::{
    lean_register_name_generator_prefix, mk_name,
};
use crate::todo_import_from_lean::lean_expr_mk_const::lean_expr_mk_const;

static INITIALIZED: AtomicBool = AtomicBool::new(false);
static BOOL_TRUE: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
static BOOL_FALSE: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
static UTIL_FRESH: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());

unsafe fn initialize_library_util_impl() {
    let bool_false_name = *get_bool_false_name();
    let bool_true_name = *get_bool_true_name();

    let false_expr = lean_expr_mk_const(bool_false_name.obj, lean_box(0));
    let true_expr = lean_expr_mk_const(bool_true_name.obj, lean_box(0));

    lean_mark_persistent(false_expr);
    lean_mark_persistent(true_expr);

    BOOL_FALSE.store(false_expr, Ordering::Release);
    BOOL_TRUE.store(true_expr, Ordering::Release);

    let util_fresh = mk_name("_util_fresh");
    lean_mark_persistent(util_fresh.obj);
    UTIL_FRESH.store(util_fresh.obj, Ordering::Release);
    lean_register_name_generator_prefix(util_fresh.obj);
}

unsafe fn ensure_initialized() {
    if INITIALIZED
        .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
        .is_ok()
    {
        initialize_library_util_impl();
    }
}

pub unsafe fn lean_initialize_library_util() {
    ensure_initialized();
}
