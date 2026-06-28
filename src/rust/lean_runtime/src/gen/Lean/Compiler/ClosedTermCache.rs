// Lean compiler output
// Module: Lean.Compiler.ClosedTermCache
// Imports: Lean.Environment
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Prelude::l_List_lengthTR___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment,
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_registerEnvExtension___redArg,
    runtime_initialize_Lean_Environment,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_hash;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
    lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_instInhabitedClosedTermCache_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedClosedTermCache_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedClosedTermCache_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedClosedTermCache_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedClosedTermCache_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedClosedTermCache_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedClosedTermCache_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedClosedTermCache: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 0]};
static mut l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__0_value) as *mut LeanObject;
pub static l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__1_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0]};
static mut l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 97, 112, 0]};
static mut l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_instInhabitedClosedTermCache_default___closed__0() -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_438_;
}
pub unsafe fn _init_l_Lean_instInhabitedClosedTermCache_default___closed__1() -> *mut LeanObject {
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___x_439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClosedTermCache_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClosedTermCache_default___closed__0_once),
        _init_l_Lean_instInhabitedClosedTermCache_default___closed__0,
    );
    v___x_440_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_440_, 0, v___x_439_);
    return v___x_440_;
}
pub unsafe fn _init_l_Lean_instInhabitedClosedTermCache_default___closed__2() -> *mut LeanObject {
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    v___x_441_ = lean_box(0);
    v___x_442_ = l_Lean_NameSet_empty;
    v___x_443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClosedTermCache_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClosedTermCache_default___closed__1_once),
        _init_l_Lean_instInhabitedClosedTermCache_default___closed__1,
    );
    v___x_444_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_444_, 0, v___x_443_);
    lean_ctor_set(v___x_444_, 1, v___x_442_);
    lean_ctor_set(v___x_444_, 2, v___x_441_);
    return v___x_444_;
}
pub unsafe fn _init_l_Lean_instInhabitedClosedTermCache_default() -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClosedTermCache_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClosedTermCache_default___closed__2_once),
        _init_l_Lean_instInhabitedClosedTermCache_default___closed__2,
    );
    return v___x_445_;
}
pub unsafe fn _init_l_Lean_instInhabitedClosedTermCache() -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Lean_instInhabitedClosedTermCache_default;
    return v___x_446_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__2(
    mut v_msg_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    v___x_448_ = lean_box(0);
    v___x_449_ = lean_panic_fn_borrowed(v___x_448_, v_msg_447_);
    return v___x_449_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(
    mut v_keys_450_: *mut LeanObject,
    mut v_vals_451_: *mut LeanObject,
    mut v_i_452_: *mut LeanObject,
    mut v_k_453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: u8 = 0;
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_454_ = lean_array_get_size(v_keys_450_);
                v___x_455_ = lean_nat_dec_lt(v_i_452_, v___x_454_);
                if v___x_455_ == 0 {
                    lean_dec(v_i_452_);
                    v___x_456_ = lean_box(0);
                    return v___x_456_;
                } else {
                    v_k_x27_457_ = lean_array_fget_borrowed(v_keys_450_, v_i_452_);
                    v___x_458_ = lean_expr_eqv(v_k_453_, v_k_x27_457_);
                    if v___x_458_ == 0 {
                        v___x_459_ = lean_unsigned_to_nat(1);
                        v___x_460_ = lean_nat_add(v_i_452_, v___x_459_);
                        lean_dec(v_i_452_);
                        v_i_452_ = v___x_460_;
                        state = 0;
                        continue;
                    } else {
                        v___x_462_ = lean_array_fget_borrowed(v_vals_451_, v_i_452_);
                        lean_dec(v_i_452_);
                        lean_inc(v___x_462_);
                        v___x_463_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_463_, 0, v___x_462_);
                        return v___x_463_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg___boxed(
    mut v_keys_464_: *mut LeanObject,
    mut v_vals_465_: *mut LeanObject,
    mut v_i_466_: *mut LeanObject,
    mut v_k_467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_468_: *mut LeanObject = core::ptr::null_mut();
    v_res_468_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_464_, v_vals_465_, v_i_466_, v_k_467_);
    lean_dec_ref(v_k_467_);
    lean_dec_ref(v_vals_465_);
    lean_dec_ref(v_keys_464_);
    return v_res_468_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_469_: usize = 0;
    let mut v___x_470_: usize = 0;
    let mut v___x_471_: usize = 0;
    v___x_469_ = 5usize;
    v___x_470_ = 1usize;
    v___x_471_ = lean_usize_shift_left(v___x_470_, v___x_469_);
    return v___x_471_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_472_: usize = 0;
    let mut v___x_473_: usize = 0;
    let mut v___x_474_: usize = 0;
    v___x_472_ = 1usize;
    v___x_473_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0);
    v___x_474_ = lean_usize_sub(v___x_473_, v___x_472_);
    return v___x_474_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_x_475_: *mut LeanObject,
    mut v_x_476_: usize,
    mut v_x_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: usize = 0;
    let mut v___x_481_: usize = 0;
    let mut v___x_482_: usize = 0;
    let mut v_j_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: u8 = 0;
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: usize = 0;
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_475_) == 0 {
                    v_es_478_ = lean_ctor_get(v_x_475_, 0);
                    v___x_479_ = lean_box(2);
                    v___x_480_ = 5usize;
                    v___x_481_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1);
                    v___x_482_ = lean_usize_land(v_x_476_, v___x_481_);
                    v_j_483_ = lean_usize_to_nat(v___x_482_);
                    v___x_484_ = lean_array_get_borrowed(v___x_479_, v_es_478_, v_j_483_);
                    lean_dec(v_j_483_);
                    match lean_obj_tag(v___x_484_) {
                        0 => {
                            v_key_485_ = lean_ctor_get(v___x_484_, 0);
                            v_val_486_ = lean_ctor_get(v___x_484_, 1);
                            v___x_487_ = lean_expr_eqv(v_x_477_, v_key_485_);
                            if v___x_487_ == 0 {
                                v___x_488_ = lean_box(0);
                                return v___x_488_;
                            } else {
                                lean_inc(v_val_486_);
                                v___x_489_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_489_, 0, v_val_486_);
                                return v___x_489_;
                            }
                        }
                        1 => {
                            v_node_490_ = lean_ctor_get(v___x_484_, 0);
                            v___x_491_ = lean_usize_shift_right(v_x_476_, v___x_480_);
                            v_x_475_ = v_node_490_;
                            v_x_476_ = v___x_491_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_493_ = lean_box(0);
                            return v___x_493_;
                        }
                    }
                } else {
                    v_ks_494_ = lean_ctor_get(v_x_475_, 0);
                    v_vs_495_ = lean_ctor_get(v_x_475_, 1);
                    v___x_496_ = lean_unsigned_to_nat(0);
                    v___x_497_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_ks_494_, v_vs_495_, v___x_496_, v_x_477_);
                    return v___x_497_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(
    mut v_x_498_: *mut LeanObject,
    mut v_x_499_: *mut LeanObject,
    mut v_x_500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_566__boxed_501_: usize = 0;
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
    v_x_566__boxed_501_ = lean_unbox_usize(v_x_499_);
    lean_dec(v_x_499_);
    v_res_502_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_498_, v_x_566__boxed_501_, v_x_500_);
    lean_dec_ref(v_x_500_);
    lean_dec_ref(v_x_498_);
    return v_res_502_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_503_: *mut LeanObject,
    mut v_x_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_505_: u64 = 0;
    let mut v___x_506_: usize = 0;
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    v___x_505_ = l_Lean_Expr_hash(v_x_504_);
    v___x_506_ = lean_uint64_to_usize(v___x_505_);
    v___x_507_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_503_, v___x_506_, v_x_504_);
    return v___x_507_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_x_508_: *mut LeanObject,
    mut v_x_509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_510_: *mut LeanObject = core::ptr::null_mut();
    v_res_510_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(v_x_508_, v_x_509_);
    lean_dec_ref(v_x_509_);
    lean_dec_ref(v_x_508_);
    return v_res_510_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_x_511_: *mut LeanObject,
    mut v_x_512_: *mut LeanObject,
    mut v_x_513_: *mut LeanObject,
    mut v_x_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: u8 = 0;
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: u8 = 0;
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_515_ = lean_ctor_get(v_x_511_, 0);
                v_vs_516_ = lean_ctor_get(v_x_511_, 1);
                v_isSharedCheck_540_ = (!lean_is_exclusive(v_x_511_)) as u8;
                if v_isSharedCheck_540_ == 0 {
                    v___x_518_ = v_x_511_;
                    v_isShared_519_ = v_isSharedCheck_540_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_516_);
                    lean_inc(v_ks_515_);
                    lean_dec(v_x_511_);
                    v___x_518_ = lean_box(0);
                    v_isShared_519_ = v_isSharedCheck_540_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_520_ = lean_array_get_size(v_ks_515_);
                v___x_521_ = lean_nat_dec_lt(v_x_512_, v___x_520_);
                if v___x_521_ == 0 {
                    lean_dec(v_x_512_);
                    v___x_522_ = lean_array_push(v_ks_515_, v_x_513_);
                    v___x_523_ = lean_array_push(v_vs_516_, v_x_514_);
                    if v_isShared_519_ == 0 {
                        lean_ctor_set(v___x_518_, 1, v___x_523_);
                        lean_ctor_set(v___x_518_, 0, v___x_522_);
                        v___x_525_ = v___x_518_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_522_);
                        lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_523_);
                        v___x_525_ = v_reuseFailAlloc_526_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_527_ = lean_array_fget_borrowed(v_ks_515_, v_x_512_);
                    v___x_528_ = lean_expr_eqv(v_x_513_, v_k_x27_527_);
                    if v___x_528_ == 0 {
                        if v_isShared_519_ == 0 {
                            v___x_530_ = v___x_518_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_534_, 0, v_ks_515_);
                            lean_ctor_set(v_reuseFailAlloc_534_, 1, v_vs_516_);
                            v___x_530_ = v_reuseFailAlloc_534_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_535_ = lean_array_fset(v_ks_515_, v_x_512_, v_x_513_);
                        v___x_536_ = lean_array_fset(v_vs_516_, v_x_512_, v_x_514_);
                        lean_dec(v_x_512_);
                        if v_isShared_519_ == 0 {
                            lean_ctor_set(v___x_518_, 1, v___x_536_);
                            lean_ctor_set(v___x_518_, 0, v___x_535_);
                            v___x_538_ = v___x_518_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_535_);
                            lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
                            v___x_538_ = v_reuseFailAlloc_539_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_525_;
            }
            3 => {
                v___x_531_ = lean_unsigned_to_nat(1);
                v___x_532_ = lean_nat_add(v_x_512_, v___x_531_);
                lean_dec(v_x_512_);
                v_x_511_ = v___x_530_;
                v_x_512_ = v___x_532_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(
    mut v_n_541_: *mut LeanObject,
    mut v_k_542_: *mut LeanObject,
    mut v_v_543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    v___x_544_ = lean_unsigned_to_nat(0);
    v___x_545_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_n_541_, v___x_544_, v_k_542_, v_v_543_);
    return v___x_545_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    v___x_546_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_546_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_547_: *mut LeanObject,
    mut v_x_548_: usize,
    mut v_x_549_: usize,
    mut v_x_550_: *mut LeanObject,
    mut v_x_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: usize = 0;
    let mut v___x_554_: usize = 0;
    let mut v___x_555_: usize = 0;
    let mut v___x_556_: usize = 0;
    let mut v_j_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: u8 = 0;
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_562_: u8 = 0;
    let mut v_v_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v___x_577_: u8 = 0;
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_583_: u8 = 0;
    let mut v_node_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_587_: u8 = 0;
    let mut v___x_588_: usize = 0;
    let mut v___x_589_: usize = 0;
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_594_: u8 = 0;
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_596_: u8 = 0;
    let mut v_unused_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_602_: u8 = 0;
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_607_: u8 = 0;
    let mut v_ks_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: usize = 0;
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: u8 = 0;
    let mut v_reuseFailAlloc_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_547_) == 0 {
                    v_es_552_ = lean_ctor_get(v_x_547_, 0);
                    v___x_553_ = 5usize;
                    v___x_554_ = 1usize;
                    v___x_555_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1);
                    v___x_556_ = lean_usize_land(v_x_548_, v___x_555_);
                    v_j_557_ = lean_usize_to_nat(v___x_556_);
                    v___x_558_ = lean_array_get_size(v_es_552_);
                    v___x_559_ = lean_nat_dec_lt(v_j_557_, v___x_558_);
                    if v___x_559_ == 0 {
                        lean_dec(v_j_557_);
                        lean_dec(v_x_551_);
                        lean_dec_ref(v_x_550_);
                        return v_x_547_;
                    } else {
                        lean_inc_ref(v_es_552_);
                        v_isSharedCheck_596_ = (!lean_is_exclusive(v_x_547_)) as u8;
                        if v_isSharedCheck_596_ == 0 {
                            v_unused_597_ = lean_ctor_get(v_x_547_, 0);
                            lean_dec(v_unused_597_);
                            v___x_561_ = v_x_547_;
                            v_isShared_562_ = v_isSharedCheck_596_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_547_);
                            v___x_561_ = lean_box(0);
                            v_isShared_562_ = v_isSharedCheck_596_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_598_ = lean_ctor_get(v_x_547_, 0);
                    v_vs_599_ = lean_ctor_get(v_x_547_, 1);
                    v_isSharedCheck_619_ = (!lean_is_exclusive(v_x_547_)) as u8;
                    if v_isSharedCheck_619_ == 0 {
                        v___x_601_ = v_x_547_;
                        v_isShared_602_ = v_isSharedCheck_619_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_599_);
                        lean_inc(v_ks_598_);
                        lean_dec(v_x_547_);
                        v___x_601_ = lean_box(0);
                        v_isShared_602_ = v_isSharedCheck_619_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_563_ = lean_array_fget(v_es_552_, v_j_557_);
                v___x_564_ = lean_box(0);
                v_xs_x27_565_ = lean_array_fset(v_es_552_, v_j_557_, v___x_564_);
                match lean_obj_tag(v_v_563_) {
                    0 => {
                        v_key_572_ = lean_ctor_get(v_v_563_, 0);
                        v_val_573_ = lean_ctor_get(v_v_563_, 1);
                        v_isSharedCheck_583_ = (!lean_is_exclusive(v_v_563_)) as u8;
                        if v_isSharedCheck_583_ == 0 {
                            v___x_575_ = v_v_563_;
                            v_isShared_576_ = v_isSharedCheck_583_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_573_);
                            lean_inc(v_key_572_);
                            lean_dec(v_v_563_);
                            v___x_575_ = lean_box(0);
                            v_isShared_576_ = v_isSharedCheck_583_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_584_ = lean_ctor_get(v_v_563_, 0);
                        v_isSharedCheck_594_ = (!lean_is_exclusive(v_v_563_)) as u8;
                        if v_isSharedCheck_594_ == 0 {
                            v___x_586_ = v_v_563_;
                            v_isShared_587_ = v_isSharedCheck_594_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_584_);
                            lean_dec(v_v_563_);
                            v___x_586_ = lean_box(0);
                            v_isShared_587_ = v_isSharedCheck_594_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_595_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_595_, 0, v_x_550_);
                        lean_ctor_set(v___x_595_, 1, v_x_551_);
                        v___y_567_ = v___x_595_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_568_ = lean_array_fset(v_xs_x27_565_, v_j_557_, v___y_567_);
                lean_dec(v_j_557_);
                if v_isShared_562_ == 0 {
                    lean_ctor_set(v___x_561_, 0, v___x_568_);
                    v___x_570_ = v___x_561_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
                    v___x_570_ = v_reuseFailAlloc_571_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_570_;
            }
            4 => {
                v___x_577_ = lean_expr_eqv(v_x_550_, v_key_572_);
                if v___x_577_ == 0 {
                    lean_del_object(v___x_575_);
                    v___x_578_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_572_, v_val_573_, v_x_550_, v_x_551_,
                    );
                    v___x_579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_579_, 0, v___x_578_);
                    v___y_567_ = v___x_579_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_573_);
                    lean_dec(v_key_572_);
                    if v_isShared_576_ == 0 {
                        lean_ctor_set(v___x_575_, 1, v_x_551_);
                        lean_ctor_set(v___x_575_, 0, v_x_550_);
                        v___x_581_ = v___x_575_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_582_, 0, v_x_550_);
                        lean_ctor_set(v_reuseFailAlloc_582_, 1, v_x_551_);
                        v___x_581_ = v_reuseFailAlloc_582_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_567_ = v___x_581_;
                state = 2;
                continue;
            }
            6 => {
                v___x_588_ = lean_usize_shift_right(v_x_548_, v___x_553_);
                v___x_589_ = lean_usize_add(v_x_549_, v___x_554_);
                v___x_590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_node_584_, v___x_588_, v___x_589_, v_x_550_, v_x_551_);
                if v_isShared_587_ == 0 {
                    lean_ctor_set(v___x_586_, 0, v___x_590_);
                    v___x_592_ = v___x_586_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
                    v___x_592_ = v_reuseFailAlloc_593_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_567_ = v___x_592_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_602_ == 0 {
                    v___x_604_ = v___x_601_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_618_, 0, v_ks_598_);
                    lean_ctor_set(v_reuseFailAlloc_618_, 1, v_vs_599_);
                    v___x_604_ = v_reuseFailAlloc_618_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_605_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v___x_604_, v_x_550_, v_x_551_);
                v___x_613_ = 7usize;
                v___x_614_ = lean_usize_dec_le(v___x_613_, v_x_549_);
                if v___x_614_ == 0 {
                    v___x_615_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_605_);
                    v___x_616_ = lean_unsigned_to_nat(4);
                    v___x_617_ = lean_nat_dec_lt(v___x_615_, v___x_616_);
                    lean_dec(v___x_615_);
                    v___y_607_ = v___x_617_;
                    state = 10;
                    continue;
                } else {
                    v___y_607_ = v___x_614_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_607_ == 0 {
                    v_ks_608_ = lean_ctor_get(v_newNode_605_, 0);
                    lean_inc_ref(v_ks_608_);
                    v_vs_609_ = lean_ctor_get(v_newNode_605_, 1);
                    lean_inc_ref(v_vs_609_);
                    lean_dec_ref(v_newNode_605_);
                    v___x_610_ = lean_unsigned_to_nat(0);
                    v___x_611_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
                    v___x_612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_x_549_, v_ks_608_, v_vs_609_, v___x_610_, v___x_611_);
                    lean_dec_ref(v_vs_609_);
                    lean_dec_ref(v_ks_608_);
                    return v___x_612_;
                } else {
                    return v_newNode_605_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(
    mut v_depth_620_: usize,
    mut v_keys_621_: *mut LeanObject,
    mut v_vals_622_: *mut LeanObject,
    mut v_i_623_: *mut LeanObject,
    mut v_entries_624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: u8 = 0;
    let mut v_k_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: u64 = 0;
    let mut v_h_630_: usize = 0;
    let mut v___x_631_: usize = 0;
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: usize = 0;
    let mut v___x_634_: usize = 0;
    let mut v___x_635_: usize = 0;
    let mut v_h_636_: usize = 0;
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_625_ = lean_array_get_size(v_keys_621_);
                v___x_626_ = lean_nat_dec_lt(v_i_623_, v___x_625_);
                if v___x_626_ == 0 {
                    lean_dec(v_i_623_);
                    return v_entries_624_;
                } else {
                    v_k_627_ = lean_array_fget_borrowed(v_keys_621_, v_i_623_);
                    v_v_628_ = lean_array_fget_borrowed(v_vals_622_, v_i_623_);
                    v___x_629_ = l_Lean_Expr_hash(v_k_627_);
                    v_h_630_ = lean_uint64_to_usize(v___x_629_);
                    v___x_631_ = 5usize;
                    v___x_632_ = lean_unsigned_to_nat(1);
                    v___x_633_ = 1usize;
                    v___x_634_ = lean_usize_sub(v_depth_620_, v___x_633_);
                    v___x_635_ = lean_usize_mul(v___x_631_, v___x_634_);
                    v_h_636_ = lean_usize_shift_right(v_h_630_, v___x_635_);
                    v___x_637_ = lean_nat_add(v_i_623_, v___x_632_);
                    lean_dec(v_i_623_);
                    lean_inc(v_v_628_);
                    lean_inc(v_k_627_);
                    v___x_638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_entries_624_, v_h_636_, v_depth_620_, v_k_627_, v_v_628_);
                    v_i_623_ = v___x_637_;
                    v_entries_624_ = v___x_638_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(
    mut v_depth_640_: *mut LeanObject,
    mut v_keys_641_: *mut LeanObject,
    mut v_vals_642_: *mut LeanObject,
    mut v_i_643_: *mut LeanObject,
    mut v_entries_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_645_: usize = 0;
    let mut v_res_646_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_645_ = lean_unbox_usize(v_depth_640_);
    lean_dec(v_depth_640_);
    v_res_646_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_boxed_645_, v_keys_641_, v_vals_642_, v_i_643_, v_entries_644_);
    lean_dec_ref(v_vals_642_);
    lean_dec_ref(v_keys_641_);
    return v_res_646_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_x_647_: *mut LeanObject,
    mut v_x_648_: *mut LeanObject,
    mut v_x_649_: *mut LeanObject,
    mut v_x_650_: *mut LeanObject,
    mut v_x_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_713__boxed_652_: usize = 0;
    let mut v_x_714__boxed_653_: usize = 0;
    let mut v_res_654_: *mut LeanObject = core::ptr::null_mut();
    v_x_713__boxed_652_ = lean_unbox_usize(v_x_648_);
    lean_dec(v_x_648_);
    v_x_714__boxed_653_ = lean_unbox_usize(v_x_649_);
    lean_dec(v_x_649_);
    v_res_654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_647_, v_x_713__boxed_652_, v_x_714__boxed_653_, v_x_650_, v_x_651_);
    return v_res_654_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_655_: *mut LeanObject,
    mut v_x_656_: *mut LeanObject,
    mut v_x_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_658_: u64 = 0;
    let mut v___x_659_: usize = 0;
    let mut v___x_660_: usize = 0;
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    v___x_658_ = l_Lean_Expr_hash(v_x_656_);
    v___x_659_ = lean_uint64_to_usize(v___x_658_);
    v___x_660_ = 1usize;
    v___x_661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_655_, v___x_659_, v___x_660_, v_x_656_, v_x_657_);
    return v___x_661_;
}
pub unsafe fn _init_l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_665_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__2;
    v___x_666_ = lean_unsigned_to_nat(14);
    v___x_667_ = lean_unsigned_to_nat(177);
    v___x_668_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__1;
    v___x_669_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__0;
    v___x_670_ =
        l_mkPanicMessageWithDecl(v___x_669_, v___x_668_, v___x_667_, v___x_666_, v___x_665_);
    return v___x_670_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3(
    mut v_newState_671_: *mut LeanObject,
    mut v_x_672_: *mut LeanObject,
    mut v_x_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___y_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constNames_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revExprs_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_686_: u8 = 0;
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_696_: u8 = 0;
    let mut v_map_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_673_) == 0 {
                    return v_x_672_;
                } else {
                    v_head_674_ = lean_ctor_get(v_x_673_, 0);
                    v_tail_675_ = lean_ctor_get(v_x_673_, 1);
                    v_isSharedCheck_702_ = (!lean_is_exclusive(v_x_673_)) as u8;
                    if v_isSharedCheck_702_ == 0 {
                        v___x_677_ = v_x_673_;
                        v_isShared_678_ = v_isSharedCheck_702_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_675_);
                        lean_inc(v_head_674_);
                        lean_dec(v_x_673_);
                        v___x_677_ = lean_box(0);
                        v_isShared_678_ = v_isSharedCheck_702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_map_697_ = lean_ctor_get(v_newState_671_, 0);
                v___x_698_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(v_map_697_, v_head_674_);
                if lean_obj_tag(v___x_698_) == 0 {
                    v___x_699_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3_once), _init_l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3);
                    v___x_700_ = l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__2(v___x_699_);
                    v___y_680_ = v___x_700_;
                    state = 2;
                    continue;
                } else {
                    v_val_701_ = lean_ctor_get(v___x_698_, 0);
                    lean_inc(v_val_701_);
                    lean_dec_ref_known(v___x_698_, 1);
                    v___y_680_ = v_val_701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_map_681_ = lean_ctor_get(v_x_672_, 0);
                v_constNames_682_ = lean_ctor_get(v_x_672_, 1);
                v_revExprs_683_ = lean_ctor_get(v_x_672_, 2);
                v_isSharedCheck_696_ = (!lean_is_exclusive(v_x_672_)) as u8;
                if v_isSharedCheck_696_ == 0 {
                    v___x_685_ = v_x_672_;
                    v_isShared_686_ = v_isSharedCheck_696_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_revExprs_683_);
                    lean_inc(v_constNames_682_);
                    lean_inc(v_map_681_);
                    lean_dec(v_x_672_);
                    v___x_685_ = lean_box(0);
                    v_isShared_686_ = v_isSharedCheck_696_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v___y_680_);
                lean_inc(v_head_674_);
                v___x_687_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(v_map_681_, v_head_674_, v___y_680_);
                v___x_688_ = l_Lean_NameSet_insert(v_constNames_682_, v___y_680_);
                if v_isShared_678_ == 0 {
                    lean_ctor_set(v___x_677_, 1, v_revExprs_683_);
                    v___x_690_ = v___x_677_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_695_, 0, v_head_674_);
                    lean_ctor_set(v_reuseFailAlloc_695_, 1, v_revExprs_683_);
                    v___x_690_ = v_reuseFailAlloc_695_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_686_ == 0 {
                    lean_ctor_set(v___x_685_, 2, v___x_690_);
                    lean_ctor_set(v___x_685_, 1, v___x_688_);
                    lean_ctor_set(v___x_685_, 0, v___x_687_);
                    v___x_692_ = v___x_685_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_687_);
                    lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_688_);
                    lean_ctor_set(v_reuseFailAlloc_694_, 2, v___x_690_);
                    v___x_692_ = v_reuseFailAlloc_694_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_672_ = v___x_692_;
                v_x_673_ = v_tail_675_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___boxed(
    mut v_newState_703_: *mut LeanObject,
    mut v_x_704_: *mut LeanObject,
    mut v_x_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_706_: *mut LeanObject = core::ptr::null_mut();
    v_res_706_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3(v_newState_703_, v_x_704_, v_x_705_);
    lean_dec_ref(v_newState_703_);
    return v_res_706_;
}
pub unsafe fn l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(
    mut v_oldState_709_: *mut LeanObject,
    mut v_newState_710_: *mut LeanObject,
    mut v_x_711_: *mut LeanObject,
    mut v_s_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_revExprs_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revExprs_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newExprs_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    v_revExprs_713_ = lean_ctor_get(v_newState_710_, 2);
    v_revExprs_714_ = lean_ctor_get(v_oldState_709_, 2);
    v___x_715_ = l_List_lengthTR___redArg(v_revExprs_713_);
    v___x_716_ = l_List_lengthTR___redArg(v_revExprs_714_);
    v___x_717_ = lean_nat_sub(v___x_715_, v___x_716_);
    lean_dec(v___x_716_);
    lean_dec(v___x_715_);
    v___x_718_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_;
    lean_inc(v_revExprs_713_);
    v_newExprs_719_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        lean_box(0),
        v_revExprs_713_,
        v_revExprs_713_,
        v___x_717_,
        v___x_718_,
    );
    v___x_720_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3(v_newState_710_, v_s_712_, v_newExprs_719_);
    lean_dec_ref(v_newState_710_);
    return v___x_720_;
}
pub unsafe fn l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(
    mut v_oldState_721_: *mut LeanObject,
    mut v_newState_722_: *mut LeanObject,
    mut v_x_723_: *mut LeanObject,
    mut v_s_724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_725_: *mut LeanObject = core::ptr::null_mut();
    v_res_725_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(v_oldState_721_, v_newState_722_, v_x_723_, v_s_724_);
    lean_dec(v_x_723_);
    lean_dec_ref(v_oldState_721_);
    return v_res_725_;
}
pub unsafe fn l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(
    mut v___x_726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_728_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_728_, 0, v___x_726_);
    return v___x_728_;
}
pub unsafe fn l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(
    mut v___x_729_: *mut LeanObject,
    mut v___y_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_731_: *mut LeanObject = core::ptr::null_mut();
    v_res_731_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(v___x_729_);
    return v_res_731_;
}
pub unsafe fn _init_l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_734_: *mut LeanObject = core::ptr::null_mut();
    v___x_733_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClosedTermCache_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClosedTermCache_default___closed__2_once),
        _init_l_Lean_instInhabitedClosedTermCache_default___closed__2,
    );
    v___f_734_ = lean_alloc_closure(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_734_, 0, v___x_733_);
    return v___f_734_;
}
pub unsafe fn l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    v___f_738_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_);
    v___x_739_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_;
    v___x_740_ = lean_box(0);
    v___x_741_ = l_Lean_registerEnvExtension___redArg(v___f_738_, v___x_739_, v___x_740_);
    return v___x_741_;
}
pub unsafe fn l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(
    mut v_a_742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_743_: *mut LeanObject = core::ptr::null_mut();
    v_res_743_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_();
    return v_res_743_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_744_: *mut LeanObject,
    mut v_x_745_: *mut LeanObject,
    mut v_x_746_: *mut LeanObject,
    mut v_x_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    v___x_748_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(v_x_745_, v_x_746_, v_x_747_);
    return v___x_748_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_749_: *mut LeanObject,
    mut v_x_750_: *mut LeanObject,
    mut v_x_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(v_x_750_, v_x_751_);
    return v___x_752_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b2_753_: *mut LeanObject,
    mut v_x_754_: *mut LeanObject,
    mut v_x_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_756_: *mut LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1(v_00_u03b2_753_, v_x_754_, v_x_755_);
    lean_dec_ref(v_x_755_);
    lean_dec_ref(v_x_754_);
    return v_res_756_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_757_: *mut LeanObject,
    mut v_x_758_: *mut LeanObject,
    mut v_x_759_: usize,
    mut v_x_760_: usize,
    mut v_x_761_: *mut LeanObject,
    mut v_x_762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v___x_763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_758_, v_x_759_, v_x_760_, v_x_761_, v_x_762_);
    return v___x_763_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_764_: *mut LeanObject,
    mut v_x_765_: *mut LeanObject,
    mut v_x_766_: *mut LeanObject,
    mut v_x_767_: *mut LeanObject,
    mut v_x_768_: *mut LeanObject,
    mut v_x_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1042__boxed_770_: usize = 0;
    let mut v_x_1043__boxed_771_: usize = 0;
    let mut v_res_772_: *mut LeanObject = core::ptr::null_mut();
    v_x_1042__boxed_770_ = lean_unbox_usize(v_x_766_);
    lean_dec(v_x_766_);
    v_x_1043__boxed_771_ = lean_unbox_usize(v_x_767_);
    lean_dec(v_x_767_);
    v_res_772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_764_, v_x_765_, v_x_1042__boxed_770_, v_x_1043__boxed_771_, v_x_768_, v_x_769_);
    return v_res_772_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2(
    mut v_00_u03b2_773_: *mut LeanObject,
    mut v_x_774_: *mut LeanObject,
    mut v_x_775_: usize,
    mut v_x_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v___x_777_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_774_, v_x_775_, v_x_776_);
    return v___x_777_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_00_u03b2_778_: *mut LeanObject,
    mut v_x_779_: *mut LeanObject,
    mut v_x_780_: *mut LeanObject,
    mut v_x_781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1059__boxed_782_: usize = 0;
    let mut v_res_783_: *mut LeanObject = core::ptr::null_mut();
    v_x_1059__boxed_782_ = lean_unbox_usize(v_x_780_);
    lean_dec(v_x_780_);
    v_res_783_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_778_, v_x_779_, v_x_1059__boxed_782_, v_x_781_);
    lean_dec_ref(v_x_781_);
    lean_dec_ref(v_x_779_);
    return v_res_783_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2(
    mut v_00_u03b2_784_: *mut LeanObject,
    mut v_n_785_: *mut LeanObject,
    mut v_k_786_: *mut LeanObject,
    mut v_v_787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_788_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_n_785_, v_k_786_, v_v_787_);
    return v___x_788_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3(
    mut v_00_u03b2_789_: *mut LeanObject,
    mut v_depth_790_: usize,
    mut v_keys_791_: *mut LeanObject,
    mut v_vals_792_: *mut LeanObject,
    mut v_heq_793_: *mut LeanObject,
    mut v_i_794_: *mut LeanObject,
    mut v_entries_795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    v___x_796_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_790_, v_keys_791_, v_vals_792_, v_i_794_, v_entries_795_);
    return v___x_796_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_797_: *mut LeanObject,
    mut v_depth_798_: *mut LeanObject,
    mut v_keys_799_: *mut LeanObject,
    mut v_vals_800_: *mut LeanObject,
    mut v_heq_801_: *mut LeanObject,
    mut v_i_802_: *mut LeanObject,
    mut v_entries_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_804_: usize = 0;
    let mut v_res_805_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_804_ = lean_unbox_usize(v_depth_798_);
    lean_dec(v_depth_798_);
    v_res_805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_00_u03b2_797_, v_depth_boxed_804_, v_keys_799_, v_vals_800_, v_heq_801_, v_i_802_, v_entries_803_);
    lean_dec_ref(v_vals_800_);
    lean_dec_ref(v_keys_799_);
    return v_res_805_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6(
    mut v_00_u03b2_806_: *mut LeanObject,
    mut v_keys_807_: *mut LeanObject,
    mut v_vals_808_: *mut LeanObject,
    mut v_heq_809_: *mut LeanObject,
    mut v_i_810_: *mut LeanObject,
    mut v_k_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_807_, v_vals_808_, v_i_810_, v_k_811_);
    return v___x_812_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_813_: *mut LeanObject,
    mut v_keys_814_: *mut LeanObject,
    mut v_vals_815_: *mut LeanObject,
    mut v_heq_816_: *mut LeanObject,
    mut v_i_817_: *mut LeanObject,
    mut v_k_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_819_: *mut LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6(v_00_u03b2_813_, v_keys_814_, v_vals_815_, v_heq_816_, v_i_817_, v_k_818_);
    lean_dec_ref(v_k_818_);
    lean_dec_ref(v_vals_815_);
    lean_dec_ref(v_keys_814_);
    return v_res_819_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_820_: *mut LeanObject,
    mut v_x_821_: *mut LeanObject,
    mut v_x_822_: *mut LeanObject,
    mut v_x_823_: *mut LeanObject,
    mut v_x_824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    v___x_825_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_x_821_, v_x_822_, v_x_823_, v_x_824_);
    return v___x_825_;
}
pub unsafe fn l_Lean_cacheClosedTermName___lam__0(
    mut v_e_826_: *mut LeanObject,
    mut v_n_827_: *mut LeanObject,
    mut v_s_828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constNames_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revExprs_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_834_: u8 = 0;
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_829_ = lean_ctor_get(v_s_828_, 0);
                v_constNames_830_ = lean_ctor_get(v_s_828_, 1);
                v_revExprs_831_ = lean_ctor_get(v_s_828_, 2);
                v_isSharedCheck_841_ = (!lean_is_exclusive(v_s_828_)) as u8;
                if v_isSharedCheck_841_ == 0 {
                    v___x_833_ = v_s_828_;
                    v_isShared_834_ = v_isSharedCheck_841_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revExprs_831_);
                    lean_inc(v_constNames_830_);
                    lean_inc(v_map_829_);
                    lean_dec(v_s_828_);
                    v___x_833_ = lean_box(0);
                    v_isShared_834_ = v_isSharedCheck_841_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_n_827_);
                lean_inc_ref(v_e_826_);
                v___x_835_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(v_map_829_, v_e_826_, v_n_827_);
                v___x_836_ = l_Lean_NameSet_insert(v_constNames_830_, v_n_827_);
                v___x_837_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_837_, 0, v_e_826_);
                lean_ctor_set(v___x_837_, 1, v_revExprs_831_);
                if v_isShared_834_ == 0 {
                    lean_ctor_set(v___x_833_, 2, v___x_837_);
                    lean_ctor_set(v___x_833_, 1, v___x_836_);
                    lean_ctor_set(v___x_833_, 0, v___x_835_);
                    v___x_839_ = v___x_833_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_835_);
                    lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_836_);
                    lean_ctor_set(v_reuseFailAlloc_840_, 2, v___x_837_);
                    v___x_839_ = v_reuseFailAlloc_840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_cacheClosedTermName(
    mut v_env_842_: *mut LeanObject,
    mut v_e_843_: *mut LeanObject,
    mut v_n_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    v___x_845_ = l_Lean_closedTermCacheExt;
    v_asyncMode_846_ = lean_ctor_get(v___x_845_, 2);
    v___f_847_ = lean_alloc_closure(
        l_Lean_cacheClosedTermName___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_847_, 0, v_e_843_);
    lean_closure_set(v___f_847_, 1, v_n_844_);
    v___x_848_ = lean_box(0);
    v___x_849_ = l_Lean_EnvExtension_modifyState___redArg(
        v___x_845_,
        v_env_842_,
        v___f_847_,
        v_asyncMode_846_,
        v___x_848_,
    );
    return v___x_849_;
}
pub unsafe fn l_Lean_getClosedTermName_x3f(
    mut v_env_850_: *mut LeanObject,
    mut v_e_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Lean_closedTermCacheExt;
    v_asyncMode_853_ = lean_ctor_get(v___x_852_, 2);
    v___x_854_ = l_Lean_instInhabitedClosedTermCache_default;
    v___x_855_ = lean_box(0);
    v___x_856_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_854_,
        v___x_852_,
        v_env_850_,
        v_asyncMode_853_,
        v___x_855_,
    );
    v_map_857_ = lean_ctor_get(v___x_856_, 0);
    lean_inc_ref(v_map_857_);
    lean_dec(v___x_856_);
    v___x_858_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(v_map_857_, v_e_851_);
    lean_dec_ref(v_map_857_);
    return v___x_858_;
}
pub unsafe fn l_Lean_getClosedTermName_x3f___boxed(
    mut v_env_859_: *mut LeanObject,
    mut v_e_860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_861_: *mut LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Lean_getClosedTermName_x3f(v_env_859_, v_e_860_);
    lean_dec_ref(v_e_860_);
    return v_res_861_;
}
pub unsafe fn l_Lean_isClosedTermName(
    mut v_env_862_: *mut LeanObject,
    mut v_n_863_: *mut LeanObject,
) -> u8 {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constNames_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: u8 = 0;
    v___x_864_ = l_Lean_closedTermCacheExt;
    v_asyncMode_865_ = lean_ctor_get(v___x_864_, 2);
    v___x_866_ = l_Lean_instInhabitedClosedTermCache_default;
    v___x_867_ = lean_box(0);
    v___x_868_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_866_,
        v___x_864_,
        v_env_862_,
        v_asyncMode_865_,
        v___x_867_,
    );
    v_constNames_869_ = lean_ctor_get(v___x_868_, 1);
    lean_inc(v_constNames_869_);
    lean_dec(v___x_868_);
    v___x_870_ = l_Lean_NameSet_contains(v_constNames_869_, v_n_863_);
    lean_dec(v_constNames_869_);
    return v___x_870_;
}
pub unsafe fn l_Lean_isClosedTermName___boxed(
    mut v_env_871_: *mut LeanObject,
    mut v_n_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_873_: u8 = 0;
    let mut v_r_874_: *mut LeanObject = core::ptr::null_mut();
    v_res_873_ = l_Lean_isClosedTermName(v_env_871_, v_n_872_);
    lean_dec(v_n_872_);
    v_r_874_ = lean_box((v_res_873_) as usize);
    return v_r_874_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_ClosedTermCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedClosedTermCache_default =
        _init_l_Lean_instInhabitedClosedTermCache_default();
    lean_mark_persistent(l_Lean_instInhabitedClosedTermCache_default);
    l_Lean_instInhabitedClosedTermCache = _init_l_Lean_instInhabitedClosedTermCache();
    lean_mark_persistent(l_Lean_instInhabitedClosedTermCache);
    res = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_closedTermCacheExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_closedTermCacheExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_ClosedTermCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_ClosedTermCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ClosedTermCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_ClosedTermCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_ClosedTermCache(builtin);
}
