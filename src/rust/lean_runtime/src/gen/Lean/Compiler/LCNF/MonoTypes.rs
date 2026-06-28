// Lean compiler output
// Module: Lean.Compiler.LCNF.MonoTypes
// Imports: Lean.Compiler.LCNF.Util Lean.Compiler.LCNF.BaseTypes Lean.Compiler.LCNF.Irrelevant
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1,
    l_List_lengthTR___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::BaseTypes::{
    initialize_Lean_Compiler_LCNF_BaseTypes, l_Lean_Compiler_LCNF_getOtherDeclBaseType,
    runtime_initialize_Lean_Compiler_LCNF_BaseTypes,
};
use crate::r#gen::Lean::Compiler::LCNF::Irrelevant::{
    initialize_Lean_Compiler_LCNF_Irrelevant,
    l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f,
    runtime_initialize_Lean_Compiler_LCNF_Irrelevant,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_anyExpr, l_Lean_Compiler_LCNF_erasedExpr,
    l_Lean_Compiler_LCNF_instantiateForall, l_Lean_Expr_isErased,
};
use crate::r#gen::Lean::Compiler::LCNF::Util::{
    initialize_Lean_Compiler_LCNF_Util, runtime_initialize_Lean_Compiler_LCNF_Util,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_instInhabitedCoreM___lam__0___boxed;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_headBeta, l_Lean_Expr_mdata___override, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProp, l_Lean_Meta_isTypeFormerType};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__0_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__1_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 97, 112, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_getParamTypes___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Compiler_LCNF_getParamTypes___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getParamTypes___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_toMonoType___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_toMonoType___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toMonoType___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 99, 69, 114, 97, 115, 101, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_toMonoType___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toMonoType___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 77, 111, 110, 111, 84, 121, 112, 101, 115, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 116, 111, 77, 111, 110, 111, 84, 121, 112, 101, 46, 118, 105, 115, 105, 116, 65, 112, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 77, 111, 110, 111, 84, 121, 112, 101, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 99, 65, 110, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__2_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__1(
    mut v___x_986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    v___x_988_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_988_, 0, v___x_986_);
    return v___x_988_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v___x_989_: *mut LeanObject,
    mut v___y_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_991_: *mut LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__1(v___x_989_);
    return v_res_991_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__2(
    mut v_msg_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    v___x_993_ = lean_box(0);
    v___x_994_ = lean_panic_fn_borrowed(v___x_993_, v_msg_992_);
    return v___x_994_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_995_: *mut LeanObject,
    mut v_x_996_: *mut LeanObject,
    mut v_x_997_: *mut LeanObject,
    mut v_x_998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: u8 = 0;
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: u8 = 0;
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_999_ = lean_ctor_get(v_x_995_, 0);
                v_vs_1000_ = lean_ctor_get(v_x_995_, 1);
                v_isSharedCheck_1024_ = (!lean_is_exclusive(v_x_995_)) as u8;
                if v_isSharedCheck_1024_ == 0 {
                    v___x_1002_ = v_x_995_;
                    v_isShared_1003_ = v_isSharedCheck_1024_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1000_);
                    lean_inc(v_ks_999_);
                    lean_dec(v_x_995_);
                    v___x_1002_ = lean_box(0);
                    v_isShared_1003_ = v_isSharedCheck_1024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1004_ = lean_array_get_size(v_ks_999_);
                v___x_1005_ = lean_nat_dec_lt(v_x_996_, v___x_1004_);
                if v___x_1005_ == 0 {
                    lean_dec(v_x_996_);
                    v___x_1006_ = lean_array_push(v_ks_999_, v_x_997_);
                    v___x_1007_ = lean_array_push(v_vs_1000_, v_x_998_);
                    if v_isShared_1003_ == 0 {
                        lean_ctor_set(v___x_1002_, 1, v___x_1007_);
                        lean_ctor_set(v___x_1002_, 0, v___x_1006_);
                        v___x_1009_ = v___x_1002_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1006_);
                        lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1007_);
                        v___x_1009_ = v_reuseFailAlloc_1010_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1011_ = lean_array_fget_borrowed(v_ks_999_, v_x_996_);
                    v___x_1012_ = lean_name_eq(v_x_997_, v_k_x27_1011_);
                    if v___x_1012_ == 0 {
                        if v_isShared_1003_ == 0 {
                            v___x_1014_ = v___x_1002_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_ks_999_);
                            lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_vs_1000_);
                            v___x_1014_ = v_reuseFailAlloc_1018_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1019_ = lean_array_fset(v_ks_999_, v_x_996_, v_x_997_);
                        v___x_1020_ = lean_array_fset(v_vs_1000_, v_x_996_, v_x_998_);
                        lean_dec(v_x_996_);
                        if v_isShared_1003_ == 0 {
                            lean_ctor_set(v___x_1002_, 1, v___x_1020_);
                            lean_ctor_set(v___x_1002_, 0, v___x_1019_);
                            v___x_1022_ = v___x_1002_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1019_);
                            lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1020_);
                            v___x_1022_ = v_reuseFailAlloc_1023_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1009_;
            }
            3 => {
                v___x_1015_ = lean_unsigned_to_nat(1);
                v___x_1016_ = lean_nat_add(v_x_996_, v___x_1015_);
                lean_dec(v_x_996_);
                v_x_995_ = v___x_1014_;
                v_x_996_ = v___x_1016_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1022_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_n_1025_: *mut LeanObject,
    mut v_k_1026_: *mut LeanObject,
    mut v_v_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    v___x_1028_ = lean_unsigned_to_nat(0);
    v___x_1029_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_n_1025_, v___x_1028_, v_k_1026_, v_v_1027_);
    return v___x_1029_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0()
-> u64 {
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: u64 = 0;
    v___x_1030_ = lean_unsigned_to_nat(1723);
    v___x_1031_ = lean_uint64_of_nat(v___x_1030_);
    return v___x_1031_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1032_: usize = 0;
    let mut v___x_1033_: usize = 0;
    let mut v___x_1034_: usize = 0;
    v___x_1032_ = 5usize;
    v___x_1033_ = 1usize;
    v___x_1034_ = lean_usize_shift_left(v___x_1033_, v___x_1032_);
    return v___x_1034_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1035_: usize = 0;
    let mut v___x_1036_: usize = 0;
    let mut v___x_1037_: usize = 0;
    v___x_1035_ = 1usize;
    v___x_1036_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_1037_ = lean_usize_sub(v___x_1036_, v___x_1035_);
    return v___x_1037_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    v___x_1038_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1038_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_1039_: *mut LeanObject,
    mut v_x_1040_: usize,
    mut v_x_1041_: usize,
    mut v_x_1042_: *mut LeanObject,
    mut v_x_1043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: usize = 0;
    let mut v___x_1046_: usize = 0;
    let mut v___x_1047_: usize = 0;
    let mut v___x_1048_: usize = 0;
    let mut v_j_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1054_: u8 = 0;
    let mut v_v_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1068_: u8 = 0;
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut v_node_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1079_: u8 = 0;
    let mut v___x_1080_: usize = 0;
    let mut v___x_1081_: usize = 0;
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1086_: u8 = 0;
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1088_: u8 = 0;
    let mut v_unused_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1099_: u8 = 0;
    let mut v_ks_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: usize = 0;
    let mut v___x_1106_: u8 = 0;
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u8 = 0;
    let mut v_reuseFailAlloc_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1039_) == 0 {
                    v_es_1044_ = lean_ctor_get(v_x_1039_, 0);
                    v___x_1045_ = 5usize;
                    v___x_1046_ = 1usize;
                    v___x_1047_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_1048_ = lean_usize_land(v_x_1040_, v___x_1047_);
                    v_j_1049_ = lean_usize_to_nat(v___x_1048_);
                    v___x_1050_ = lean_array_get_size(v_es_1044_);
                    v___x_1051_ = lean_nat_dec_lt(v_j_1049_, v___x_1050_);
                    if v___x_1051_ == 0 {
                        lean_dec(v_j_1049_);
                        lean_dec(v_x_1043_);
                        lean_dec(v_x_1042_);
                        return v_x_1039_;
                    } else {
                        lean_inc_ref(v_es_1044_);
                        v_isSharedCheck_1088_ = (!lean_is_exclusive(v_x_1039_)) as u8;
                        if v_isSharedCheck_1088_ == 0 {
                            v_unused_1089_ = lean_ctor_get(v_x_1039_, 0);
                            lean_dec(v_unused_1089_);
                            v___x_1053_ = v_x_1039_;
                            v_isShared_1054_ = v_isSharedCheck_1088_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1039_);
                            v___x_1053_ = lean_box(0);
                            v_isShared_1054_ = v_isSharedCheck_1088_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1090_ = lean_ctor_get(v_x_1039_, 0);
                    v_vs_1091_ = lean_ctor_get(v_x_1039_, 1);
                    v_isSharedCheck_1111_ = (!lean_is_exclusive(v_x_1039_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v___x_1093_ = v_x_1039_;
                        v_isShared_1094_ = v_isSharedCheck_1111_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1091_);
                        lean_inc(v_ks_1090_);
                        lean_dec(v_x_1039_);
                        v___x_1093_ = lean_box(0);
                        v_isShared_1094_ = v_isSharedCheck_1111_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1055_ = lean_array_fget(v_es_1044_, v_j_1049_);
                v___x_1056_ = lean_box(0);
                v_xs_x27_1057_ = lean_array_fset(v_es_1044_, v_j_1049_, v___x_1056_);
                match lean_obj_tag(v_v_1055_) {
                    0 => {
                        v_key_1064_ = lean_ctor_get(v_v_1055_, 0);
                        v_val_1065_ = lean_ctor_get(v_v_1055_, 1);
                        v_isSharedCheck_1075_ = (!lean_is_exclusive(v_v_1055_)) as u8;
                        if v_isSharedCheck_1075_ == 0 {
                            v___x_1067_ = v_v_1055_;
                            v_isShared_1068_ = v_isSharedCheck_1075_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1065_);
                            lean_inc(v_key_1064_);
                            lean_dec(v_v_1055_);
                            v___x_1067_ = lean_box(0);
                            v_isShared_1068_ = v_isSharedCheck_1075_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1076_ = lean_ctor_get(v_v_1055_, 0);
                        v_isSharedCheck_1086_ = (!lean_is_exclusive(v_v_1055_)) as u8;
                        if v_isSharedCheck_1086_ == 0 {
                            v___x_1078_ = v_v_1055_;
                            v_isShared_1079_ = v_isSharedCheck_1086_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1076_);
                            lean_dec(v_v_1055_);
                            v___x_1078_ = lean_box(0);
                            v_isShared_1079_ = v_isSharedCheck_1086_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1087_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1087_, 0, v_x_1042_);
                        lean_ctor_set(v___x_1087_, 1, v_x_1043_);
                        v___y_1059_ = v___x_1087_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1060_ = lean_array_fset(v_xs_x27_1057_, v_j_1049_, v___y_1059_);
                lean_dec(v_j_1049_);
                if v_isShared_1054_ == 0 {
                    lean_ctor_set(v___x_1053_, 0, v___x_1060_);
                    v___x_1062_ = v___x_1053_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
                    v___x_1062_ = v_reuseFailAlloc_1063_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1062_;
            }
            4 => {
                v___x_1069_ = lean_name_eq(v_x_1042_, v_key_1064_);
                if v___x_1069_ == 0 {
                    lean_del_object(v___x_1067_);
                    v___x_1070_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1064_,
                        v_val_1065_,
                        v_x_1042_,
                        v_x_1043_,
                    );
                    v___x_1071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1071_, 0, v___x_1070_);
                    v___y_1059_ = v___x_1071_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1065_);
                    lean_dec(v_key_1064_);
                    if v_isShared_1068_ == 0 {
                        lean_ctor_set(v___x_1067_, 1, v_x_1043_);
                        lean_ctor_set(v___x_1067_, 0, v_x_1042_);
                        v___x_1073_ = v___x_1067_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_x_1042_);
                        lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_x_1043_);
                        v___x_1073_ = v_reuseFailAlloc_1074_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1059_ = v___x_1073_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1080_ = lean_usize_shift_right(v_x_1040_, v___x_1045_);
                v___x_1081_ = lean_usize_add(v_x_1041_, v___x_1046_);
                v___x_1082_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_node_1076_, v___x_1080_, v___x_1081_, v_x_1042_, v_x_1043_);
                if v_isShared_1079_ == 0 {
                    lean_ctor_set(v___x_1078_, 0, v___x_1082_);
                    v___x_1084_ = v___x_1078_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
                    v___x_1084_ = v_reuseFailAlloc_1085_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1059_ = v___x_1084_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1094_ == 0 {
                    v___x_1096_ = v___x_1093_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_ks_1090_);
                    lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_vs_1091_);
                    v___x_1096_ = v_reuseFailAlloc_1110_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1097_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v___x_1096_, v_x_1042_, v_x_1043_);
                v___x_1105_ = 7usize;
                v___x_1106_ = lean_usize_dec_le(v___x_1105_, v_x_1041_);
                if v___x_1106_ == 0 {
                    v___x_1107_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1097_);
                    v___x_1108_ = lean_unsigned_to_nat(4);
                    v___x_1109_ = lean_nat_dec_lt(v___x_1107_, v___x_1108_);
                    lean_dec(v___x_1107_);
                    v___y_1099_ = v___x_1109_;
                    state = 10;
                    continue;
                } else {
                    v___y_1099_ = v___x_1106_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1099_ == 0 {
                    v_ks_1100_ = lean_ctor_get(v_newNode_1097_, 0);
                    lean_inc_ref(v_ks_1100_);
                    v_vs_1101_ = lean_ctor_get(v_newNode_1097_, 1);
                    lean_inc_ref(v_vs_1101_);
                    lean_dec_ref(v_newNode_1097_);
                    v___x_1102_ = lean_unsigned_to_nat(0);
                    v___x_1103_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_1104_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_x_1041_, v_ks_1100_, v_vs_1101_, v___x_1102_, v___x_1103_);
                    lean_dec_ref(v_vs_1101_);
                    lean_dec_ref(v_ks_1100_);
                    return v___x_1104_;
                } else {
                    return v_newNode_1097_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_depth_1112_: usize,
    mut v_keys_1113_: *mut LeanObject,
    mut v_vals_1114_: *mut LeanObject,
    mut v_i_1115_: *mut LeanObject,
    mut v_entries_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: u8 = 0;
    let mut v_k_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1122_: u64 = 0;
    let mut v_h_1123_: usize = 0;
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: usize = 0;
    let mut v___x_1127_: usize = 0;
    let mut v___x_1128_: usize = 0;
    let mut v_h_1129_: usize = 0;
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: u64 = 0;
    let mut v_hash_1134_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1117_ = lean_array_get_size(v_keys_1113_);
                v___x_1118_ = lean_nat_dec_lt(v_i_1115_, v___x_1117_);
                if v___x_1118_ == 0 {
                    lean_dec(v_i_1115_);
                    return v_entries_1116_;
                } else {
                    v_k_1119_ = lean_array_fget_borrowed(v_keys_1113_, v_i_1115_);
                    v_v_1120_ = lean_array_fget_borrowed(v_vals_1114_, v_i_1115_);
                    if lean_obj_tag(v_k_1119_) == 0 {
                        v___x_1133_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                        v___y_1122_ = v___x_1133_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1134_ = lean_ctor_get_uint64(
                            v_k_1119_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_1122_ = v_hash_1134_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_1123_ = lean_uint64_to_usize(v___y_1122_);
                v___x_1124_ = 5usize;
                v___x_1125_ = lean_unsigned_to_nat(1);
                v___x_1126_ = 1usize;
                v___x_1127_ = lean_usize_sub(v_depth_1112_, v___x_1126_);
                v___x_1128_ = lean_usize_mul(v___x_1124_, v___x_1127_);
                v_h_1129_ = lean_usize_shift_right(v_h_1123_, v___x_1128_);
                v___x_1130_ = lean_nat_add(v_i_1115_, v___x_1125_);
                lean_dec(v_i_1115_);
                lean_inc(v_v_1120_);
                lean_inc(v_k_1119_);
                v___x_1131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_entries_1116_, v_h_1129_, v_depth_1112_, v_k_1119_, v_v_1120_);
                v_i_1115_ = v___x_1130_;
                v_entries_1116_ = v___x_1131_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_depth_1135_: *mut LeanObject,
    mut v_keys_1136_: *mut LeanObject,
    mut v_vals_1137_: *mut LeanObject,
    mut v_i_1138_: *mut LeanObject,
    mut v_entries_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1140_: usize = 0;
    let mut v_res_1141_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1140_ = lean_unbox_usize(v_depth_1135_);
    lean_dec(v_depth_1135_);
    v_res_1141_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_1140_, v_keys_1136_, v_vals_1137_, v_i_1138_, v_entries_1139_);
    lean_dec_ref(v_vals_1137_);
    lean_dec_ref(v_keys_1136_);
    return v_res_1141_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1142_: *mut LeanObject,
    mut v_x_1143_: *mut LeanObject,
    mut v_x_1144_: *mut LeanObject,
    mut v_x_1145_: *mut LeanObject,
    mut v_x_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_665__boxed_1147_: usize = 0;
    let mut v_x_666__boxed_1148_: usize = 0;
    let mut v_res_1149_: *mut LeanObject = core::ptr::null_mut();
    v_x_665__boxed_1147_ = lean_unbox_usize(v_x_1143_);
    lean_dec(v_x_1143_);
    v_x_666__boxed_1148_ = lean_unbox_usize(v_x_1144_);
    lean_dec(v_x_1144_);
    v_res_1149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1142_, v_x_665__boxed_1147_, v_x_666__boxed_1148_, v_x_1145_, v_x_1146_);
    return v_res_1149_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_1150_: *mut LeanObject,
    mut v_x_1151_: *mut LeanObject,
    mut v_x_1152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1154_: u64 = 0;
    let mut v___x_1155_: usize = 0;
    let mut v___x_1156_: usize = 0;
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: u64 = 0;
    let mut v_hash_1159_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1151_) == 0 {
                    v___x_1158_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                    v___y_1154_ = v___x_1158_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1159_ = lean_ctor_get_uint64(
                        v_x_1151_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1154_ = v_hash_1159_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1155_ = lean_uint64_to_usize(v___y_1154_);
                v___x_1156_ = 1usize;
                v___x_1157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1150_, v___x_1155_, v___x_1156_, v_x_1151_, v_x_1152_);
                return v___x_1157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_keys_1160_: *mut LeanObject,
    mut v_vals_1161_: *mut LeanObject,
    mut v_i_1162_: *mut LeanObject,
    mut v_k_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: u8 = 0;
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u8 = 0;
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1164_ = lean_array_get_size(v_keys_1160_);
                v___x_1165_ = lean_nat_dec_lt(v_i_1162_, v___x_1164_);
                if v___x_1165_ == 0 {
                    lean_dec(v_i_1162_);
                    v___x_1166_ = lean_box(0);
                    return v___x_1166_;
                } else {
                    v_k_x27_1167_ = lean_array_fget_borrowed(v_keys_1160_, v_i_1162_);
                    v___x_1168_ = lean_name_eq(v_k_1163_, v_k_x27_1167_);
                    if v___x_1168_ == 0 {
                        v___x_1169_ = lean_unsigned_to_nat(1);
                        v___x_1170_ = lean_nat_add(v_i_1162_, v___x_1169_);
                        lean_dec(v_i_1162_);
                        v_i_1162_ = v___x_1170_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1172_ = lean_array_fget_borrowed(v_vals_1161_, v_i_1162_);
                        lean_dec(v_i_1162_);
                        lean_inc(v___x_1172_);
                        v___x_1173_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1173_, 0, v___x_1172_);
                        return v___x_1173_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_keys_1174_: *mut LeanObject,
    mut v_vals_1175_: *mut LeanObject,
    mut v_i_1176_: *mut LeanObject,
    mut v_k_1177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1178_: *mut LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_keys_1174_, v_vals_1175_, v_i_1176_, v_k_1177_);
    lean_dec(v_k_1177_);
    lean_dec_ref(v_vals_1175_);
    lean_dec_ref(v_keys_1174_);
    return v_res_1178_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_x_1179_: *mut LeanObject,
    mut v_x_1180_: usize,
    mut v_x_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: usize = 0;
    let mut v___x_1185_: usize = 0;
    let mut v___x_1186_: usize = 0;
    let mut v_j_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: u8 = 0;
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: usize = 0;
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1179_) == 0 {
                    v_es_1182_ = lean_ctor_get(v_x_1179_, 0);
                    v___x_1183_ = lean_box(2);
                    v___x_1184_ = 5usize;
                    v___x_1185_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_1186_ = lean_usize_land(v_x_1180_, v___x_1185_);
                    v_j_1187_ = lean_usize_to_nat(v___x_1186_);
                    v___x_1188_ = lean_array_get_borrowed(v___x_1183_, v_es_1182_, v_j_1187_);
                    lean_dec(v_j_1187_);
                    match lean_obj_tag(v___x_1188_) {
                        0 => {
                            v_key_1189_ = lean_ctor_get(v___x_1188_, 0);
                            v_val_1190_ = lean_ctor_get(v___x_1188_, 1);
                            v___x_1191_ = lean_name_eq(v_x_1181_, v_key_1189_);
                            if v___x_1191_ == 0 {
                                v___x_1192_ = lean_box(0);
                                return v___x_1192_;
                            } else {
                                lean_inc(v_val_1190_);
                                v___x_1193_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1193_, 0, v_val_1190_);
                                return v___x_1193_;
                            }
                        }
                        1 => {
                            v_node_1194_ = lean_ctor_get(v___x_1188_, 0);
                            v___x_1195_ = lean_usize_shift_right(v_x_1180_, v___x_1184_);
                            v_x_1179_ = v_node_1194_;
                            v_x_1180_ = v___x_1195_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1197_ = lean_box(0);
                            return v___x_1197_;
                        }
                    }
                } else {
                    v_ks_1198_ = lean_ctor_get(v_x_1179_, 0);
                    v_vs_1199_ = lean_ctor_get(v_x_1179_, 1);
                    v___x_1200_ = lean_unsigned_to_nat(0);
                    v___x_1201_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_ks_1198_, v_vs_1199_, v___x_1200_, v_x_1181_);
                    return v___x_1201_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_1202_: *mut LeanObject,
    mut v_x_1203_: *mut LeanObject,
    mut v_x_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_876__boxed_1205_: usize = 0;
    let mut v_res_1206_: *mut LeanObject = core::ptr::null_mut();
    v_x_876__boxed_1205_ = lean_unbox_usize(v_x_1203_);
    lean_dec(v_x_1203_);
    v_res_1206_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_1202_, v_x_876__boxed_1205_, v_x_1204_);
    lean_dec(v_x_1204_);
    lean_dec_ref(v_x_1202_);
    return v_res_1206_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_x_1207_: *mut LeanObject,
    mut v_x_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1210_: u64 = 0;
    let mut v___x_1211_: usize = 0;
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: u64 = 0;
    let mut v_hash_1214_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1208_) == 0 {
                    v___x_1213_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                    v___y_1210_ = v___x_1213_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1214_ = lean_ctor_get_uint64(
                        v_x_1208_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1210_ = v_hash_1214_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1211_ = lean_uint64_to_usize(v___y_1210_);
                v___x_1212_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_1207_, v___x_1211_, v_x_1208_);
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(
    mut v_x_1215_: *mut LeanObject,
    mut v_x_1216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1217_: *mut LeanObject = core::ptr::null_mut();
    v_res_1217_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_1215_, v_x_1216_);
    lean_dec(v_x_1216_);
    lean_dec_ref(v_x_1215_);
    return v_res_1217_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__2;
    v___x_1222_ = lean_unsigned_to_nat(14);
    v___x_1223_ = lean_unsigned_to_nat(177);
    v___x_1224_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__1;
    v___x_1225_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__0;
    v___x_1226_ = l_mkPanicMessageWithDecl(
        v___x_1225_,
        v___x_1224_,
        v___x_1223_,
        v___x_1222_,
        v___x_1221_,
    );
    return v___x_1226_;
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3(
    mut v_newState_1227_: *mut LeanObject,
    mut v_x_1228_: *mut LeanObject,
    mut v_x_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1234_: u8 = 0;
    let mut v_fst_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1239_: u8 = 0;
    let mut v_snd_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut v_isSharedCheck_1256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1229_) == 0 {
                    return v_x_1228_;
                } else {
                    v_head_1230_ = lean_ctor_get(v_x_1229_, 0);
                    v_tail_1231_ = lean_ctor_get(v_x_1229_, 1);
                    v_isSharedCheck_1256_ = (!lean_is_exclusive(v_x_1229_)) as u8;
                    if v_isSharedCheck_1256_ == 0 {
                        v___x_1233_ = v_x_1229_;
                        v_isShared_1234_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1231_);
                        lean_inc(v_head_1230_);
                        lean_dec(v_x_1229_);
                        v___x_1233_ = lean_box(0);
                        v_isShared_1234_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1235_ = lean_ctor_get(v_x_1228_, 0);
                v_snd_1236_ = lean_ctor_get(v_x_1228_, 1);
                v_isSharedCheck_1255_ = (!lean_is_exclusive(v_x_1228_)) as u8;
                if v_isSharedCheck_1255_ == 0 {
                    v___x_1238_ = v_x_1228_;
                    v_isShared_1239_ = v_isSharedCheck_1255_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1236_);
                    lean_inc(v_fst_1235_);
                    lean_dec(v_x_1228_);
                    v___x_1238_ = lean_box(0);
                    v_isShared_1239_ = v_isSharedCheck_1255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_1240_ = lean_ctor_get(v_newState_1227_, 1);
                lean_inc(v_head_1230_);
                if v_isShared_1234_ == 0 {
                    lean_ctor_set(v___x_1233_, 1, v_fst_1235_);
                    v___x_1242_ = v___x_1233_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_head_1230_);
                    lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_fst_1235_);
                    v___x_1242_ = v_reuseFailAlloc_1254_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1250_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_1240_, v_head_1230_);
                if lean_obj_tag(v___x_1250_) == 0 {
                    v___x_1251_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3);
                    v___x_1252_ = l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__2(v___x_1251_);
                    v___y_1244_ = v___x_1252_;
                    state = 4;
                    continue;
                } else {
                    v_val_1253_ = lean_ctor_get(v___x_1250_, 0);
                    lean_inc(v_val_1253_);
                    lean_dec_ref_known(v___x_1250_, 1);
                    v___y_1244_ = v_val_1253_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1245_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_1236_, v_head_1230_, v___y_1244_);
                if v_isShared_1239_ == 0 {
                    lean_ctor_set(v___x_1238_, 1, v___x_1245_);
                    lean_ctor_set(v___x_1238_, 0, v___x_1242_);
                    v___x_1247_ = v___x_1238_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1242_);
                    lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1245_);
                    v___x_1247_ = v_reuseFailAlloc_1249_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_1228_ = v___x_1247_;
                v_x_1229_ = v_tail_1231_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___boxed(
    mut v_newState_1257_: *mut LeanObject,
    mut v_x_1258_: *mut LeanObject,
    mut v_x_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1260_: *mut LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3(v_newState_1257_, v_x_1258_, v_x_1259_);
    lean_dec_ref(v_newState_1257_);
    return v_res_1260_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0(
    mut v_oldState_1263_: *mut LeanObject,
    mut v_newState_1264_: *mut LeanObject,
    mut v_x_1265_: *mut LeanObject,
    mut v_s_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1267_ = lean_ctor_get(v_newState_1264_, 0);
    v_fst_1268_ = lean_ctor_get(v_oldState_1263_, 0);
    v___x_1269_ = l_List_lengthTR___redArg(v_fst_1267_);
    v___x_1270_ = l_List_lengthTR___redArg(v_fst_1268_);
    v___x_1271_ = lean_nat_sub(v___x_1269_, v___x_1270_);
    lean_dec(v___x_1270_);
    lean_dec(v___x_1269_);
    v___x_1272_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0___closed__0;
    lean_inc(v_fst_1267_);
    v_newEntries_1273_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        lean_box(0),
        v_fst_1267_,
        v_fst_1267_,
        v___x_1271_,
        v___x_1272_,
    );
    v___x_1274_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3(v_newState_1264_, v_s_1266_, v_newEntries_1273_);
    lean_dec_ref(v_newState_1264_);
    return v___x_1274_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0___boxed(
    mut v_oldState_1275_: *mut LeanObject,
    mut v_newState_1276_: *mut LeanObject,
    mut v_x_1277_: *mut LeanObject,
    mut v_s_1278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1279_: *mut LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0(v_oldState_1275_, v_newState_1276_, v_x_1277_, v_s_1278_);
    lean_dec(v_x_1277_);
    lean_dec_ref(v_oldState_1275_);
    return v_res_1279_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1281_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    v___x_1282_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__1);
    v___x_1283_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1283_, 0, v___x_1282_);
    return v___x_1283_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    v___x_1284_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__2);
    v___x_1285_ = lean_box(0);
    v___x_1286_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1286_, 0, v___x_1285_);
    lean_ctor_set(v___x_1286_, 1, v___x_1284_);
    return v___x_1286_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1288_: *mut LeanObject = core::ptr::null_mut();
    v___x_1287_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__3);
    v___f_1288_ = lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1288_, 0, v___x_1287_);
    return v___f_1288_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0()
-> *mut LeanObject {
    let mut v___f_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1299_: u8 = 0;
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_a_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1292_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__4_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__4);
                v___x_1293_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___closed__5;
                v___x_1294_ = lean_box(0);
                v___x_1295_ =
                    l_Lean_registerEnvExtension___redArg(v___f_1292_, v___x_1293_, v___x_1294_);
                if lean_obj_tag(v___x_1295_) == 0 {
                    v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
                    v_isSharedCheck_1303_ = (!lean_is_exclusive(v___x_1295_)) as u8;
                    if v_isSharedCheck_1303_ == 0 {
                        v___x_1298_ = v___x_1295_;
                        v_isShared_1299_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1296_);
                        lean_dec(v___x_1295_);
                        v___x_1298_ = lean_box(0);
                        v_isShared_1299_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1304_ = lean_ctor_get(v___x_1295_, 0);
                    v_isSharedCheck_1311_ = (!lean_is_exclusive(v___x_1295_)) as u8;
                    if v_isSharedCheck_1311_ == 0 {
                        v___x_1306_ = v___x_1295_;
                        v_isShared_1307_ = v_isSharedCheck_1311_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1304_);
                        lean_dec(v___x_1295_);
                        v___x_1306_ = lean_box(0);
                        v_isShared_1307_ = v_isSharedCheck_1311_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1299_ == 0 {
                    v___x_1301_ = v___x_1298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
                    v___x_1301_ = v_reuseFailAlloc_1302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1301_;
            }
            3 => {
                if v_isShared_1307_ == 0 {
                    v___x_1309_ = v___x_1306_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
                    v___x_1309_ = v_reuseFailAlloc_1310_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___boxed(
    mut v_a_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1313_: *mut LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0();
    return v_res_1313_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0();
    return v___x_1315_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2____boxed(
    mut v_a_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1317_: *mut LeanObject = core::ptr::null_mut();
    v_res_1317_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2_();
    return v_res_1317_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_1318_: *mut LeanObject,
    mut v_x_1319_: *mut LeanObject,
    mut v_x_1320_: *mut LeanObject,
    mut v_x_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1319_, v_x_1320_, v_x_1321_);
    return v___x_1322_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_1323_: *mut LeanObject,
    mut v_x_1324_: *mut LeanObject,
    mut v_x_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1326_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_1324_, v_x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_00_u03b2_1327_: *mut LeanObject,
    mut v_x_1328_: *mut LeanObject,
    mut v_x_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1330_: *mut LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b2_1327_, v_x_1328_, v_x_1329_);
    lean_dec(v_x_1329_);
    lean_dec_ref(v_x_1328_);
    return v_res_1330_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_1331_: *mut LeanObject,
    mut v_x_1332_: *mut LeanObject,
    mut v_x_1333_: usize,
    mut v_x_1334_: usize,
    mut v_x_1335_: *mut LeanObject,
    mut v_x_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    v___x_1337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1332_, v_x_1333_, v_x_1334_, v_x_1335_, v_x_1336_);
    return v___x_1337_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1338_: *mut LeanObject,
    mut v_x_1339_: *mut LeanObject,
    mut v_x_1340_: *mut LeanObject,
    mut v_x_1341_: *mut LeanObject,
    mut v_x_1342_: *mut LeanObject,
    mut v_x_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1141__boxed_1344_: usize = 0;
    let mut v_x_1142__boxed_1345_: usize = 0;
    let mut v_res_1346_: *mut LeanObject = core::ptr::null_mut();
    v_x_1141__boxed_1344_ = lean_unbox_usize(v_x_1340_);
    lean_dec(v_x_1340_);
    v_x_1142__boxed_1345_ = lean_unbox_usize(v_x_1341_);
    lean_dec(v_x_1341_);
    v_res_1346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1338_, v_x_1339_, v_x_1141__boxed_1344_, v_x_1142__boxed_1345_, v_x_1342_, v_x_1343_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_1347_: *mut LeanObject,
    mut v_x_1348_: *mut LeanObject,
    mut v_x_1349_: usize,
    mut v_x_1350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_1348_, v_x_1349_, v_x_1350_);
    return v___x_1351_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_1352_: *mut LeanObject,
    mut v_x_1353_: *mut LeanObject,
    mut v_x_1354_: *mut LeanObject,
    mut v_x_1355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1158__boxed_1356_: usize = 0;
    let mut v_res_1357_: *mut LeanObject = core::ptr::null_mut();
    v_x_1158__boxed_1356_ = lean_unbox_usize(v_x_1354_);
    lean_dec(v_x_1354_);
    v_res_1357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_1352_, v_x_1353_, v_x_1158__boxed_1356_, v_x_1355_);
    lean_dec(v_x_1355_);
    lean_dec_ref(v_x_1353_);
    return v_res_1357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_1358_: *mut LeanObject,
    mut v_n_1359_: *mut LeanObject,
    mut v_k_1360_: *mut LeanObject,
    mut v_v_1361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_n_1359_, v_k_1360_, v_v_1361_);
    return v___x_1362_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_1363_: *mut LeanObject,
    mut v_depth_1364_: usize,
    mut v_keys_1365_: *mut LeanObject,
    mut v_vals_1366_: *mut LeanObject,
    mut v_heq_1367_: *mut LeanObject,
    mut v_i_1368_: *mut LeanObject,
    mut v_entries_1369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    v___x_1370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_depth_1364_, v_keys_1365_, v_vals_1366_, v_i_1368_, v_entries_1369_);
    return v___x_1370_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_1371_: *mut LeanObject,
    mut v_depth_1372_: *mut LeanObject,
    mut v_keys_1373_: *mut LeanObject,
    mut v_vals_1374_: *mut LeanObject,
    mut v_heq_1375_: *mut LeanObject,
    mut v_i_1376_: *mut LeanObject,
    mut v_entries_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1378_: usize = 0;
    let mut v_res_1379_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1378_ = lean_unbox_usize(v_depth_1372_);
    lean_dec(v_depth_1372_);
    v_res_1379_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1371_, v_depth_boxed_1378_, v_keys_1373_, v_vals_1374_, v_heq_1375_, v_i_1376_, v_entries_1377_);
    lean_dec_ref(v_vals_1374_);
    lean_dec_ref(v_keys_1373_);
    return v_res_1379_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_1380_: *mut LeanObject,
    mut v_keys_1381_: *mut LeanObject,
    mut v_vals_1382_: *mut LeanObject,
    mut v_heq_1383_: *mut LeanObject,
    mut v_i_1384_: *mut LeanObject,
    mut v_k_1385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    v___x_1386_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_keys_1381_, v_vals_1382_, v_i_1384_, v_k_1385_);
    return v___x_1386_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_1387_: *mut LeanObject,
    mut v_keys_1388_: *mut LeanObject,
    mut v_vals_1389_: *mut LeanObject,
    mut v_heq_1390_: *mut LeanObject,
    mut v_i_1391_: *mut LeanObject,
    mut v_k_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1393_: *mut LeanObject = core::ptr::null_mut();
    v_res_1393_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(v_00_u03b2_1387_, v_keys_1388_, v_vals_1389_, v_heq_1390_, v_i_1391_, v_k_1392_);
    lean_dec(v_k_1392_);
    lean_dec_ref(v_vals_1389_);
    lean_dec_ref(v_keys_1388_);
    return v_res_1393_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_1394_: *mut LeanObject,
    mut v_x_1395_: *mut LeanObject,
    mut v_x_1396_: *mut LeanObject,
    mut v_x_1397_: *mut LeanObject,
    mut v_x_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1395_, v_x_1396_, v_x_1397_, v_x_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lam__0(
    mut v_type_1400_: *mut LeanObject,
    mut v___y_1401_: *mut LeanObject,
    mut v___y_1402_: *mut LeanObject,
    mut v___y_1403_: *mut LeanObject,
    mut v___y_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_type_1400_);
    v___x_1406_ = l_Lean_Meta_isProp(
        v_type_1400_,
        v___y_1401_,
        v___y_1402_,
        v___y_1403_,
        v___y_1404_,
    );
    if lean_obj_tag(v___x_1406_) == 0 {
        let mut v_a_1407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1408_: u8 = 0;
        v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
        lean_inc(v_a_1407_);
        v___x_1408_ = (lean_unbox(v_a_1407_) as u8);
        lean_dec(v_a_1407_);
        if v___x_1408_ == 0 {
            let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1406_, 1);
            v___x_1409_ = l_Lean_Meta_isTypeFormerType(
                v_type_1400_,
                v___y_1401_,
                v___y_1402_,
                v___y_1403_,
                v___y_1404_,
            );
            return v___x_1409_;
        } else {
            lean_dec_ref(v_type_1400_);
            return v___x_1406_;
        }
    } else {
        lean_dec_ref(v_type_1400_);
        return v___x_1406_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lam__0___boxed(
    mut v_type_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
    mut v___y_1412_: *mut LeanObject,
    mut v___y_1413_: *mut LeanObject,
    mut v___y_1414_: *mut LeanObject,
    mut v___y_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1416_: *mut LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lam__0(
        v_type_1410_,
        v___y_1411_,
        v___y_1412_,
        v___y_1413_,
        v___y_1414_,
    );
    lean_dec(v___y_1414_);
    lean_dec_ref(v___y_1413_);
    lean_dec(v___y_1412_);
    lean_dec_ref(v___y_1411_);
    return v_res_1416_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(
    mut v_declName_1418_: *mut LeanObject,
    mut v_a_1419_: *mut LeanObject,
    mut v_a_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_irrelevantType_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    v_irrelevantType_1422_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0;
    v___x_1423_ =
        l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt;
    v___x_1424_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(
        v___x_1423_,
        v_irrelevantType_1422_,
        v_declName_1418_,
        v_a_1419_,
        v_a_1420_,
    );
    return v___x_1424_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___boxed(
    mut v_declName_1425_: *mut LeanObject,
    mut v_a_1426_: *mut LeanObject,
    mut v_a_1427_: *mut LeanObject,
    mut v_a_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_res_1429_ =
        l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_declName_1425_, v_a_1426_, v_a_1427_);
    lean_dec(v_a_1427_);
    lean_dec_ref(v_a_1426_);
    return v_res_1429_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(
    mut v_type_1430_: *mut LeanObject,
    mut v_r_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderType_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_type_1430_) == 7 {
                    v_binderType_1432_ = lean_ctor_get(v_type_1430_, 1);
                    lean_inc_ref(v_binderType_1432_);
                    v_body_1433_ = lean_ctor_get(v_type_1430_, 2);
                    lean_inc_ref(v_body_1433_);
                    lean_dec_ref_known(v_type_1430_, 3);
                    v___x_1434_ = lean_array_push(v_r_1431_, v_binderType_1432_);
                    v_type_1430_ = v_body_1433_;
                    v_r_1431_ = v___x_1434_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_type_1430_);
                    return v_r_1431_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getParamTypes(
    mut v_type_1438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Lean_Compiler_LCNF_getParamTypes___closed__0;
    v___x_1440_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_getParamTypes_go(
        v_type_1438_,
        v___x_1439_,
    );
    return v___x_1440_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(
    mut v_msg_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494__overap_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    v___f_1446_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___closed__0;
    v___x_3494__overap_1447_ = lean_panic_fn_borrowed(v___f_1446_, v_msg_1442_);
    lean_inc(v___y_1444_);
    lean_inc_ref(v___y_1443_);
    v___x_1448_ = lean_apply_3(
        v___x_3494__overap_1447_,
        v___y_1443_,
        v___y_1444_,
        lean_box(0),
    );
    return v___x_1448_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___boxed(
    mut v_msg_1449_: *mut LeanObject,
    mut v___y_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
    mut v___y_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1453_: *mut LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(v_msg_1449_, v___y_1450_, v___y_1451_);
    lean_dec(v___y_1451_);
    lean_dec_ref(v___y_1450_);
    return v_res_1453_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toMonoType___closed__0() -> *mut LeanObject {
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1455_: *mut LeanObject = core::ptr::null_mut();
    v___x_1454_ = lean_box(0);
    v_dummy_1455_ = l_Lean_Expr_sort___override(v___x_1454_);
    return v_dummy_1455_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toMonoType(
    mut v_type_1457_: *mut LeanObject,
    mut v_a_1458_: *mut LeanObject,
    mut v_a_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1473_: u8 = 0;
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___y_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1493_: u8 = 0;
    let mut v_declName_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_1461_ = l_Lean_Expr_headBeta(v_type_1457_);
                match lean_obj_tag(v_type_1461_) {
                    4 => {
                        v___x_1462_ = l_Lean_Compiler_LCNF_getParamTypes___closed__0;
                        v___x_1463_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_type_1461_, v___x_1462_, v_a_1458_, v_a_1459_);
                        return v___x_1463_;
                    }
                    5 => {
                        v_dummy_1464_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toMonoType___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_toMonoType___closed__0_once
                            ),
                            _init_l_Lean_Compiler_LCNF_toMonoType___closed__0,
                        );
                        v_nargs_1465_ = l_Lean_Expr_getAppNumArgs(v_type_1461_);
                        lean_inc(v_nargs_1465_);
                        v___x_1466_ = lean_mk_array(v_nargs_1465_, v_dummy_1464_);
                        v___x_1467_ = lean_unsigned_to_nat(1);
                        v___x_1468_ = lean_nat_sub(v_nargs_1465_, v___x_1467_);
                        lean_dec(v_nargs_1465_);
                        v___x_1469_ =
                            l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(
                                v_type_1461_,
                                v___x_1466_,
                                v___x_1468_,
                                v_a_1458_,
                                v_a_1459_,
                            );
                        return v___x_1469_;
                    }
                    7 => {
                        v_binderName_1470_ = lean_ctor_get(v_type_1461_, 0);
                        lean_inc(v_binderName_1470_);
                        v_binderType_1471_ = lean_ctor_get(v_type_1461_, 1);
                        lean_inc_ref(v_binderType_1471_);
                        v_body_1472_ = lean_ctor_get(v_type_1461_, 2);
                        lean_inc_ref(v_body_1472_);
                        v_binderInfo_1473_ = lean_ctor_get_uint8(
                            v_type_1461_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_dec_ref_known(v_type_1461_, 3);
                        v___x_1474_ = l_Lean_Compiler_LCNF_anyExpr;
                        v___x_1475_ = lean_expr_instantiate1(v_body_1472_, v___x_1474_);
                        lean_dec_ref(v_body_1472_);
                        v___x_1476_ =
                            l_Lean_Compiler_LCNF_toMonoType(v___x_1475_, v_a_1458_, v_a_1459_);
                        if lean_obj_tag(v___x_1476_) == 0 {
                            v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
                            v_isSharedCheck_1503_ = (!lean_is_exclusive(v___x_1476_)) as u8;
                            if v_isSharedCheck_1503_ == 0 {
                                v___x_1479_ = v___x_1476_;
                                v_isShared_1480_ = v_isSharedCheck_1503_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1477_);
                                lean_dec(v___x_1476_);
                                v___x_1479_ = lean_box(0);
                                v_isShared_1480_ = v_isSharedCheck_1503_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_binderType_1471_);
                            lean_dec(v_binderName_1470_);
                            return v___x_1476_;
                        }
                    }
                    3 => {
                        lean_dec_ref_known(v_type_1461_, 1);
                        v___x_1504_ = l_Lean_Compiler_LCNF_erasedExpr;
                        v___x_1505_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1505_, 0, v___x_1504_);
                        return v___x_1505_;
                    }
                    10 => {
                        v_data_1506_ = lean_ctor_get(v_type_1461_, 0);
                        lean_inc(v_data_1506_);
                        v_expr_1507_ = lean_ctor_get(v_type_1461_, 1);
                        lean_inc_ref(v_expr_1507_);
                        lean_dec_ref_known(v_type_1461_, 2);
                        v___x_1508_ =
                            l_Lean_Compiler_LCNF_toMonoType(v_expr_1507_, v_a_1458_, v_a_1459_);
                        if lean_obj_tag(v___x_1508_) == 0 {
                            v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
                            v_isSharedCheck_1517_ = (!lean_is_exclusive(v___x_1508_)) as u8;
                            if v_isSharedCheck_1517_ == 0 {
                                v___x_1511_ = v___x_1508_;
                                v_isShared_1512_ = v_isSharedCheck_1517_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1509_);
                                lean_dec(v___x_1508_);
                                v___x_1511_ = lean_box(0);
                                v_isShared_1512_ = v_isSharedCheck_1517_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_data_1506_);
                            return v___x_1508_;
                        }
                    }
                    _ => {
                        lean_dec_ref(v_type_1461_);
                        v___x_1518_ = l_Lean_Compiler_LCNF_anyExpr;
                        v___x_1519_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1519_, 0, v___x_1518_);
                        return v___x_1519_;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1477_) == 4 {
                    v_declName_1494_ = lean_ctor_get(v_a_1477_, 0);
                    if lean_obj_tag(v_declName_1494_) == 1 {
                        v_pre_1495_ = lean_ctor_get(v_declName_1494_, 0);
                        if lean_obj_tag(v_pre_1495_) == 0 {
                            v_str_1496_ = lean_ctor_get(v_declName_1494_, 1);
                            v___x_1497_ = l_Lean_Compiler_LCNF_toMonoType___closed__1;
                            v___x_1498_ = lean_string_dec_eq(v_str_1496_, v___x_1497_);
                            if v___x_1498_ == 0 {
                                lean_del_object(v___x_1479_);
                                v___y_1482_ = v_a_1458_;
                                v___y_1483_ = v_a_1459_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec_ref_known(v_a_1477_, 2);
                                lean_dec_ref(v_binderType_1471_);
                                lean_dec(v_binderName_1470_);
                                v___x_1499_ = l_Lean_Compiler_LCNF_erasedExpr;
                                if v_isShared_1480_ == 0 {
                                    lean_ctor_set(v___x_1479_, 0, v___x_1499_);
                                    v___x_1501_ = v___x_1479_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
                                    v___x_1501_ = v_reuseFailAlloc_1502_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_1479_);
                            v___y_1482_ = v_a_1458_;
                            v___y_1483_ = v_a_1459_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1479_);
                        v___y_1482_ = v_a_1458_;
                        v___y_1483_ = v_a_1459_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1479_);
                    v___y_1482_ = v_a_1458_;
                    v___y_1483_ = v_a_1459_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1484_ =
                    l_Lean_Compiler_LCNF_toMonoType(v_binderType_1471_, v___y_1482_, v___y_1483_);
                if lean_obj_tag(v___x_1484_) == 0 {
                    v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
                    v_isSharedCheck_1493_ = (!lean_is_exclusive(v___x_1484_)) as u8;
                    if v_isSharedCheck_1493_ == 0 {
                        v___x_1487_ = v___x_1484_;
                        v_isShared_1488_ = v_isSharedCheck_1493_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1485_);
                        lean_dec(v___x_1484_);
                        v___x_1487_ = lean_box(0);
                        v_isShared_1488_ = v_isSharedCheck_1493_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1477_);
                    lean_dec(v_binderName_1470_);
                    return v___x_1484_;
                }
            }
            3 => {
                v___x_1489_ = l_Lean_Expr_forallE___override(
                    v_binderName_1470_,
                    v_a_1485_,
                    v_a_1477_,
                    v_binderInfo_1473_,
                );
                if v_isShared_1488_ == 0 {
                    lean_ctor_set(v___x_1487_, 0, v___x_1489_);
                    v___x_1491_ = v___x_1487_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
                    v___x_1491_ = v_reuseFailAlloc_1492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1491_;
            }
            5 => {
                return v___x_1501_;
            }
            6 => {
                v___x_1513_ = l_Lean_Expr_mdata___override(v_data_1506_, v_a_1509_);
                if v_isShared_1512_ == 0 {
                    lean_ctor_set(v___x_1511_, 0, v___x_1513_);
                    v___x_1515_ = v___x_1511_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
                    v___x_1515_ = v_reuseFailAlloc_1516_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2;
    v___x_1524_ = lean_unsigned_to_nat(50);
    v___x_1525_ = lean_unsigned_to_nat(76);
    v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1;
    v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0;
    v___x_1528_ = l_mkPanicMessageWithDecl(
        v___x_1527_,
        v___x_1526_,
        v___x_1525_,
        v___x_1524_,
        v___x_1523_,
    );
    return v___x_1528_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(
    mut v___x_1529_: u8,
    mut v_as_1530_: *mut LeanObject,
    mut v_sz_1531_: usize,
    mut v_i_1532_: usize,
    mut v_b_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: usize = 0;
    let mut v___x_1540_: usize = 0;
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v___y_1573_: u8 = 0;
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1542_ = lean_usize_dec_lt(v_i_1532_, v_sz_1531_);
                if v___x_1542_ == 0 {
                    v___x_1543_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1543_, 0, v_b_1533_);
                    return v___x_1543_;
                } else {
                    v_fst_1544_ = lean_ctor_get(v_b_1533_, 0);
                    v_snd_1545_ = lean_ctor_get(v_b_1533_, 1);
                    v_isSharedCheck_1594_ = (!lean_is_exclusive(v_b_1533_)) as u8;
                    if v_isSharedCheck_1594_ == 0 {
                        v___x_1547_ = v_b_1533_;
                        v_isShared_1548_ = v_isSharedCheck_1594_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1545_);
                        lean_inc(v_fst_1544_);
                        lean_dec(v_b_1533_);
                        v___x_1547_ = lean_box(0);
                        v_isShared_1548_ = v_isSharedCheck_1594_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1539_ = 1usize;
                v___x_1540_ = lean_usize_add(v_i_1532_, v___x_1539_);
                v_i_1532_ = v___x_1540_;
                v_b_1533_ = v_a_1538_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v_snd_1545_);
                v___x_1549_ = l_Lean_Expr_headBeta(v_snd_1545_);
                if lean_obj_tag(v___x_1549_) == 7 {
                    lean_dec(v_snd_1545_);
                    v_binderType_1550_ = lean_ctor_get(v___x_1549_, 1);
                    lean_inc_ref(v_binderType_1550_);
                    v_body_1551_ = lean_ctor_get(v___x_1549_, 2);
                    lean_inc_ref(v_body_1551_);
                    lean_dec_ref_known(v___x_1549_, 3);
                    v_a_1552_ = lean_array_uget_borrowed(v_as_1530_, v_i_1532_);
                    lean_inc(v_a_1552_);
                    v___x_1553_ = l_Lean_Expr_headBeta(v_a_1552_);
                    match lean_obj_tag(v_binderType_1550_) {
                        4 => {
                            v_declName_1576_ = lean_ctor_get(v_binderType_1550_, 0);
                            lean_inc(v_declName_1576_);
                            lean_dec_ref_known(v_binderType_1550_, 2);
                            if lean_obj_tag(v_declName_1576_) == 1 {
                                v_pre_1577_ = lean_ctor_get(v_declName_1576_, 0);
                                if lean_obj_tag(v_pre_1577_) == 0 {
                                    v_str_1578_ = lean_ctor_get(v_declName_1576_, 1);
                                    lean_inc_ref(v_str_1578_);
                                    lean_dec_ref_known(v_declName_1576_, 2);
                                    v___x_1579_ = l_Lean_Compiler_LCNF_toMonoType___closed__1;
                                    v___x_1580_ = lean_string_dec_eq(v_str_1578_, v___x_1579_);
                                    lean_dec_ref(v_str_1578_);
                                    if v___x_1580_ == 0 {
                                        v___y_1573_ = v___x_1529_;
                                        state = 8;
                                        continue;
                                    } else {
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_declName_1576_, 2);
                                    v___y_1573_ = v___x_1529_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v_declName_1576_);
                                v___y_1573_ = v___x_1529_;
                                state = 8;
                                continue;
                            }
                        }
                        3 => {
                            lean_dec_ref_known(v_binderType_1550_, 1);
                            state = 5;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_binderType_1550_);
                            v___y_1573_ = v___x_1529_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1549_);
                    v___x_1581_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__3);
                    v___x_1582_ = l_panic___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(v___x_1581_, v___y_1534_, v___y_1535_);
                    if lean_obj_tag(v___x_1582_) == 0 {
                        lean_dec_ref_known(v___x_1582_, 1);
                        if v_isShared_1548_ == 0 {
                            v___x_1584_ = v___x_1547_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_fst_1544_);
                            lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_snd_1545_);
                            v___x_1584_ = v_reuseFailAlloc_1585_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1547_);
                        lean_dec(v_snd_1545_);
                        lean_dec(v_fst_1544_);
                        v_a_1586_ = lean_ctor_get(v___x_1582_, 0);
                        v_isSharedCheck_1593_ = (!lean_is_exclusive(v___x_1582_)) as u8;
                        if v_isSharedCheck_1593_ == 0 {
                            v___x_1588_ = v___x_1582_;
                            v_isShared_1589_ = v_isSharedCheck_1593_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1586_);
                            lean_dec(v___x_1582_);
                            v___x_1588_ = lean_box(0);
                            v_isShared_1589_ = v_isSharedCheck_1593_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_1556_ = lean_expr_instantiate1(v_body_1551_, v___x_1553_);
                lean_dec_ref(v___x_1553_);
                lean_dec_ref(v_body_1551_);
                if v_isShared_1548_ == 0 {
                    lean_ctor_set(v___x_1547_, 1, v___x_1556_);
                    lean_ctor_set(v___x_1547_, 0, v_result_1555_);
                    v___x_1558_ = v___x_1547_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_result_1555_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1556_);
                    v___x_1558_ = v_reuseFailAlloc_1559_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_1538_ = v___x_1558_;
                state = 1;
                continue;
            }
            5 => {
                lean_inc_ref(v___x_1553_);
                v___x_1561_ =
                    l_Lean_Compiler_LCNF_toMonoType(v___x_1553_, v___y_1534_, v___y_1535_);
                if lean_obj_tag(v___x_1561_) == 0 {
                    v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
                    lean_inc(v_a_1562_);
                    lean_dec_ref_known(v___x_1561_, 1);
                    v___x_1563_ = l_Lean_Expr_app___override(v_fst_1544_, v_a_1562_);
                    v_result_1555_ = v___x_1563_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v___x_1553_);
                    lean_dec_ref(v_body_1551_);
                    lean_del_object(v___x_1547_);
                    lean_dec(v_fst_1544_);
                    v_a_1564_ = lean_ctor_get(v___x_1561_, 0);
                    v_isSharedCheck_1571_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v___x_1566_ = v___x_1561_;
                        v_isShared_1567_ = v_isSharedCheck_1571_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1564_);
                        lean_dec(v___x_1561_);
                        v___x_1566_ = lean_box(0);
                        v_isShared_1567_ = v_isSharedCheck_1571_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1567_ == 0 {
                    v___x_1569_ = v___x_1566_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
                    v___x_1569_ = v_reuseFailAlloc_1570_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1569_;
            }
            8 => {
                if v___y_1573_ == 0 {
                    v___x_1574_ = l_Lean_Compiler_LCNF_anyExpr;
                    v___x_1575_ = l_Lean_Expr_app___override(v_fst_1544_, v___x_1574_);
                    v_result_1555_ = v___x_1575_;
                    state = 3;
                    continue;
                } else {
                    state = 5;
                    continue;
                }
            }
            9 => {
                v_a_1538_ = v___x_1584_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_1589_ == 0 {
                    v___x_1591_ = v___x_1588_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
                    v___x_1591_ = v_reuseFailAlloc_1592_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4()
-> *mut LeanObject {
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v___x_1600_ = lean_box(0);
    v___x_1601_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__3;
    v___x_1602_ = l_Lean_mkConst(v___x_1601_, v___x_1600_);
    return v___x_1602_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(
    mut v_f_1603_: *mut LeanObject,
    mut v_args_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldIdx_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1640_: usize = 0;
    let mut v___x_1641_: usize = 0;
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1646_: u8 = 0;
    let mut v_fst_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v_a_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1664_: u8 = 0;
    let mut v_a_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1668_: u8 = 0;
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1672_: u8 = 0;
    let mut v_pre_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: u8 = 0;
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_f_1603_) == 4 {
                    v_declName_1608_ = lean_ctor_get(v_f_1603_, 0);
                    lean_inc(v_declName_1608_);
                    v_us_1609_ = lean_ctor_get(v_f_1603_, 1);
                    lean_inc(v_us_1609_);
                    lean_dec_ref_known(v_f_1603_, 2);
                    v___x_1610_ = l_Lean_instInhabitedExpr;
                    if lean_obj_tag(v_declName_1608_) == 1 {
                        v_pre_1673_ = lean_ctor_get(v_declName_1608_, 0);
                        if lean_obj_tag(v_pre_1673_) == 0 {
                            v_str_1674_ = lean_ctor_get(v_declName_1608_, 1);
                            v___x_1675_ = l_Lean_Compiler_LCNF_toMonoType___closed__1;
                            v___x_1676_ = lean_string_dec_eq(v_str_1674_, v___x_1675_);
                            if v___x_1676_ == 0 {
                                v___x_1677_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__0;
                                v___x_1678_ = lean_string_dec_eq(v_str_1674_, v___x_1677_);
                                if v___x_1678_ == 0 {
                                    v___x_1679_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__1;
                                    v___x_1680_ = lean_string_dec_eq(v_str_1674_, v___x_1679_);
                                    if v___x_1680_ == 0 {
                                        v___y_1612_ = v_a_1605_;
                                        v___y_1613_ = v_a_1606_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref_known(v_declName_1608_, 2);
                                        lean_dec(v_us_1609_);
                                        lean_dec_ref(v_args_1604_);
                                        v___x_1681_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4_once), _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___closed__4);
                                        v___x_1682_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_1682_, 0, v___x_1681_);
                                        return v___x_1682_;
                                    }
                                } else {
                                    lean_dec_ref_known(v_declName_1608_, 2);
                                    lean_dec(v_us_1609_);
                                    lean_dec_ref(v_args_1604_);
                                    v___x_1683_ = l_Lean_Compiler_LCNF_anyExpr;
                                    v___x_1684_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1684_, 0, v___x_1683_);
                                    return v___x_1684_;
                                }
                            } else {
                                lean_dec_ref_known(v_declName_1608_, 2);
                                lean_dec(v_us_1609_);
                                lean_dec_ref(v_args_1604_);
                                v___x_1685_ = l_Lean_Compiler_LCNF_erasedExpr;
                                v___x_1686_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1686_, 0, v___x_1685_);
                                return v___x_1686_;
                            }
                        } else {
                            v___y_1612_ = v_a_1605_;
                            v___y_1613_ = v_a_1606_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_1612_ = v_a_1605_;
                        v___y_1613_ = v_a_1606_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_1604_);
                    lean_dec_ref(v_f_1603_);
                    v___x_1687_ = l_Lean_Compiler_LCNF_anyExpr;
                    v___x_1688_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1688_, 0, v___x_1687_);
                    return v___x_1688_;
                }
            }
            1 => {
                lean_inc(v_declName_1608_);
                v___x_1614_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(
                    v_declName_1608_,
                    v___y_1612_,
                    v___y_1613_,
                );
                if lean_obj_tag(v___x_1614_) == 0 {
                    v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
                    lean_inc(v_a_1615_);
                    lean_dec_ref_known(v___x_1614_, 1);
                    if lean_obj_tag(v_a_1615_) == 1 {
                        lean_dec(v_us_1609_);
                        lean_dec(v_declName_1608_);
                        v_val_1616_ = lean_ctor_get(v_a_1615_, 0);
                        lean_inc(v_val_1616_);
                        lean_dec_ref_known(v_a_1615_, 1);
                        v_ctorName_1617_ = lean_ctor_get(v_val_1616_, 0);
                        lean_inc(v_ctorName_1617_);
                        v_numParams_1618_ = lean_ctor_get(v_val_1616_, 1);
                        lean_inc(v_numParams_1618_);
                        v_fieldIdx_1619_ = lean_ctor_get(v_val_1616_, 2);
                        lean_inc(v_fieldIdx_1619_);
                        lean_dec(v_val_1616_);
                        v___x_1620_ = lean_box(0);
                        v___x_1621_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(
                            v_ctorName_1617_,
                            v___x_1620_,
                            v___y_1612_,
                            v___y_1613_,
                        );
                        if lean_obj_tag(v___x_1621_) == 0 {
                            v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
                            lean_inc(v_a_1622_);
                            lean_dec_ref_known(v___x_1621_, 1);
                            v___x_1623_ = lean_unsigned_to_nat(0);
                            v___x_1624_ = l_Array_toSubarray___redArg(
                                v_args_1604_,
                                v___x_1623_,
                                v_numParams_1618_,
                            );
                            v___x_1625_ = l_Subarray_copy___redArg(v___x_1624_);
                            v___x_1626_ = l_Lean_Compiler_LCNF_instantiateForall(
                                v_a_1622_,
                                v___x_1625_,
                                v___y_1612_,
                                v___y_1613_,
                            );
                            lean_dec_ref(v___x_1625_);
                            if lean_obj_tag(v___x_1626_) == 0 {
                                v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
                                lean_inc(v_a_1627_);
                                lean_dec_ref_known(v___x_1626_, 1);
                                v___x_1628_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_1627_);
                                v___x_1629_ =
                                    lean_array_get(v___x_1610_, v___x_1628_, v_fieldIdx_1619_);
                                lean_dec(v_fieldIdx_1619_);
                                lean_dec_ref(v___x_1628_);
                                v___x_1630_ = l_Lean_Compiler_LCNF_toMonoType(
                                    v___x_1629_,
                                    v___y_1612_,
                                    v___y_1613_,
                                );
                                return v___x_1630_;
                            } else {
                                lean_dec(v_fieldIdx_1619_);
                                return v___x_1626_;
                            }
                        } else {
                            lean_dec(v_fieldIdx_1619_);
                            lean_dec(v_numParams_1618_);
                            lean_dec_ref(v_args_1604_);
                            return v___x_1621_;
                        }
                    } else {
                        lean_dec(v_a_1615_);
                        v___x_1631_ = lean_box(0);
                        lean_inc(v_declName_1608_);
                        v___x_1632_ = l_Lean_mkConst(v_declName_1608_, v___x_1631_);
                        v___x_1633_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(
                            v_declName_1608_,
                            v_us_1609_,
                            v___y_1612_,
                            v___y_1613_,
                        );
                        if lean_obj_tag(v___x_1633_) == 0 {
                            v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
                            v_isSharedCheck_1664_ = (!lean_is_exclusive(v___x_1633_)) as u8;
                            if v_isSharedCheck_1664_ == 0 {
                                v___x_1636_ = v___x_1633_;
                                v_isShared_1637_ = v_isSharedCheck_1664_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1634_);
                                lean_dec(v___x_1633_);
                                v___x_1636_ = lean_box(0);
                                v_isShared_1637_ = v_isSharedCheck_1664_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1632_);
                            lean_dec_ref(v_args_1604_);
                            return v___x_1633_;
                        }
                    }
                } else {
                    lean_dec(v_us_1609_);
                    lean_dec(v_declName_1608_);
                    lean_dec_ref(v_args_1604_);
                    v_a_1665_ = lean_ctor_get(v___x_1614_, 0);
                    v_isSharedCheck_1672_ = (!lean_is_exclusive(v___x_1614_)) as u8;
                    if v_isSharedCheck_1672_ == 0 {
                        v___x_1667_ = v___x_1614_;
                        v_isShared_1668_ = v_isSharedCheck_1672_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1665_);
                        lean_dec(v___x_1614_);
                        v___x_1667_ = lean_box(0);
                        v_isShared_1668_ = v_isSharedCheck_1672_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1638_ = l_Lean_Expr_isErased(v_a_1634_);
                if v___x_1638_ == 0 {
                    lean_del_object(v___x_1636_);
                    v___x_1639_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1639_, 0, v___x_1632_);
                    lean_ctor_set(v___x_1639_, 1, v_a_1634_);
                    v_sz_1640_ = lean_array_size(v_args_1604_);
                    v___x_1641_ = 0usize;
                    v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(v___x_1638_, v_args_1604_, v_sz_1640_, v___x_1641_, v___x_1639_, v___y_1612_, v___y_1613_);
                    lean_dec_ref(v_args_1604_);
                    if lean_obj_tag(v___x_1642_) == 0 {
                        v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
                        v_isSharedCheck_1651_ = (!lean_is_exclusive(v___x_1642_)) as u8;
                        if v_isSharedCheck_1651_ == 0 {
                            v___x_1645_ = v___x_1642_;
                            v_isShared_1646_ = v_isSharedCheck_1651_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1643_);
                            lean_dec(v___x_1642_);
                            v___x_1645_ = lean_box(0);
                            v_isShared_1646_ = v_isSharedCheck_1651_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1652_ = lean_ctor_get(v___x_1642_, 0);
                        v_isSharedCheck_1659_ = (!lean_is_exclusive(v___x_1642_)) as u8;
                        if v_isSharedCheck_1659_ == 0 {
                            v___x_1654_ = v___x_1642_;
                            v_isShared_1655_ = v_isSharedCheck_1659_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1652_);
                            lean_dec(v___x_1642_);
                            v___x_1654_ = lean_box(0);
                            v_isShared_1655_ = v_isSharedCheck_1659_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1634_);
                    lean_dec_ref(v___x_1632_);
                    lean_dec_ref(v_args_1604_);
                    v___x_1660_ = l_Lean_Compiler_LCNF_erasedExpr;
                    if v_isShared_1637_ == 0 {
                        lean_ctor_set(v___x_1636_, 0, v___x_1660_);
                        v___x_1662_ = v___x_1636_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
                        v___x_1662_ = v_reuseFailAlloc_1663_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_1647_ = lean_ctor_get(v_a_1643_, 0);
                lean_inc(v_fst_1647_);
                lean_dec(v_a_1643_);
                if v_isShared_1646_ == 0 {
                    lean_ctor_set(v___x_1645_, 0, v_fst_1647_);
                    v___x_1649_ = v___x_1645_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_fst_1647_);
                    v___x_1649_ = v_reuseFailAlloc_1650_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1649_;
            }
            5 => {
                if v_isShared_1655_ == 0 {
                    v___x_1657_ = v___x_1654_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
                    v___x_1657_ = v_reuseFailAlloc_1658_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1657_;
            }
            7 => {
                return v___x_1662_;
            }
            8 => {
                if v_isShared_1668_ == 0 {
                    v___x_1670_ = v___x_1667_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
                    v___x_1670_ = v_reuseFailAlloc_1671_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(
    mut v_x_1689_: *mut LeanObject,
    mut v_x_1690_: *mut LeanObject,
    mut v_x_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1689_) == 5 {
                    v_fn_1695_ = lean_ctor_get(v_x_1689_, 0);
                    lean_inc_ref(v_fn_1695_);
                    v_arg_1696_ = lean_ctor_get(v_x_1689_, 1);
                    lean_inc_ref(v_arg_1696_);
                    lean_dec_ref_known(v_x_1689_, 2);
                    v___x_1697_ = lean_array_set(v_x_1690_, v_x_1691_, v_arg_1696_);
                    v___x_1698_ = lean_unsigned_to_nat(1);
                    v___x_1699_ = lean_nat_sub(v_x_1691_, v___x_1698_);
                    lean_dec(v_x_1691_);
                    v_x_1689_ = v_fn_1695_;
                    v_x_1690_ = v___x_1697_;
                    v_x_1691_ = v___x_1699_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_1691_);
                    v___x_1701_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(v_x_1689_, v_x_1690_, v___y_1692_, v___y_1693_);
                    return v___x_1701_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3___boxed(
    mut v_x_1702_: *mut LeanObject,
    mut v_x_1703_: *mut LeanObject,
    mut v_x_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1708_: *mut LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Lean_Expr_withAppAux___at___00Lean_Compiler_LCNF_toMonoType_spec__3(
        v_x_1702_,
        v_x_1703_,
        v_x_1704_,
        v___y_1705_,
        v___y_1706_,
    );
    lean_dec(v___y_1706_);
    lean_dec_ref(v___y_1705_);
    return v_res_1708_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toMonoType___boxed(
    mut v_type_1709_: *mut LeanObject,
    mut v_a_1710_: *mut LeanObject,
    mut v_a_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1713_: *mut LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1709_, v_a_1710_, v_a_1711_);
    lean_dec(v_a_1711_);
    lean_dec_ref(v_a_1710_);
    return v_res_1713_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(
    mut v___x_1714_: *mut LeanObject,
    mut v_as_1715_: *mut LeanObject,
    mut v_sz_1716_: *mut LeanObject,
    mut v_i_1717_: *mut LeanObject,
    mut v_b_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3962__boxed_1722_: u8 = 0;
    let mut v_sz_boxed_1723_: usize = 0;
    let mut v_i_boxed_1724_: usize = 0;
    let mut v_res_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_3962__boxed_1722_ = (lean_unbox(v___x_1714_) as u8);
    v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1716_);
    lean_dec(v_sz_1716_);
    v_i_boxed_1724_ = lean_unbox_usize(v_i_1717_);
    lean_dec(v_i_1717_);
    v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(v___x_3962__boxed_1722_, v_as_1715_, v_sz_boxed_1723_, v_i_boxed_1724_, v_b_1718_, v___y_1719_, v___y_1720_);
    lean_dec(v___y_1720_);
    lean_dec_ref(v___y_1719_);
    lean_dec_ref(v_as_1715_);
    return v_res_1725_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp___boxed(
    mut v_f_1726_: *mut LeanObject,
    mut v_args_1727_: *mut LeanObject,
    mut v_a_1728_: *mut LeanObject,
    mut v_a_1729_: *mut LeanObject,
    mut v_a_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1731_: *mut LeanObject = core::ptr::null_mut();
    v_res_1731_ =
        l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_toMonoType_visitApp(
            v_f_1726_,
            v_args_1727_,
            v_a_1728_,
            v_a_1729_,
        );
    lean_dec(v_a_1729_);
    lean_dec_ref(v_a_1728_);
    return v_res_1731_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___lam__1(
    mut v___x_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    v___x_1734_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1734_, 0, v___x_1732_);
    return v___x_1734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v___x_1735_: *mut LeanObject,
    mut v___y_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1737_: *mut LeanObject = core::ptr::null_mut();
    v_res_1737_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___lam__1(v___x_1735_);
    return v_res_1737_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msg_1738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    v___x_1739_ = l_Lean_instInhabitedExpr;
    v___x_1740_ = lean_panic_fn_borrowed(v___x_1739_, v_msg_1738_);
    return v___x_1740_;
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0_spec__1(
    mut v_newState_1741_: *mut LeanObject,
    mut v_x_1742_: *mut LeanObject,
    mut v_x_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v_fst_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v_snd_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1743_) == 0 {
                    return v_x_1742_;
                } else {
                    v_head_1744_ = lean_ctor_get(v_x_1743_, 0);
                    v_tail_1745_ = lean_ctor_get(v_x_1743_, 1);
                    v_isSharedCheck_1770_ = (!lean_is_exclusive(v_x_1743_)) as u8;
                    if v_isSharedCheck_1770_ == 0 {
                        v___x_1747_ = v_x_1743_;
                        v_isShared_1748_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1745_);
                        lean_inc(v_head_1744_);
                        lean_dec(v_x_1743_);
                        v___x_1747_ = lean_box(0);
                        v_isShared_1748_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1749_ = lean_ctor_get(v_x_1742_, 0);
                v_snd_1750_ = lean_ctor_get(v_x_1742_, 1);
                v_isSharedCheck_1769_ = (!lean_is_exclusive(v_x_1742_)) as u8;
                if v_isSharedCheck_1769_ == 0 {
                    v___x_1752_ = v_x_1742_;
                    v_isShared_1753_ = v_isSharedCheck_1769_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1750_);
                    lean_inc(v_fst_1749_);
                    lean_dec(v_x_1742_);
                    v___x_1752_ = lean_box(0);
                    v_isShared_1753_ = v_isSharedCheck_1769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_1754_ = lean_ctor_get(v_newState_1741_, 1);
                lean_inc(v_head_1744_);
                if v_isShared_1748_ == 0 {
                    lean_ctor_set(v___x_1747_, 1, v_fst_1749_);
                    v___x_1756_ = v___x_1747_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_head_1744_);
                    lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_fst_1749_);
                    v___x_1756_ = v_reuseFailAlloc_1768_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1764_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_1754_, v_head_1744_);
                if lean_obj_tag(v___x_1764_) == 0 {
                    v___x_1765_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__3___closed__3);
                    v___x_1766_ = l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0_spec__0(v___x_1765_);
                    v___y_1758_ = v___x_1766_;
                    state = 4;
                    continue;
                } else {
                    v_val_1767_ = lean_ctor_get(v___x_1764_, 0);
                    lean_inc(v_val_1767_);
                    lean_dec_ref_known(v___x_1764_, 1);
                    v___y_1758_ = v_val_1767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1759_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_1750_, v_head_1744_, v___y_1758_);
                if v_isShared_1753_ == 0 {
                    lean_ctor_set(v___x_1752_, 1, v___x_1759_);
                    lean_ctor_set(v___x_1752_, 0, v___x_1756_);
                    v___x_1761_ = v___x_1752_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1756_);
                    lean_ctor_set(v_reuseFailAlloc_1763_, 1, v___x_1759_);
                    v___x_1761_ = v_reuseFailAlloc_1763_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_1742_ = v___x_1761_;
                v_x_1743_ = v_tail_1745_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_newState_1771_: *mut LeanObject,
    mut v_x_1772_: *mut LeanObject,
    mut v_x_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1774_: *mut LeanObject = core::ptr::null_mut();
    v_res_1774_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0_spec__1(v_newState_1771_, v_x_1772_, v_x_1773_);
    lean_dec_ref(v_newState_1771_);
    return v_res_1774_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___lam__0(
    mut v_oldState_1775_: *mut LeanObject,
    mut v_newState_1776_: *mut LeanObject,
    mut v_x_1777_: *mut LeanObject,
    mut v_s_1778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1779_ = lean_ctor_get(v_newState_1776_, 0);
    v_fst_1780_ = lean_ctor_get(v_oldState_1775_, 0);
    v___x_1781_ = l_List_lengthTR___redArg(v_fst_1779_);
    v___x_1782_ = l_List_lengthTR___redArg(v_fst_1780_);
    v___x_1783_ = lean_nat_sub(v___x_1781_, v___x_1782_);
    lean_dec(v___x_1782_);
    lean_dec(v___x_1781_);
    v___x_1784_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0___lam__0___closed__0;
    lean_inc(v_fst_1779_);
    v_newEntries_1785_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        lean_box(0),
        v_fst_1779_,
        v_fst_1779_,
        v___x_1783_,
        v___x_1784_,
    );
    v___x_1786_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0_spec__1(v_newState_1776_, v_s_1778_, v_newEntries_1785_);
    lean_dec_ref(v_newState_1776_);
    return v___x_1786_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___lam__0___boxed(
    mut v_oldState_1787_: *mut LeanObject,
    mut v_newState_1788_: *mut LeanObject,
    mut v_x_1789_: *mut LeanObject,
    mut v_s_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1791_: *mut LeanObject = core::ptr::null_mut();
    v_res_1791_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___lam__0(v_oldState_1787_, v_newState_1788_, v_x_1789_, v_s_1790_);
    lean_dec(v_x_1789_);
    lean_dec_ref(v_oldState_1787_);
    return v_res_1791_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    v___x_1793_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1793_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    v___x_1794_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__1);
    v___x_1795_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1795_, 0, v___x_1794_);
    return v___x_1795_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__2);
    v___x_1797_ = lean_box(0);
    v___x_1798_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1798_, 0, v___x_1797_);
    lean_ctor_set(v___x_1798_, 1, v___x_1796_);
    return v___x_1798_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1800_: *mut LeanObject = core::ptr::null_mut();
    v___x_1799_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__3);
    v___f_1800_ = lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1800_, 0, v___x_1799_);
    return v___f_1800_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0()
-> *mut LeanObject {
    let mut v___f_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_a_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1804_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__4_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__4);
                v___x_1805_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___closed__5;
                v___x_1806_ = lean_box(0);
                v___x_1807_ =
                    l_Lean_registerEnvExtension___redArg(v___f_1804_, v___x_1805_, v___x_1806_);
                if lean_obj_tag(v___x_1807_) == 0 {
                    v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
                    v_isSharedCheck_1815_ = (!lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1815_ == 0 {
                        v___x_1810_ = v___x_1807_;
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1808_);
                        lean_dec(v___x_1807_);
                        v___x_1810_ = lean_box(0);
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1816_ = lean_ctor_get(v___x_1807_, 0);
                    v_isSharedCheck_1823_ = (!lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v___x_1818_ = v___x_1807_;
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1816_);
                        lean_dec(v___x_1807_);
                        v___x_1818_ = lean_box(0);
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1811_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
                    v___x_1813_ = v_reuseFailAlloc_1814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1813_;
            }
            3 => {
                if v_isShared_1819_ == 0 {
                    v___x_1821_ = v___x_1818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
                    v___x_1821_ = v_reuseFailAlloc_1822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0___boxed(
    mut v_a_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1825_: *mut LeanObject = core::ptr::null_mut();
    v_res_1825_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0();
    return v_res_1825_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1827_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2__spec__0();
    return v___x_1827_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2____boxed(
    mut v_a_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1829_: *mut LeanObject = core::ptr::null_mut();
    v_res_1829_ = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2_();
    return v_res_1829_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    v___x_1832_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__1;
    v___x_1833_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__0;
    v___x_1834_ =
        l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1833_, v___x_1832_);
    return v___x_1834_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    v___x_1835_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__2);
    v___x_1836_ = lean_box(0);
    v___x_1837_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1837_, 0, v___x_1836_);
    lean_ctor_set(v___x_1837_, 1, v___x_1835_);
    return v___x_1837_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(
    mut v_ext_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    v___x_1842_ = lean_st_ref_get(v_a_1840_);
    v_env_1843_ = lean_ctor_get(v___x_1842_, 0);
    lean_inc_ref(v_env_1843_);
    lean_dec(v___x_1842_);
    v_asyncMode_1844_ = lean_ctor_get(v_ext_1838_, 2);
    v___x_1845_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___closed__3);
    v___x_1846_ = lean_box(0);
    v___x_1847_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_1845_,
        v_ext_1838_,
        v_env_1843_,
        v_asyncMode_1844_,
        v___x_1846_,
    );
    v_snd_1848_ = lean_ctor_get(v___x_1847_, 1);
    lean_inc(v_snd_1848_);
    lean_dec(v___x_1847_);
    v___x_1849_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_1848_, v_a_1839_);
    lean_dec(v_snd_1848_);
    v___x_1850_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1850_, 0, v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg___boxed(
    mut v_ext_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1855_: *mut LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v_ext_1851_, v_a_1852_, v_a_1853_);
    lean_dec(v_a_1853_);
    lean_dec(v_a_1852_);
    lean_dec_ref(v_ext_1851_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___lam__0(
    mut v_a_1856_: *mut LeanObject,
    mut v_b_1857_: *mut LeanObject,
    mut v_x_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1859_ = lean_ctor_get(v_x_1858_, 0);
                v_snd_1860_ = lean_ctor_get(v_x_1858_, 1);
                v_isSharedCheck_1869_ = (!lean_is_exclusive(v_x_1858_)) as u8;
                if v_isSharedCheck_1869_ == 0 {
                    v___x_1862_ = v_x_1858_;
                    v_isShared_1863_ = v_isSharedCheck_1869_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1860_);
                    lean_inc(v_fst_1859_);
                    lean_dec(v_x_1858_);
                    v___x_1862_ = lean_box(0);
                    v_isShared_1863_ = v_isSharedCheck_1869_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_1856_);
                v___x_1864_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1864_, 0, v_a_1856_);
                lean_ctor_set(v___x_1864_, 1, v_fst_1859_);
                v___x_1865_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_1860_, v_a_1856_, v_b_1857_);
                if v_isShared_1863_ == 0 {
                    lean_ctor_set(v___x_1862_, 1, v___x_1865_);
                    lean_ctor_set(v___x_1862_, 0, v___x_1864_);
                    v___x_1867_ = v___x_1862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1864_);
                    lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1865_);
                    v___x_1867_ = v_reuseFailAlloc_1868_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1870_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    v___x_1871_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__0_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__0);
    v___x_1872_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1872_, 0, v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1873_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__1);
    v___x_1874_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1874_, 0, v___x_1873_);
    lean_ctor_set(v___x_1874_, 1, v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg(
    mut v_ext_1875_: *mut LeanObject,
    mut v_a_1876_: *mut LeanObject,
    mut v_b_1877_: *mut LeanObject,
    mut v_a_1878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v_asyncMode_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_unused_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1880_ = lean_st_ref_take(v_a_1878_);
                v_env_1881_ = lean_ctor_get(v___x_1880_, 0);
                v_nextMacroScope_1882_ = lean_ctor_get(v___x_1880_, 1);
                v_ngen_1883_ = lean_ctor_get(v___x_1880_, 2);
                v_auxDeclNGen_1884_ = lean_ctor_get(v___x_1880_, 3);
                v_traceState_1885_ = lean_ctor_get(v___x_1880_, 4);
                v_messages_1886_ = lean_ctor_get(v___x_1880_, 6);
                v_infoState_1887_ = lean_ctor_get(v___x_1880_, 7);
                v_snapshotTasks_1888_ = lean_ctor_get(v___x_1880_, 8);
                v_isSharedCheck_1903_ = (!lean_is_exclusive(v___x_1880_)) as u8;
                if v_isSharedCheck_1903_ == 0 {
                    v_unused_1904_ = lean_ctor_get(v___x_1880_, 5);
                    lean_dec(v_unused_1904_);
                    v___x_1890_ = v___x_1880_;
                    v_isShared_1891_ = v_isSharedCheck_1903_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1888_);
                    lean_inc(v_infoState_1887_);
                    lean_inc(v_messages_1886_);
                    lean_inc(v_traceState_1885_);
                    lean_inc(v_auxDeclNGen_1884_);
                    lean_inc(v_ngen_1883_);
                    lean_inc(v_nextMacroScope_1882_);
                    lean_inc(v_env_1881_);
                    lean_dec(v___x_1880_);
                    v___x_1890_ = lean_box(0);
                    v_isShared_1891_ = v_isSharedCheck_1903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_1892_ = lean_ctor_get(v_ext_1875_, 2);
                lean_inc(v_asyncMode_1892_);
                v___f_1893_ = lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_1893_, 0, v_a_1876_);
                lean_closure_set(v___f_1893_, 1, v_b_1877_);
                v___x_1894_ = lean_box(0);
                v___x_1895_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_1875_,
                    v_env_1881_,
                    v___f_1893_,
                    v_asyncMode_1892_,
                    v___x_1894_,
                );
                lean_dec(v_asyncMode_1892_);
                v___x_1896_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___closed__2);
                if v_isShared_1891_ == 0 {
                    lean_ctor_set(v___x_1890_, 5, v___x_1896_);
                    lean_ctor_set(v___x_1890_, 0, v___x_1895_);
                    v___x_1898_ = v___x_1890_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1895_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_nextMacroScope_1882_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_ngen_1883_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_auxDeclNGen_1884_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_traceState_1885_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 5, v___x_1896_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 6, v_messages_1886_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 7, v_infoState_1887_);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 8, v_snapshotTasks_1888_);
                    v___x_1898_ = v_reuseFailAlloc_1902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1899_ = lean_st_ref_set(v_a_1878_, v___x_1898_);
                v___x_1900_ = lean_box(0);
                v___x_1901_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1901_, 0, v___x_1900_);
                return v___x_1901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg___boxed(
    mut v_ext_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_b_1907_: *mut LeanObject,
    mut v_a_1908_: *mut LeanObject,
    mut v_a_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1910_: *mut LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg(v_ext_1905_, v_a_1906_, v_b_1907_, v_a_1908_);
    lean_dec(v_a_1908_);
    return v_res_1910_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getOtherDeclMonoType(
    mut v_declName_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1929_: u8 = 0;
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_unused_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1939_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1915_ = l_Lean_Compiler_LCNF_monoTypeExt;
                v___x_1916_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v___x_1915_, v_declName_1911_, v_a_1913_);
                v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
                v_isSharedCheck_1939_ = (!lean_is_exclusive(v___x_1916_)) as u8;
                if v_isSharedCheck_1939_ == 0 {
                    v___x_1919_ = v___x_1916_;
                    v_isShared_1920_ = v_isSharedCheck_1939_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1917_);
                    lean_dec(v___x_1916_);
                    v___x_1919_ = lean_box(0);
                    v_isShared_1920_ = v_isSharedCheck_1939_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1917_) == 0 {
                    lean_del_object(v___x_1919_);
                    v___x_1921_ = lean_box(0);
                    lean_inc(v_declName_1911_);
                    v___x_1922_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(
                        v_declName_1911_,
                        v___x_1921_,
                        v_a_1912_,
                        v_a_1913_,
                    );
                    if lean_obj_tag(v___x_1922_) == 0 {
                        v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
                        lean_inc(v_a_1923_);
                        lean_dec_ref_known(v___x_1922_, 1);
                        v___x_1924_ =
                            l_Lean_Compiler_LCNF_toMonoType(v_a_1923_, v_a_1912_, v_a_1913_);
                        if lean_obj_tag(v___x_1924_) == 0 {
                            v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
                            lean_inc_n(v_a_1925_, 2);
                            lean_dec_ref_known(v___x_1924_, 1);
                            v___x_1926_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg(v___x_1915_, v_declName_1911_, v_a_1925_, v_a_1913_);
                            v_isSharedCheck_1933_ = (!lean_is_exclusive(v___x_1926_)) as u8;
                            if v_isSharedCheck_1933_ == 0 {
                                v_unused_1934_ = lean_ctor_get(v___x_1926_, 0);
                                lean_dec(v_unused_1934_);
                                v___x_1928_ = v___x_1926_;
                                v_isShared_1929_ = v_isSharedCheck_1933_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_1926_);
                                v___x_1928_ = lean_box(0);
                                v_isShared_1929_ = v_isSharedCheck_1933_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_declName_1911_);
                            return v___x_1924_;
                        }
                    } else {
                        lean_dec(v_declName_1911_);
                        return v___x_1922_;
                    }
                } else {
                    lean_dec(v_declName_1911_);
                    v_val_1935_ = lean_ctor_get(v_a_1917_, 0);
                    lean_inc(v_val_1935_);
                    lean_dec_ref_known(v_a_1917_, 1);
                    if v_isShared_1920_ == 0 {
                        lean_ctor_set(v___x_1919_, 0, v_val_1935_);
                        v___x_1937_ = v___x_1919_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_val_1935_);
                        v___x_1937_ = v_reuseFailAlloc_1938_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1929_ == 0 {
                    lean_ctor_set(v___x_1928_, 0, v_a_1925_);
                    v___x_1931_ = v___x_1928_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1925_);
                    v___x_1931_ = v_reuseFailAlloc_1932_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1931_;
            }
            4 => {
                return v___x_1937_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getOtherDeclMonoType___boxed(
    mut v_declName_1940_: *mut LeanObject,
    mut v_a_1941_: *mut LeanObject,
    mut v_a_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1944_: *mut LeanObject = core::ptr::null_mut();
    v_res_1944_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(v_declName_1940_, v_a_1941_, v_a_1942_);
    lean_dec(v_a_1942_);
    lean_dec_ref(v_a_1941_);
    return v_res_1944_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(
    mut v_ext_1945_: *mut LeanObject,
    mut v_a_1946_: *mut LeanObject,
    mut v_a_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    v___x_1950_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___redArg(v_ext_1945_, v_a_1946_, v_a_1948_);
    return v___x_1950_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0___boxed(
    mut v_ext_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
    mut v_a_1953_: *mut LeanObject,
    mut v_a_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1956_: *mut LeanObject = core::ptr::null_mut();
    v_res_1956_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__0(v_ext_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
    lean_dec(v_a_1954_);
    lean_dec_ref(v_a_1953_);
    lean_dec(v_a_1952_);
    lean_dec_ref(v_ext_1951_);
    return v_res_1956_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1(
    mut v_ext_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_b_1959_: *mut LeanObject,
    mut v_a_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    v___x_1963_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___redArg(v_ext_1957_, v_a_1958_, v_b_1959_, v_a_1961_);
    return v___x_1963_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1___boxed(
    mut v_ext_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
    mut v_b_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1970_: *mut LeanObject = core::ptr::null_mut();
    v_res_1970_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclMonoType_spec__1(v_ext_1964_, v_a_1965_, v_b_1966_, v_a_1967_, v_a_1968_);
    lean_dec(v_a_1968_);
    lean_dec_ref(v_a_1967_);
    return v_res_1970_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_3322084883____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt =
        lean_io_result_get_value(res);
    lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_trivialStructureInfoExt,
    );
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_MonoTypes_1500374787____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_monoTypeExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_LCNF_monoTypeExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_MonoTypes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_MonoTypes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
}
