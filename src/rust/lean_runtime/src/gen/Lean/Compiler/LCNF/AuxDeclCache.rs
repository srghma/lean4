// Lean compiler output
// Module: Lean.Compiler.LCNF.AuxDeclCache
// Imports: Lean.Compiler.LCNF.DeclHash Lean.Compiler.LCNF.Internalize
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Prelude::l_List_lengthTR___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_instBEqDecl_beq, l_Lean_Compiler_LCNF_instDecidableEqPurity,
    l_Lean_Compiler_LCNF_instHashablePurity_hash,
};
use crate::r#gen::Lean::Compiler::LCNF::DeclHash::{
    initialize_Lean_Compiler_LCNF_DeclHash, l_Lean_Compiler_LCNF_instHashableDecl_hash,
    runtime_initialize_Lean_Compiler_LCNF_DeclHash,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    initialize_Lean_Compiler_LCNF_Internalize, l_Lean_Compiler_LCNF_normalizeFVarIds,
    runtime_initialize_Lean_Compiler_LCNF_Internalize,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_registerEnvExtension___redArg,
};
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
    lean_nat_sub, lean_panic_fn_borrowed, lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey_hash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__0_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__1_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 97, 112, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__5_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey_beq(
    mut v_x_665_: *mut LeanObject,
    mut v_x_666_: *mut LeanObject,
) -> u8 {
    let mut v_pu_667_: u8 = 0;
    let mut v_decl_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pu_669_: u8 = 0;
    let mut v_decl_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: u8 = 0;
    v_pu_667_ = lean_ctor_get_uint8(
        v_x_665_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_decl_668_ = lean_ctor_get(v_x_665_, 0);
    v_pu_669_ = lean_ctor_get_uint8(
        v_x_666_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_decl_670_ = lean_ctor_get(v_x_666_, 0);
    v___x_671_ = l_Lean_Compiler_LCNF_instDecidableEqPurity(v_pu_667_, v_pu_669_);
    if v___x_671_ == 0 {
        return v___x_671_;
    } else {
        let mut v___x_672_: u8 = 0;
        v___x_672_ = l_Lean_Compiler_LCNF_instBEqDecl_beq(v_pu_667_, v_decl_668_, v_decl_670_);
        return v___x_672_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey_beq___boxed(
    mut v_x_673_: *mut LeanObject,
    mut v_x_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_675_: u8 = 0;
    let mut v_r_676_: *mut LeanObject = core::ptr::null_mut();
    v_res_675_ = l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey_beq(v_x_673_, v_x_674_);
    lean_dec_ref(v_x_674_);
    lean_dec_ref(v_x_673_);
    v_r_676_ = lean_box((v_res_675_) as usize);
    return v_r_676_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey_hash(
    mut v_x_679_: *mut LeanObject,
) -> u64 {
    let mut v_pu_680_: u8 = 0;
    let mut v_decl_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u64 = 0;
    let mut v___x_683_: u64 = 0;
    let mut v___x_684_: u64 = 0;
    let mut v___x_685_: u64 = 0;
    let mut v___x_686_: u64 = 0;
    v_pu_680_ = lean_ctor_get_uint8(
        v_x_679_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_decl_681_ = lean_ctor_get(v_x_679_, 0);
    v___x_682_ = 0u64;
    v___x_683_ = l_Lean_Compiler_LCNF_instHashablePurity_hash(v_pu_680_);
    v___x_684_ = lean_uint64_mix_hash(v___x_682_, v___x_683_);
    v___x_685_ = l_Lean_Compiler_LCNF_instHashableDecl_hash(v_pu_680_, v_decl_681_);
    v___x_686_ = lean_uint64_mix_hash(v___x_684_, v___x_685_);
    return v___x_686_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey_hash___boxed(
    mut v_x_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_688_: u64 = 0;
    let mut v_r_689_: *mut LeanObject = core::ptr::null_mut();
    v_res_688_ = l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey_hash(v_x_687_);
    lean_dec_ref(v_x_687_);
    v_r_689_ = lean_box_uint64(v_res_688_);
    return v_r_689_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__1(
    mut v___x_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    v___x_694_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_694_, 0, v___x_692_);
    return v___x_694_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v___x_695_: *mut LeanObject,
    mut v___y_696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_697_: *mut LeanObject = core::ptr::null_mut();
    v_res_697_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__1(v___x_695_);
    return v_res_697_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__2(
    mut v_msg_698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    v___x_699_ = lean_box(0);
    v___x_700_ = lean_panic_fn_borrowed(v___x_699_, v_msg_698_);
    return v___x_700_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_701_: *mut LeanObject,
    mut v_x_702_: *mut LeanObject,
    mut v_x_703_: *mut LeanObject,
    mut v_x_704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_709_: u8 = 0;
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: u8 = 0;
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: u8 = 0;
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_705_ = lean_ctor_get(v_x_701_, 0);
                v_vs_706_ = lean_ctor_get(v_x_701_, 1);
                v_isSharedCheck_730_ = (!lean_is_exclusive(v_x_701_)) as u8;
                if v_isSharedCheck_730_ == 0 {
                    v___x_708_ = v_x_701_;
                    v_isShared_709_ = v_isSharedCheck_730_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_706_);
                    lean_inc(v_ks_705_);
                    lean_dec(v_x_701_);
                    v___x_708_ = lean_box(0);
                    v_isShared_709_ = v_isSharedCheck_730_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_710_ = lean_array_get_size(v_ks_705_);
                v___x_711_ = lean_nat_dec_lt(v_x_702_, v___x_710_);
                if v___x_711_ == 0 {
                    lean_dec(v_x_702_);
                    v___x_712_ = lean_array_push(v_ks_705_, v_x_703_);
                    v___x_713_ = lean_array_push(v_vs_706_, v_x_704_);
                    if v_isShared_709_ == 0 {
                        lean_ctor_set(v___x_708_, 1, v___x_713_);
                        lean_ctor_set(v___x_708_, 0, v___x_712_);
                        v___x_715_ = v___x_708_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_712_);
                        lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_713_);
                        v___x_715_ = v_reuseFailAlloc_716_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_717_ = lean_array_fget_borrowed(v_ks_705_, v_x_702_);
                    v___x_718_ =
                        l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey_beq(v_x_703_, v_k_x27_717_);
                    if v___x_718_ == 0 {
                        if v_isShared_709_ == 0 {
                            v___x_720_ = v___x_708_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_724_, 0, v_ks_705_);
                            lean_ctor_set(v_reuseFailAlloc_724_, 1, v_vs_706_);
                            v___x_720_ = v_reuseFailAlloc_724_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_725_ = lean_array_fset(v_ks_705_, v_x_702_, v_x_703_);
                        v___x_726_ = lean_array_fset(v_vs_706_, v_x_702_, v_x_704_);
                        lean_dec(v_x_702_);
                        if v_isShared_709_ == 0 {
                            lean_ctor_set(v___x_708_, 1, v___x_726_);
                            lean_ctor_set(v___x_708_, 0, v___x_725_);
                            v___x_728_ = v___x_708_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_725_);
                            lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_726_);
                            v___x_728_ = v_reuseFailAlloc_729_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_715_;
            }
            3 => {
                v___x_721_ = lean_unsigned_to_nat(1);
                v___x_722_ = lean_nat_add(v_x_702_, v___x_721_);
                lean_dec(v_x_702_);
                v_x_701_ = v___x_720_;
                v_x_702_ = v___x_722_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_n_731_: *mut LeanObject,
    mut v_k_732_: *mut LeanObject,
    mut v_v_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    v___x_734_ = lean_unsigned_to_nat(0);
    v___x_735_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_n_731_, v___x_734_, v_k_732_, v_v_733_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_736_: usize = 0;
    let mut v___x_737_: usize = 0;
    let mut v___x_738_: usize = 0;
    v___x_736_ = 5usize;
    v___x_737_ = 1usize;
    v___x_738_ = lean_usize_shift_left(v___x_737_, v___x_736_);
    return v___x_738_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_739_: usize = 0;
    let mut v___x_740_: usize = 0;
    let mut v___x_741_: usize = 0;
    v___x_739_ = 1usize;
    v___x_740_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_741_ = lean_usize_sub(v___x_740_, v___x_739_);
    return v___x_741_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    v___x_742_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_742_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_743_: *mut LeanObject,
    mut v_x_744_: usize,
    mut v_x_745_: usize,
    mut v_x_746_: *mut LeanObject,
    mut v_x_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: usize = 0;
    let mut v___x_750_: usize = 0;
    let mut v___x_751_: usize = 0;
    let mut v___x_752_: usize = 0;
    let mut v_j_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: u8 = 0;
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v_v_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_772_: u8 = 0;
    let mut v___x_773_: u8 = 0;
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut v_node_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_783_: u8 = 0;
    let mut v___x_784_: usize = 0;
    let mut v___x_785_: usize = 0;
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_792_: u8 = 0;
    let mut v_unused_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_798_: u8 = 0;
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_803_: u8 = 0;
    let mut v_ks_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: usize = 0;
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    let mut v_reuseFailAlloc_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_743_) == 0 {
                    v_es_748_ = lean_ctor_get(v_x_743_, 0);
                    v___x_749_ = 5usize;
                    v___x_750_ = 1usize;
                    v___x_751_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_752_ = lean_usize_land(v_x_744_, v___x_751_);
                    v_j_753_ = lean_usize_to_nat(v___x_752_);
                    v___x_754_ = lean_array_get_size(v_es_748_);
                    v___x_755_ = lean_nat_dec_lt(v_j_753_, v___x_754_);
                    if v___x_755_ == 0 {
                        lean_dec(v_j_753_);
                        lean_dec(v_x_747_);
                        lean_dec_ref(v_x_746_);
                        return v_x_743_;
                    } else {
                        lean_inc_ref(v_es_748_);
                        v_isSharedCheck_792_ = (!lean_is_exclusive(v_x_743_)) as u8;
                        if v_isSharedCheck_792_ == 0 {
                            v_unused_793_ = lean_ctor_get(v_x_743_, 0);
                            lean_dec(v_unused_793_);
                            v___x_757_ = v_x_743_;
                            v_isShared_758_ = v_isSharedCheck_792_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_743_);
                            v___x_757_ = lean_box(0);
                            v_isShared_758_ = v_isSharedCheck_792_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_794_ = lean_ctor_get(v_x_743_, 0);
                    v_vs_795_ = lean_ctor_get(v_x_743_, 1);
                    v_isSharedCheck_815_ = (!lean_is_exclusive(v_x_743_)) as u8;
                    if v_isSharedCheck_815_ == 0 {
                        v___x_797_ = v_x_743_;
                        v_isShared_798_ = v_isSharedCheck_815_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_795_);
                        lean_inc(v_ks_794_);
                        lean_dec(v_x_743_);
                        v___x_797_ = lean_box(0);
                        v_isShared_798_ = v_isSharedCheck_815_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_759_ = lean_array_fget(v_es_748_, v_j_753_);
                v___x_760_ = lean_box(0);
                v_xs_x27_761_ = lean_array_fset(v_es_748_, v_j_753_, v___x_760_);
                match lean_obj_tag(v_v_759_) {
                    0 => {
                        v_key_768_ = lean_ctor_get(v_v_759_, 0);
                        v_val_769_ = lean_ctor_get(v_v_759_, 1);
                        v_isSharedCheck_779_ = (!lean_is_exclusive(v_v_759_)) as u8;
                        if v_isSharedCheck_779_ == 0 {
                            v___x_771_ = v_v_759_;
                            v_isShared_772_ = v_isSharedCheck_779_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_769_);
                            lean_inc(v_key_768_);
                            lean_dec(v_v_759_);
                            v___x_771_ = lean_box(0);
                            v_isShared_772_ = v_isSharedCheck_779_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_780_ = lean_ctor_get(v_v_759_, 0);
                        v_isSharedCheck_790_ = (!lean_is_exclusive(v_v_759_)) as u8;
                        if v_isSharedCheck_790_ == 0 {
                            v___x_782_ = v_v_759_;
                            v_isShared_783_ = v_isSharedCheck_790_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_780_);
                            lean_dec(v_v_759_);
                            v___x_782_ = lean_box(0);
                            v_isShared_783_ = v_isSharedCheck_790_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_791_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_791_, 0, v_x_746_);
                        lean_ctor_set(v___x_791_, 1, v_x_747_);
                        v___y_763_ = v___x_791_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_764_ = lean_array_fset(v_xs_x27_761_, v_j_753_, v___y_763_);
                lean_dec(v_j_753_);
                if v_isShared_758_ == 0 {
                    lean_ctor_set(v___x_757_, 0, v___x_764_);
                    v___x_766_ = v___x_757_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
                    v___x_766_ = v_reuseFailAlloc_767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_766_;
            }
            4 => {
                v___x_773_ = l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey_beq(v_x_746_, v_key_768_);
                if v___x_773_ == 0 {
                    lean_del_object(v___x_771_);
                    v___x_774_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_768_, v_val_769_, v_x_746_, v_x_747_,
                    );
                    v___x_775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_775_, 0, v___x_774_);
                    v___y_763_ = v___x_775_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_769_);
                    lean_dec(v_key_768_);
                    if v_isShared_772_ == 0 {
                        lean_ctor_set(v___x_771_, 1, v_x_747_);
                        lean_ctor_set(v___x_771_, 0, v_x_746_);
                        v___x_777_ = v___x_771_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_778_, 0, v_x_746_);
                        lean_ctor_set(v_reuseFailAlloc_778_, 1, v_x_747_);
                        v___x_777_ = v_reuseFailAlloc_778_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_763_ = v___x_777_;
                state = 2;
                continue;
            }
            6 => {
                v___x_784_ = lean_usize_shift_right(v_x_744_, v___x_749_);
                v___x_785_ = lean_usize_add(v_x_745_, v___x_750_);
                v___x_786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_node_780_, v___x_784_, v___x_785_, v_x_746_, v_x_747_);
                if v_isShared_783_ == 0 {
                    lean_ctor_set(v___x_782_, 0, v___x_786_);
                    v___x_788_ = v___x_782_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
                    v___x_788_ = v_reuseFailAlloc_789_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_763_ = v___x_788_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_798_ == 0 {
                    v___x_800_ = v___x_797_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_814_, 0, v_ks_794_);
                    lean_ctor_set(v_reuseFailAlloc_814_, 1, v_vs_795_);
                    v___x_800_ = v_reuseFailAlloc_814_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_801_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v___x_800_, v_x_746_, v_x_747_);
                v___x_809_ = 7usize;
                v___x_810_ = lean_usize_dec_le(v___x_809_, v_x_745_);
                if v___x_810_ == 0 {
                    v___x_811_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_801_);
                    v___x_812_ = lean_unsigned_to_nat(4);
                    v___x_813_ = lean_nat_dec_lt(v___x_811_, v___x_812_);
                    lean_dec(v___x_811_);
                    v___y_803_ = v___x_813_;
                    state = 10;
                    continue;
                } else {
                    v___y_803_ = v___x_810_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_803_ == 0 {
                    v_ks_804_ = lean_ctor_get(v_newNode_801_, 0);
                    lean_inc_ref(v_ks_804_);
                    v_vs_805_ = lean_ctor_get(v_newNode_801_, 1);
                    lean_inc_ref(v_vs_805_);
                    lean_dec_ref(v_newNode_801_);
                    v___x_806_ = lean_unsigned_to_nat(0);
                    v___x_807_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_x_745_, v_ks_804_, v_vs_805_, v___x_806_, v___x_807_);
                    lean_dec_ref(v_vs_805_);
                    lean_dec_ref(v_ks_804_);
                    return v___x_808_;
                } else {
                    return v_newNode_801_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_depth_816_: usize,
    mut v_keys_817_: *mut LeanObject,
    mut v_vals_818_: *mut LeanObject,
    mut v_i_819_: *mut LeanObject,
    mut v_entries_820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: u8 = 0;
    let mut v_k_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u64 = 0;
    let mut v_h_826_: usize = 0;
    let mut v___x_827_: usize = 0;
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: usize = 0;
    let mut v___x_830_: usize = 0;
    let mut v___x_831_: usize = 0;
    let mut v_h_832_: usize = 0;
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_821_ = lean_array_get_size(v_keys_817_);
                v___x_822_ = lean_nat_dec_lt(v_i_819_, v___x_821_);
                if v___x_822_ == 0 {
                    lean_dec(v_i_819_);
                    return v_entries_820_;
                } else {
                    v_k_823_ = lean_array_fget_borrowed(v_keys_817_, v_i_819_);
                    v_v_824_ = lean_array_fget_borrowed(v_vals_818_, v_i_819_);
                    v___x_825_ = l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey_hash(v_k_823_);
                    v_h_826_ = lean_uint64_to_usize(v___x_825_);
                    v___x_827_ = 5usize;
                    v___x_828_ = lean_unsigned_to_nat(1);
                    v___x_829_ = 1usize;
                    v___x_830_ = lean_usize_sub(v_depth_816_, v___x_829_);
                    v___x_831_ = lean_usize_mul(v___x_827_, v___x_830_);
                    v_h_832_ = lean_usize_shift_right(v_h_826_, v___x_831_);
                    v___x_833_ = lean_nat_add(v_i_819_, v___x_828_);
                    lean_dec(v_i_819_);
                    lean_inc(v_v_824_);
                    lean_inc(v_k_823_);
                    v___x_834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_entries_820_, v_h_832_, v_depth_816_, v_k_823_, v_v_824_);
                    v_i_819_ = v___x_833_;
                    v_entries_820_ = v___x_834_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_depth_836_: *mut LeanObject,
    mut v_keys_837_: *mut LeanObject,
    mut v_vals_838_: *mut LeanObject,
    mut v_i_839_: *mut LeanObject,
    mut v_entries_840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_841_: usize = 0;
    let mut v_res_842_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_841_ = lean_unbox_usize(v_depth_836_);
    lean_dec(v_depth_836_);
    v_res_842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_841_, v_keys_837_, v_vals_838_, v_i_839_, v_entries_840_);
    lean_dec_ref(v_vals_838_);
    lean_dec_ref(v_keys_837_);
    return v_res_842_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_843_: *mut LeanObject,
    mut v_x_844_: *mut LeanObject,
    mut v_x_845_: *mut LeanObject,
    mut v_x_846_: *mut LeanObject,
    mut v_x_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_647__boxed_848_: usize = 0;
    let mut v_x_648__boxed_849_: usize = 0;
    let mut v_res_850_: *mut LeanObject = core::ptr::null_mut();
    v_x_647__boxed_848_ = lean_unbox_usize(v_x_844_);
    lean_dec(v_x_844_);
    v_x_648__boxed_849_ = lean_unbox_usize(v_x_845_);
    lean_dec(v_x_845_);
    v_res_850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_843_, v_x_647__boxed_848_, v_x_648__boxed_849_, v_x_846_, v_x_847_);
    return v_res_850_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_851_: *mut LeanObject,
    mut v_x_852_: *mut LeanObject,
    mut v_x_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_854_: u64 = 0;
    let mut v___x_855_: usize = 0;
    let mut v___x_856_: usize = 0;
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    v___x_854_ = l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey_hash(v_x_852_);
    v___x_855_ = lean_uint64_to_usize(v___x_854_);
    v___x_856_ = 1usize;
    v___x_857_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_851_, v___x_855_, v___x_856_, v_x_852_, v_x_853_);
    return v___x_857_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_keys_858_: *mut LeanObject,
    mut v_vals_859_: *mut LeanObject,
    mut v_i_860_: *mut LeanObject,
    mut v_k_861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: u8 = 0;
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_862_ = lean_array_get_size(v_keys_858_);
                v___x_863_ = lean_nat_dec_lt(v_i_860_, v___x_862_);
                if v___x_863_ == 0 {
                    lean_dec(v_i_860_);
                    v___x_864_ = lean_box(0);
                    return v___x_864_;
                } else {
                    v_k_x27_865_ = lean_array_fget_borrowed(v_keys_858_, v_i_860_);
                    v___x_866_ =
                        l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey_beq(v_k_861_, v_k_x27_865_);
                    if v___x_866_ == 0 {
                        v___x_867_ = lean_unsigned_to_nat(1);
                        v___x_868_ = lean_nat_add(v_i_860_, v___x_867_);
                        lean_dec(v_i_860_);
                        v_i_860_ = v___x_868_;
                        state = 0;
                        continue;
                    } else {
                        v___x_870_ = lean_array_fget_borrowed(v_vals_859_, v_i_860_);
                        lean_dec(v_i_860_);
                        lean_inc(v___x_870_);
                        v___x_871_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_871_, 0, v___x_870_);
                        return v___x_871_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_keys_872_: *mut LeanObject,
    mut v_vals_873_: *mut LeanObject,
    mut v_i_874_: *mut LeanObject,
    mut v_k_875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_876_: *mut LeanObject = core::ptr::null_mut();
    v_res_876_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_keys_872_, v_vals_873_, v_i_874_, v_k_875_);
    lean_dec_ref(v_k_875_);
    lean_dec_ref(v_vals_873_);
    lean_dec_ref(v_keys_872_);
    return v_res_876_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_x_877_: *mut LeanObject,
    mut v_x_878_: usize,
    mut v_x_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: usize = 0;
    let mut v___x_883_: usize = 0;
    let mut v___x_884_: usize = 0;
    let mut v_j_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: u8 = 0;
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: usize = 0;
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_877_) == 0 {
                    v_es_880_ = lean_ctor_get(v_x_877_, 0);
                    v___x_881_ = lean_box(2);
                    v___x_882_ = 5usize;
                    v___x_883_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_884_ = lean_usize_land(v_x_878_, v___x_883_);
                    v_j_885_ = lean_usize_to_nat(v___x_884_);
                    v___x_886_ = lean_array_get_borrowed(v___x_881_, v_es_880_, v_j_885_);
                    lean_dec(v_j_885_);
                    match lean_obj_tag(v___x_886_) {
                        0 => {
                            v_key_887_ = lean_ctor_get(v___x_886_, 0);
                            v_val_888_ = lean_ctor_get(v___x_886_, 1);
                            v___x_889_ = l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey_beq(
                                v_x_879_, v_key_887_,
                            );
                            if v___x_889_ == 0 {
                                v___x_890_ = lean_box(0);
                                return v___x_890_;
                            } else {
                                lean_inc(v_val_888_);
                                v___x_891_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_891_, 0, v_val_888_);
                                return v___x_891_;
                            }
                        }
                        1 => {
                            v_node_892_ = lean_ctor_get(v___x_886_, 0);
                            v___x_893_ = lean_usize_shift_right(v_x_878_, v___x_882_);
                            v_x_877_ = v_node_892_;
                            v_x_878_ = v___x_893_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_895_ = lean_box(0);
                            return v___x_895_;
                        }
                    }
                } else {
                    v_ks_896_ = lean_ctor_get(v_x_877_, 0);
                    v_vs_897_ = lean_ctor_get(v_x_877_, 1);
                    v___x_898_ = lean_unsigned_to_nat(0);
                    v___x_899_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_ks_896_, v_vs_897_, v___x_898_, v_x_879_);
                    return v___x_899_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_900_: *mut LeanObject,
    mut v_x_901_: *mut LeanObject,
    mut v_x_902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_847__boxed_903_: usize = 0;
    let mut v_res_904_: *mut LeanObject = core::ptr::null_mut();
    v_x_847__boxed_903_ = lean_unbox_usize(v_x_901_);
    lean_dec(v_x_901_);
    v_res_904_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_900_, v_x_847__boxed_903_, v_x_902_);
    lean_dec_ref(v_x_902_);
    lean_dec_ref(v_x_900_);
    return v_res_904_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_x_905_: *mut LeanObject,
    mut v_x_906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_907_: u64 = 0;
    let mut v___x_908_: usize = 0;
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    v___x_907_ = l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey_hash(v_x_906_);
    v___x_908_ = lean_uint64_to_usize(v___x_907_);
    v___x_909_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_905_, v___x_908_, v_x_906_);
    return v___x_909_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(
    mut v_x_910_: *mut LeanObject,
    mut v_x_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_912_: *mut LeanObject = core::ptr::null_mut();
    v_res_912_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_910_, v_x_911_);
    lean_dec_ref(v_x_911_);
    lean_dec_ref(v_x_910_);
    return v_res_912_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    v___x_916_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__2;
    v___x_917_ = lean_unsigned_to_nat(14);
    v___x_918_ = lean_unsigned_to_nat(177);
    v___x_919_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__1;
    v___x_920_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__0;
    v___x_921_ =
        l_mkPanicMessageWithDecl(v___x_920_, v___x_919_, v___x_918_, v___x_917_, v___x_916_);
    return v___x_921_;
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3(
    mut v_newState_922_: *mut LeanObject,
    mut v_x_923_: *mut LeanObject,
    mut v_x_924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v_fst_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_934_: u8 = 0;
    let mut v_snd_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_950_: u8 = 0;
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_924_) == 0 {
                    return v_x_923_;
                } else {
                    v_head_925_ = lean_ctor_get(v_x_924_, 0);
                    v_tail_926_ = lean_ctor_get(v_x_924_, 1);
                    v_isSharedCheck_951_ = (!lean_is_exclusive(v_x_924_)) as u8;
                    if v_isSharedCheck_951_ == 0 {
                        v___x_928_ = v_x_924_;
                        v_isShared_929_ = v_isSharedCheck_951_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_926_);
                        lean_inc(v_head_925_);
                        lean_dec(v_x_924_);
                        v___x_928_ = lean_box(0);
                        v_isShared_929_ = v_isSharedCheck_951_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_930_ = lean_ctor_get(v_x_923_, 0);
                v_snd_931_ = lean_ctor_get(v_x_923_, 1);
                v_isSharedCheck_950_ = (!lean_is_exclusive(v_x_923_)) as u8;
                if v_isSharedCheck_950_ == 0 {
                    v___x_933_ = v_x_923_;
                    v_isShared_934_ = v_isSharedCheck_950_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_931_);
                    lean_inc(v_fst_930_);
                    lean_dec(v_x_923_);
                    v___x_933_ = lean_box(0);
                    v_isShared_934_ = v_isSharedCheck_950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_935_ = lean_ctor_get(v_newState_922_, 1);
                lean_inc(v_head_925_);
                if v_isShared_929_ == 0 {
                    lean_ctor_set(v___x_928_, 1, v_fst_930_);
                    v___x_937_ = v___x_928_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_949_, 0, v_head_925_);
                    lean_ctor_set(v_reuseFailAlloc_949_, 1, v_fst_930_);
                    v___x_937_ = v_reuseFailAlloc_949_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_945_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_935_, v_head_925_);
                if lean_obj_tag(v___x_945_) == 0 {
                    v___x_946_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___closed__3);
                    v___x_947_ = l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__2(v___x_946_);
                    v___y_939_ = v___x_947_;
                    state = 4;
                    continue;
                } else {
                    v_val_948_ = lean_ctor_get(v___x_945_, 0);
                    lean_inc(v_val_948_);
                    lean_dec_ref_known(v___x_945_, 1);
                    v___y_939_ = v_val_948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_940_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_931_, v_head_925_, v___y_939_);
                if v_isShared_934_ == 0 {
                    lean_ctor_set(v___x_933_, 1, v___x_940_);
                    lean_ctor_set(v___x_933_, 0, v___x_937_);
                    v___x_942_ = v___x_933_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_937_);
                    lean_ctor_set(v_reuseFailAlloc_944_, 1, v___x_940_);
                    v___x_942_ = v_reuseFailAlloc_944_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_923_ = v___x_942_;
                v_x_924_ = v_tail_926_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3___boxed(
    mut v_newState_952_: *mut LeanObject,
    mut v_x_953_: *mut LeanObject,
    mut v_x_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_955_: *mut LeanObject = core::ptr::null_mut();
    v_res_955_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3(v_newState_952_, v_x_953_, v_x_954_);
    lean_dec_ref(v_newState_952_);
    return v_res_955_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__0(
    mut v_oldState_958_: *mut LeanObject,
    mut v_newState_959_: *mut LeanObject,
    mut v_x_960_: *mut LeanObject,
    mut v_s_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    v_fst_962_ = lean_ctor_get(v_newState_959_, 0);
    v_fst_963_ = lean_ctor_get(v_oldState_958_, 0);
    v___x_964_ = l_List_lengthTR___redArg(v_fst_962_);
    v___x_965_ = l_List_lengthTR___redArg(v_fst_963_);
    v___x_966_ = lean_nat_sub(v___x_964_, v___x_965_);
    lean_dec(v___x_965_);
    lean_dec(v___x_964_);
    v___x_967_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__0___closed__0;
    lean_inc(v_fst_962_);
    v_newEntries_968_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        lean_box(0),
        v_fst_962_,
        v_fst_962_,
        v___x_966_,
        v___x_967_,
    );
    v___x_969_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__3(v_newState_959_, v_s_961_, v_newEntries_968_);
    lean_dec_ref(v_newState_959_);
    return v___x_969_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__0___boxed(
    mut v_oldState_970_: *mut LeanObject,
    mut v_newState_971_: *mut LeanObject,
    mut v_x_972_: *mut LeanObject,
    mut v_s_973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_974_: *mut LeanObject = core::ptr::null_mut();
    v_res_974_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__0(v_oldState_970_, v_newState_971_, v_x_972_, v_s_973_);
    lean_dec(v_x_972_);
    lean_dec_ref(v_oldState_970_);
    return v_res_974_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_976_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    v___x_977_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__1);
    v___x_978_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_978_, 0, v___x_977_);
    return v___x_978_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_979_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__2);
    v___x_980_ = lean_box(0);
    v___x_981_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_981_, 0, v___x_980_);
    lean_ctor_set(v___x_981_, 1, v___x_979_);
    return v___x_981_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_983_: *mut LeanObject = core::ptr::null_mut();
    v___x_982_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__3);
    v___f_983_ = lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_983_, 0, v___x_982_);
    return v___f_983_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0()
-> *mut LeanObject {
    let mut v___f_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v_a_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_987_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__4_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__4);
                v___x_988_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___closed__5;
                v___x_989_ = lean_box(0);
                v___x_990_ =
                    l_Lean_registerEnvExtension___redArg(v___f_987_, v___x_988_, v___x_989_);
                if lean_obj_tag(v___x_990_) == 0 {
                    v_a_991_ = lean_ctor_get(v___x_990_, 0);
                    v_isSharedCheck_998_ = (!lean_is_exclusive(v___x_990_)) as u8;
                    if v_isSharedCheck_998_ == 0 {
                        v___x_993_ = v___x_990_;
                        v_isShared_994_ = v_isSharedCheck_998_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_991_);
                        lean_dec(v___x_990_);
                        v___x_993_ = lean_box(0);
                        v_isShared_994_ = v_isSharedCheck_998_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_999_ = lean_ctor_get(v___x_990_, 0);
                    v_isSharedCheck_1006_ = (!lean_is_exclusive(v___x_990_)) as u8;
                    if v_isSharedCheck_1006_ == 0 {
                        v___x_1001_ = v___x_990_;
                        v_isShared_1002_ = v_isSharedCheck_1006_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_999_);
                        lean_dec(v___x_990_);
                        v___x_1001_ = lean_box(0);
                        v_isShared_1002_ = v_isSharedCheck_1006_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_994_ == 0 {
                    v___x_996_ = v___x_993_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_996_;
            }
            3 => {
                if v_isShared_1002_ == 0 {
                    v___x_1004_ = v___x_1001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
                    v___x_1004_ = v_reuseFailAlloc_1005_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0___boxed(
    mut v_a_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1008_: *mut LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0();
    return v_res_1008_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0();
    return v___x_1010_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2____boxed(
    mut v_a_1011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1012_: *mut LeanObject = core::ptr::null_mut();
    v_res_1012_ = l___private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2_();
    return v_res_1012_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_1013_: *mut LeanObject,
    mut v_x_1014_: *mut LeanObject,
    mut v_x_1015_: *mut LeanObject,
    mut v_x_1016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    v___x_1017_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1014_, v_x_1015_, v_x_1016_);
    return v___x_1017_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_1018_: *mut LeanObject,
    mut v_x_1019_: *mut LeanObject,
    mut v_x_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    v___x_1021_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_1019_, v_x_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_00_u03b2_1022_: *mut LeanObject,
    mut v_x_1023_: *mut LeanObject,
    mut v_x_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1025_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b2_1022_, v_x_1023_, v_x_1024_);
    lean_dec_ref(v_x_1024_);
    lean_dec_ref(v_x_1023_);
    return v_res_1025_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_1026_: *mut LeanObject,
    mut v_x_1027_: *mut LeanObject,
    mut v_x_1028_: usize,
    mut v_x_1029_: usize,
    mut v_x_1030_: *mut LeanObject,
    mut v_x_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1027_, v_x_1028_, v_x_1029_, v_x_1030_, v_x_1031_);
    return v___x_1032_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1033_: *mut LeanObject,
    mut v_x_1034_: *mut LeanObject,
    mut v_x_1035_: *mut LeanObject,
    mut v_x_1036_: *mut LeanObject,
    mut v_x_1037_: *mut LeanObject,
    mut v_x_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1105__boxed_1039_: usize = 0;
    let mut v_x_1106__boxed_1040_: usize = 0;
    let mut v_res_1041_: *mut LeanObject = core::ptr::null_mut();
    v_x_1105__boxed_1039_ = lean_unbox_usize(v_x_1035_);
    lean_dec(v_x_1035_);
    v_x_1106__boxed_1040_ = lean_unbox_usize(v_x_1036_);
    lean_dec(v_x_1036_);
    v_res_1041_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1033_, v_x_1034_, v_x_1105__boxed_1039_, v_x_1106__boxed_1040_, v_x_1037_, v_x_1038_);
    return v_res_1041_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_1042_: *mut LeanObject,
    mut v_x_1043_: *mut LeanObject,
    mut v_x_1044_: usize,
    mut v_x_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_1043_, v_x_1044_, v_x_1045_);
    return v___x_1046_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_1047_: *mut LeanObject,
    mut v_x_1048_: *mut LeanObject,
    mut v_x_1049_: *mut LeanObject,
    mut v_x_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1122__boxed_1051_: usize = 0;
    let mut v_res_1052_: *mut LeanObject = core::ptr::null_mut();
    v_x_1122__boxed_1051_ = lean_unbox_usize(v_x_1049_);
    lean_dec(v_x_1049_);
    v_res_1052_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_1047_, v_x_1048_, v_x_1122__boxed_1051_, v_x_1050_);
    lean_dec_ref(v_x_1050_);
    lean_dec_ref(v_x_1048_);
    return v_res_1052_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_1053_: *mut LeanObject,
    mut v_n_1054_: *mut LeanObject,
    mut v_k_1055_: *mut LeanObject,
    mut v_v_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    v___x_1057_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_n_1054_, v_k_1055_, v_v_1056_);
    return v___x_1057_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_1058_: *mut LeanObject,
    mut v_depth_1059_: usize,
    mut v_keys_1060_: *mut LeanObject,
    mut v_vals_1061_: *mut LeanObject,
    mut v_heq_1062_: *mut LeanObject,
    mut v_i_1063_: *mut LeanObject,
    mut v_entries_1064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    v___x_1065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_depth_1059_, v_keys_1060_, v_vals_1061_, v_i_1063_, v_entries_1064_);
    return v___x_1065_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_1066_: *mut LeanObject,
    mut v_depth_1067_: *mut LeanObject,
    mut v_keys_1068_: *mut LeanObject,
    mut v_vals_1069_: *mut LeanObject,
    mut v_heq_1070_: *mut LeanObject,
    mut v_i_1071_: *mut LeanObject,
    mut v_entries_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1073_: usize = 0;
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1073_ = lean_unbox_usize(v_depth_1067_);
    lean_dec(v_depth_1067_);
    v_res_1074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1066_, v_depth_boxed_1073_, v_keys_1068_, v_vals_1069_, v_heq_1070_, v_i_1071_, v_entries_1072_);
    lean_dec_ref(v_vals_1069_);
    lean_dec_ref(v_keys_1068_);
    return v_res_1074_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_1075_: *mut LeanObject,
    mut v_keys_1076_: *mut LeanObject,
    mut v_vals_1077_: *mut LeanObject,
    mut v_heq_1078_: *mut LeanObject,
    mut v_i_1079_: *mut LeanObject,
    mut v_k_1080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_keys_1076_, v_vals_1077_, v_i_1079_, v_k_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_1082_: *mut LeanObject,
    mut v_keys_1083_: *mut LeanObject,
    mut v_vals_1084_: *mut LeanObject,
    mut v_heq_1085_: *mut LeanObject,
    mut v_i_1086_: *mut LeanObject,
    mut v_k_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1088_: *mut LeanObject = core::ptr::null_mut();
    v_res_1088_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(v_00_u03b2_1082_, v_keys_1083_, v_vals_1084_, v_heq_1085_, v_i_1086_, v_k_1087_);
    lean_dec_ref(v_k_1087_);
    lean_dec_ref(v_vals_1084_);
    lean_dec_ref(v_keys_1083_);
    return v_res_1088_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_1089_: *mut LeanObject,
    mut v_x_1090_: *mut LeanObject,
    mut v_x_1091_: *mut LeanObject,
    mut v_x_1092_: *mut LeanObject,
    mut v_x_1093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    v___x_1094_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1090_, v_x_1091_, v_x_1092_, v_x_1093_);
    return v___x_1094_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorIdx(
    mut v_x_1095_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1095_) == 0 {
        let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
        v___x_1096_ = lean_unsigned_to_nat(0);
        return v___x_1096_;
    } else {
        let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
        v___x_1097_ = lean_unsigned_to_nat(1);
        return v___x_1097_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorIdx___boxed(
    mut v_x_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1099_: *mut LeanObject = core::ptr::null_mut();
    v_res_1099_ = l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorIdx(v_x_1098_);
    lean_dec(v_x_1098_);
    return v_res_1099_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim___redArg(
    mut v_t_1100_: *mut LeanObject,
    mut v_k_1101_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1100_) == 0 {
        return v_k_1101_;
    } else {
        let mut v_declName_1102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
        v_declName_1102_ = lean_ctor_get(v_t_1100_, 0);
        lean_inc(v_declName_1102_);
        lean_dec_ref_known(v_t_1100_, 1);
        v___x_1103_ = lean_apply_1(v_k_1101_, v_declName_1102_);
        return v___x_1103_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim(
    mut v_motive_1104_: *mut LeanObject,
    mut v_ctorIdx_1105_: *mut LeanObject,
    mut v_t_1106_: *mut LeanObject,
    mut v_h_1107_: *mut LeanObject,
    mut v_k_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    v___x_1109_ = l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim___redArg(v_t_1106_, v_k_1108_);
    return v___x_1109_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim___boxed(
    mut v_motive_1110_: *mut LeanObject,
    mut v_ctorIdx_1111_: *mut LeanObject,
    mut v_t_1112_: *mut LeanObject,
    mut v_h_1113_: *mut LeanObject,
    mut v_k_1114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1115_: *mut LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim(
        v_motive_1110_,
        v_ctorIdx_1111_,
        v_t_1112_,
        v_h_1113_,
        v_k_1114_,
    );
    lean_dec(v_ctorIdx_1111_);
    return v_res_1115_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_new_elim___redArg(
    mut v_t_1116_: *mut LeanObject,
    mut v_new_1117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    v___x_1118_ = l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim___redArg(v_t_1116_, v_new_1117_);
    return v___x_1118_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_new_elim(
    mut v_motive_1119_: *mut LeanObject,
    mut v_t_1120_: *mut LeanObject,
    mut v_h_1121_: *mut LeanObject,
    mut v_new_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim___redArg(v_t_1120_, v_new_1122_);
    return v___x_1123_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_alreadyCached_elim___redArg(
    mut v_t_1124_: *mut LeanObject,
    mut v_alreadyCached_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    v___x_1126_ =
        l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim___redArg(v_t_1124_, v_alreadyCached_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheAuxDeclResult_alreadyCached_elim(
    mut v_motive_1127_: *mut LeanObject,
    mut v_t_1128_: *mut LeanObject,
    mut v_h_1129_: *mut LeanObject,
    mut v_alreadyCached_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ =
        l_Lean_Compiler_LCNF_CacheAuxDeclResult_ctorElim___redArg(v_t_1128_, v_alreadyCached_1130_);
    return v___x_1131_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = l_Lean_Compiler_LCNF_instHashableAuxDeclCacheKey___closed__0;
    v___x_1133_ = l_Lean_Compiler_LCNF_instBEqAuxDeclCacheKey___closed__0;
    v___x_1134_ =
        l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1133_, v___x_1132_);
    return v___x_1134_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    v___x_1135_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__0_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__0);
    v___x_1136_ = lean_box(0);
    v___x_1137_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1137_, 0, v___x_1136_);
    lean_ctor_set(v___x_1137_, 1, v___x_1135_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg(
    mut v_ext_1138_: *mut LeanObject,
    mut v_a_1139_: *mut LeanObject,
    mut v_a_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    v___x_1142_ = lean_st_ref_get(v_a_1140_);
    v_env_1143_ = lean_ctor_get(v___x_1142_, 0);
    lean_inc_ref(v_env_1143_);
    lean_dec(v___x_1142_);
    v_asyncMode_1144_ = lean_ctor_get(v_ext_1138_, 2);
    v___x_1145_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___closed__1);
    v___x_1146_ = lean_box(0);
    v___x_1147_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_1145_,
        v_ext_1138_,
        v_env_1143_,
        v_asyncMode_1144_,
        v___x_1146_,
    );
    v_snd_1148_ = lean_ctor_get(v___x_1147_, 1);
    lean_inc(v_snd_1148_);
    lean_dec(v___x_1147_);
    v___x_1149_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_1148_, v_a_1139_);
    lean_dec(v_snd_1148_);
    v___x_1150_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1150_, 0, v___x_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg___boxed(
    mut v_ext_1151_: *mut LeanObject,
    mut v_a_1152_: *mut LeanObject,
    mut v_a_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1155_: *mut LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg(v_ext_1151_, v_a_1152_, v_a_1153_);
    lean_dec(v_a_1153_);
    lean_dec_ref(v_a_1152_);
    lean_dec_ref(v_ext_1151_);
    return v_res_1155_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___lam__0(
    mut v_a_1156_: *mut LeanObject,
    mut v_b_1157_: *mut LeanObject,
    mut v_x_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1159_ = lean_ctor_get(v_x_1158_, 0);
                v_snd_1160_ = lean_ctor_get(v_x_1158_, 1);
                v_isSharedCheck_1169_ = (!lean_is_exclusive(v_x_1158_)) as u8;
                if v_isSharedCheck_1169_ == 0 {
                    v___x_1162_ = v_x_1158_;
                    v_isShared_1163_ = v_isSharedCheck_1169_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1160_);
                    lean_inc(v_fst_1159_);
                    lean_dec(v_x_1158_);
                    v___x_1162_ = lean_box(0);
                    v_isShared_1163_ = v_isSharedCheck_1169_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_a_1156_);
                v___x_1164_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1164_, 0, v_a_1156_);
                lean_ctor_set(v___x_1164_, 1, v_fst_1159_);
                v___x_1165_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_1160_, v_a_1156_, v_b_1157_);
                if v_isShared_1163_ == 0 {
                    lean_ctor_set(v___x_1162_, 1, v___x_1165_);
                    lean_ctor_set(v___x_1162_, 0, v___x_1164_);
                    v___x_1167_ = v___x_1162_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
                    lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1165_);
                    v___x_1167_ = v_reuseFailAlloc_1168_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1170_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    v___x_1171_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__0_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__0);
    v___x_1172_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1172_, 0, v___x_1171_);
    return v___x_1172_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    v___x_1173_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__1);
    v___x_1174_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1174_, 0, v___x_1173_);
    lean_ctor_set(v___x_1174_, 1, v___x_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg(
    mut v_ext_1175_: *mut LeanObject,
    mut v_a_1176_: *mut LeanObject,
    mut v_b_1177_: *mut LeanObject,
    mut v_a_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v_asyncMode_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut v_unused_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1180_ = lean_st_ref_take(v_a_1178_);
                v_env_1181_ = lean_ctor_get(v___x_1180_, 0);
                v_nextMacroScope_1182_ = lean_ctor_get(v___x_1180_, 1);
                v_ngen_1183_ = lean_ctor_get(v___x_1180_, 2);
                v_auxDeclNGen_1184_ = lean_ctor_get(v___x_1180_, 3);
                v_traceState_1185_ = lean_ctor_get(v___x_1180_, 4);
                v_messages_1186_ = lean_ctor_get(v___x_1180_, 6);
                v_infoState_1187_ = lean_ctor_get(v___x_1180_, 7);
                v_snapshotTasks_1188_ = lean_ctor_get(v___x_1180_, 8);
                v_isSharedCheck_1203_ = (!lean_is_exclusive(v___x_1180_)) as u8;
                if v_isSharedCheck_1203_ == 0 {
                    v_unused_1204_ = lean_ctor_get(v___x_1180_, 5);
                    lean_dec(v_unused_1204_);
                    v___x_1190_ = v___x_1180_;
                    v_isShared_1191_ = v_isSharedCheck_1203_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1188_);
                    lean_inc(v_infoState_1187_);
                    lean_inc(v_messages_1186_);
                    lean_inc(v_traceState_1185_);
                    lean_inc(v_auxDeclNGen_1184_);
                    lean_inc(v_ngen_1183_);
                    lean_inc(v_nextMacroScope_1182_);
                    lean_inc(v_env_1181_);
                    lean_dec(v___x_1180_);
                    v___x_1190_ = lean_box(0);
                    v_isShared_1191_ = v_isSharedCheck_1203_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_1192_ = lean_ctor_get(v_ext_1175_, 2);
                lean_inc(v_asyncMode_1192_);
                v___f_1193_ = lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_1193_, 0, v_a_1176_);
                lean_closure_set(v___f_1193_, 1, v_b_1177_);
                v___x_1194_ = lean_box(0);
                v___x_1195_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_1175_,
                    v_env_1181_,
                    v___f_1193_,
                    v_asyncMode_1192_,
                    v___x_1194_,
                );
                lean_dec(v_asyncMode_1192_);
                v___x_1196_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___closed__2);
                if v_isShared_1191_ == 0 {
                    lean_ctor_set(v___x_1190_, 5, v___x_1196_);
                    lean_ctor_set(v___x_1190_, 0, v___x_1195_);
                    v___x_1198_ = v___x_1190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1195_);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_nextMacroScope_1182_);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_ngen_1183_);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_auxDeclNGen_1184_);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 4, v_traceState_1185_);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 5, v___x_1196_);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 6, v_messages_1186_);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 7, v_infoState_1187_);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 8, v_snapshotTasks_1188_);
                    v___x_1198_ = v_reuseFailAlloc_1202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1199_ = lean_st_ref_set(v_a_1178_, v___x_1198_);
                v___x_1200_ = lean_box(0);
                v___x_1201_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1201_, 0, v___x_1200_);
                return v___x_1201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg___boxed(
    mut v_ext_1205_: *mut LeanObject,
    mut v_a_1206_: *mut LeanObject,
    mut v_b_1207_: *mut LeanObject,
    mut v_a_1208_: *mut LeanObject,
    mut v_a_1209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1210_: *mut LeanObject = core::ptr::null_mut();
    v_res_1210_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg(v_ext_1205_, v_a_1206_, v_b_1207_, v_a_1208_);
    lean_dec(v_a_1208_);
    return v_res_1210_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(
    mut v_pu_1211_: u8,
    mut v_decl_1212_: *mut LeanObject,
    mut v_a_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_1218_: u8 = 0;
    let mut v_inlineAttr_x3f_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v_name_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_safe_1227_: u8 = 0;
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1244_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1253_: u8 = 0;
    let mut v_unused_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_isSharedCheck_1266_: u8 = 0;
    let mut v_a_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1274_: u8 = 0;
    let mut v_reuseFailAlloc_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_1216_ = lean_ctor_get(v_decl_1212_, 0);
                v_value_1217_ = lean_ctor_get(v_decl_1212_, 1);
                v_recursive_1218_ = lean_ctor_get_uint8(
                    v_decl_1212_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_1219_ = lean_ctor_get(v_decl_1212_, 2);
                v_isSharedCheck_1278_ = (!lean_is_exclusive(v_decl_1212_)) as u8;
                if v_isSharedCheck_1278_ == 0 {
                    v___x_1221_ = v_decl_1212_;
                    v_isShared_1222_ = v_isSharedCheck_1278_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_1219_);
                    lean_inc(v_value_1217_);
                    lean_inc(v_toSignature_1216_);
                    lean_dec(v_decl_1212_);
                    v___x_1221_ = lean_box(0);
                    v_isShared_1222_ = v_isSharedCheck_1278_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1223_ = lean_ctor_get(v_toSignature_1216_, 0);
                v_levelParams_1224_ = lean_ctor_get(v_toSignature_1216_, 1);
                v_type_1225_ = lean_ctor_get(v_toSignature_1216_, 2);
                v_params_1226_ = lean_ctor_get(v_toSignature_1216_, 3);
                v_safe_1227_ = lean_ctor_get_uint8(
                    v_toSignature_1216_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_1277_ = (!lean_is_exclusive(v_toSignature_1216_)) as u8;
                if v_isSharedCheck_1277_ == 0 {
                    v___x_1229_ = v_toSignature_1216_;
                    v_isShared_1230_ = v_isSharedCheck_1277_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_params_1226_);
                    lean_inc(v_type_1225_);
                    lean_inc(v_levelParams_1224_);
                    lean_inc(v_name_1223_);
                    lean_dec(v_toSignature_1216_);
                    v___x_1229_ = lean_box(0);
                    v_isShared_1230_ = v_isSharedCheck_1277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1231_ = lean_box(0);
                if v_isShared_1230_ == 0 {
                    lean_ctor_set(v___x_1229_, 0, v___x_1231_);
                    v___x_1233_ = v___x_1229_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1231_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_levelParams_1224_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_type_1225_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_params_1226_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1276_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_safe_1227_,
                    );
                    v___x_1233_ = v_reuseFailAlloc_1276_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1222_ == 0 {
                    lean_ctor_set(v___x_1221_, 0, v___x_1233_);
                    v_key_1235_ = v___x_1221_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1233_);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_value_1217_);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_inlineAttr_x3f_1219_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1275_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_1218_,
                    );
                    v_key_1235_ = v_reuseFailAlloc_1275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1236_ = l_Lean_Compiler_LCNF_normalizeFVarIds(
                    v_pu_1211_,
                    v_key_1235_,
                    v_a_1213_,
                    v_a_1214_,
                );
                if lean_obj_tag(v___x_1236_) == 0 {
                    v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
                    lean_inc(v_a_1237_);
                    lean_dec_ref_known(v___x_1236_, 1);
                    v___x_1238_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1238_, 0, v_a_1237_);
                    lean_ctor_set_uint8(
                        v___x_1238_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_pu_1211_,
                    );
                    v___x_1239_ = l_Lean_Compiler_LCNF_auxDeclCacheExt;
                    v___x_1240_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg(v___x_1239_, v___x_1238_, v_a_1214_);
                    v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
                    v_isSharedCheck_1266_ = (!lean_is_exclusive(v___x_1240_)) as u8;
                    if v_isSharedCheck_1266_ == 0 {
                        v___x_1243_ = v___x_1240_;
                        v_isShared_1244_ = v_isSharedCheck_1266_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1241_);
                        lean_dec(v___x_1240_);
                        v___x_1243_ = lean_box(0);
                        v_isShared_1244_ = v_isSharedCheck_1266_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1223_);
                    v_a_1267_ = lean_ctor_get(v___x_1236_, 0);
                    v_isSharedCheck_1274_ = (!lean_is_exclusive(v___x_1236_)) as u8;
                    if v_isSharedCheck_1274_ == 0 {
                        v___x_1269_ = v___x_1236_;
                        v_isShared_1270_ = v_isSharedCheck_1274_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1267_);
                        lean_dec(v___x_1236_);
                        v___x_1269_ = lean_box(0);
                        v_isShared_1270_ = v_isSharedCheck_1274_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_1241_) == 0 {
                    lean_del_object(v___x_1243_);
                    v___x_1245_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg(v___x_1239_, v___x_1238_, v_name_1223_, v_a_1214_);
                    v_isSharedCheck_1253_ = (!lean_is_exclusive(v___x_1245_)) as u8;
                    if v_isSharedCheck_1253_ == 0 {
                        v_unused_1254_ = lean_ctor_get(v___x_1245_, 0);
                        lean_dec(v_unused_1254_);
                        v___x_1247_ = v___x_1245_;
                        v_isShared_1248_ = v_isSharedCheck_1253_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v___x_1245_);
                        v___x_1247_ = lean_box(0);
                        v_isShared_1248_ = v_isSharedCheck_1253_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_1238_, 1);
                    lean_dec(v_name_1223_);
                    v_val_1255_ = lean_ctor_get(v_a_1241_, 0);
                    v_isSharedCheck_1265_ = (!lean_is_exclusive(v_a_1241_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1257_ = v_a_1241_;
                        v_isShared_1258_ = v_isSharedCheck_1265_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_1255_);
                        lean_dec(v_a_1241_);
                        v___x_1257_ = lean_box(0);
                        v_isShared_1258_ = v_isSharedCheck_1265_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1249_ = lean_box(0);
                if v_isShared_1248_ == 0 {
                    lean_ctor_set(v___x_1247_, 0, v___x_1249_);
                    v___x_1251_ = v___x_1247_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
                    v___x_1251_ = v_reuseFailAlloc_1252_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1251_;
            }
            8 => {
                if v_isShared_1258_ == 0 {
                    v___x_1260_ = v___x_1257_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_val_1255_);
                    v___x_1260_ = v_reuseFailAlloc_1264_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1244_ == 0 {
                    lean_ctor_set(v___x_1243_, 0, v___x_1260_);
                    v___x_1262_ = v___x_1243_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
                    v___x_1262_ = v_reuseFailAlloc_1263_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1262_;
            }
            11 => {
                if v_isShared_1270_ == 0 {
                    v___x_1272_ = v___x_1269_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
                    v___x_1272_ = v_reuseFailAlloc_1273_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_cacheAuxDecl___redArg___boxed(
    mut v_pu_1279_: *mut LeanObject,
    mut v_decl_1280_: *mut LeanObject,
    mut v_a_1281_: *mut LeanObject,
    mut v_a_1282_: *mut LeanObject,
    mut v_a_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1284_: u8 = 0;
    let mut v_res_1285_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1284_ = (lean_unbox(v_pu_1279_) as u8);
    v_res_1285_ = l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(
        v_pu_boxed_1284_,
        v_decl_1280_,
        v_a_1281_,
        v_a_1282_,
    );
    lean_dec(v_a_1282_);
    lean_dec_ref(v_a_1281_);
    return v_res_1285_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cacheAuxDecl(
    mut v_pu_1286_: u8,
    mut v_decl_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
    mut v_a_1289_: *mut LeanObject,
    mut v_a_1290_: *mut LeanObject,
    mut v_a_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    v___x_1293_ =
        l_Lean_Compiler_LCNF_cacheAuxDecl___redArg(v_pu_1286_, v_decl_1287_, v_a_1290_, v_a_1291_);
    return v___x_1293_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cacheAuxDecl___boxed(
    mut v_pu_1294_: *mut LeanObject,
    mut v_decl_1295_: *mut LeanObject,
    mut v_a_1296_: *mut LeanObject,
    mut v_a_1297_: *mut LeanObject,
    mut v_a_1298_: *mut LeanObject,
    mut v_a_1299_: *mut LeanObject,
    mut v_a_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1301_: u8 = 0;
    let mut v_res_1302_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1301_ = (lean_unbox(v_pu_1294_) as u8);
    v_res_1302_ = l_Lean_Compiler_LCNF_cacheAuxDecl(
        v_pu_boxed_1301_,
        v_decl_1295_,
        v_a_1296_,
        v_a_1297_,
        v_a_1298_,
        v_a_1299_,
    );
    lean_dec(v_a_1299_);
    lean_dec_ref(v_a_1298_);
    lean_dec(v_a_1297_);
    lean_dec_ref(v_a_1296_);
    return v_res_1302_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0(
    mut v_ext_1303_: *mut LeanObject,
    mut v_a_1304_: *mut LeanObject,
    mut v_a_1305_: *mut LeanObject,
    mut v_a_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    v___x_1308_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___redArg(v_ext_1303_, v_a_1304_, v_a_1306_);
    return v___x_1308_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0___boxed(
    mut v_ext_1309_: *mut LeanObject,
    mut v_a_1310_: *mut LeanObject,
    mut v_a_1311_: *mut LeanObject,
    mut v_a_1312_: *mut LeanObject,
    mut v_a_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1314_: *mut LeanObject = core::ptr::null_mut();
    v_res_1314_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__0(v_ext_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
    lean_dec(v_a_1312_);
    lean_dec_ref(v_a_1311_);
    lean_dec_ref(v_a_1310_);
    lean_dec_ref(v_ext_1309_);
    return v_res_1314_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1(
    mut v_ext_1315_: *mut LeanObject,
    mut v_a_1316_: *mut LeanObject,
    mut v_b_1317_: *mut LeanObject,
    mut v_a_1318_: *mut LeanObject,
    mut v_a_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    v___x_1321_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___redArg(v_ext_1315_, v_a_1316_, v_b_1317_, v_a_1319_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1___boxed(
    mut v_ext_1322_: *mut LeanObject,
    mut v_a_1323_: *mut LeanObject,
    mut v_b_1324_: *mut LeanObject,
    mut v_a_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
    mut v_a_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1328_: *mut LeanObject = core::ptr::null_mut();
    v_res_1328_ =
        l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_cacheAuxDecl_spec__1(
            v_ext_1322_,
            v_a_1323_,
            v_b_1324_,
            v_a_1325_,
            v_a_1326_,
        );
    lean_dec(v_a_1326_);
    lean_dec_ref(v_a_1325_);
    return v_res_1328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_DeclHash(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_AuxDeclCache_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_AuxDeclCache_612039165____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_auxDeclCacheExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_LCNF_auxDeclCacheExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_DeclHash(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_AuxDeclCache(builtin);
}
