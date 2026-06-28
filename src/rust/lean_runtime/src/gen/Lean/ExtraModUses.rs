// Lean compiler output
// Module: Lean.ExtraModUses
// Imports: Lean.CoreM Lean.Compiler.MetaAttr Init.Data.Range.Polymorphic.Stream
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::List::Basic::{l_List_elem___redArg, l_List_isEmpty___redArg};
use crate::r#gen::Init::Data::Range::Polymorphic::Stream::{
    initialize_Init_Data_Range_Polymorphic_Stream,
    runtime_initialize_Init_Data_Range_Polymorphic_Stream,
};
use crate::r#gen::Init::Data::Repr::l_Bool_repr___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Compiler::MetaAttr::{
    initialize_Lean_Compiler_MetaAttr, l_Lean_isMarkedMeta,
    runtime_initialize_Lean_Compiler_MetaAttr,
};
use crate::r#gen::Lean::CoreM::{initialize_Lean_CoreM, runtime_initialize_Lean_CoreM};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_contains___redArg, l_Lean_PersistentHashMap_empty,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getEntries___redArg,
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_mainModule, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_addTrace___redArg,
    l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_string_dec_eq, lean_uint64_mix_hash, lean_uint64_of_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_box_uint64, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_instBEqIndirectModUse___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqIndirectModUse_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqIndirectModUse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqIndirectModUse___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instBEqIndirectModUse: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqIndirectModUse___closed__0_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0: u64 = 0;
pub static l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 100, 105, 114, 101, 99, 116, 77, 111, 100, 85, 115, 101, 69, 120, 116, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,7815413168530042310 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_getIndirectModUses___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getIndirectModUses___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getIndirectModUses___closed__0_value) as *mut LeanObject;
pub static l_Lean_getIndirectModUses___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getIndirectModUses___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getIndirectModUses___closed__1_value) as *mut LeanObject;
static mut l_Lean_getIndirectModUses___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getIndirectModUses___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_getIndirectModUses___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getIndirectModUses___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 105, 110, 100, 105, 114, 101, 99, 116,
            32, 109, 111, 100, 32, 117, 115, 101, 32, 111, 102, 32, 96, 0,
        ],
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_recordIndirectModUse___redArg___lam__2___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [96, 32, 40, 0],
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_recordIndirectModUse___redArg___lam__2___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__2___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_recordIndirectModUse___redArg___lam__3___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0],
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_recordIndirectModUse___redArg___lam__5___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value)
                as *mut LeanObject,
            7870113334857981723 as *mut LeanObject,
        ],
    };
static mut l_Lean_recordIndirectModUse___redArg___lam__5___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instBEqExtraModUse___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instBEqExtraModUse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqExtraModUse___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instBEqExtraModUse: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqExtraModUse___closed__0_value) as *mut LeanObject;
pub static l_Lean_instHashableExtraModUse___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableExtraModUse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableExtraModUse___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instHashableExtraModUse: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableExtraModUse___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [123, 32, 0],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__8_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [44, 0],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__10_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 115, 69, 120, 112, 111, 114, 116, 101, 100, 0],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__13_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 115, 77, 101, 116, 97, 0],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__15_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [32, 125, 0],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__18_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse_repr___redArg___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprExtraModUse_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_instReprExtraModUse___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instReprExtraModUse_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprExtraModUse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprExtraModUse: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprExtraModUse___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [69, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,7432567167288952258 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,12505354990541503907 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,8453234876759232750 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value) as *mut LeanObject,10666000162378543426 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanClosureObject<4> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_getExtraModUses___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getExtraModUses___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_getExtraModUses___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getExtraModUses___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 115, 69, 120, 116, 114, 97, 82, 101, 118, 77, 111, 100, 85, 115, 101, 69, 120, 116, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject,15277525081364648378 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_isExtraRevModUse___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_isExtraRevModUse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_isExtraRevModUse___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 101, 120, 116, 114, 97, 32, 114, 101, 118,
        101, 114, 115, 101, 32, 117, 115, 101, 32, 111, 102, 32, 99, 117, 114, 114, 101, 110, 116,
        32, 109, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject,2221357554095543171 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject,14045213744755362806 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value) as *mut LeanObject,14174113666980693535 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value) as *mut LeanObject,5538872010216668907 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_instBEqIndirectModUse_beq(
    mut v_x_1703_: *mut LeanObject,
    mut v_x_1704_: *mut LeanObject,
) -> u8 {
    let mut v_kind_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: u8 = 0;
    v_kind_1705_ = lean_ctor_get(v_x_1703_, 0);
    v_declName_1706_ = lean_ctor_get(v_x_1703_, 1);
    v_kind_1707_ = lean_ctor_get(v_x_1704_, 0);
    v_declName_1708_ = lean_ctor_get(v_x_1704_, 1);
    v___x_1709_ = lean_string_dec_eq(v_kind_1705_, v_kind_1707_);
    if v___x_1709_ == 0 {
        return v___x_1709_;
    } else {
        let mut v___x_1710_: u8 = 0;
        v___x_1710_ = lean_name_eq(v_declName_1706_, v_declName_1708_);
        return v___x_1710_;
    }
}
pub unsafe fn l_Lean_instBEqIndirectModUse_beq___boxed(
    mut v_x_1711_: *mut LeanObject,
    mut v_x_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1713_: u8 = 0;
    let mut v_r_1714_: *mut LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lean_instBEqIndirectModUse_beq(v_x_1711_, v_x_1712_);
    lean_dec_ref(v_x_1712_);
    lean_dec_ref(v_x_1711_);
    v_r_1714_ = lean_box((v_res_1713_) as usize);
    return v_r_1714_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(
    mut v_es_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    v___x_1718_ = lean_array_mk(v_es_1717_);
    return v___x_1718_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(
    mut v_s_1719_: *mut LeanObject,
    mut v_x_1720_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_s_1719_);
    return v_s_1719_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(
    mut v_s_1721_: *mut LeanObject,
    mut v_x_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1723_: *mut LeanObject = core::ptr::null_mut();
    v_res_1723_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_s_1721_, v_x_1722_);
    lean_dec_ref(v_x_1722_);
    lean_dec_ref(v_s_1721_);
    return v_res_1723_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: u64 = 0;
    v___x_1724_ = lean_unsigned_to_nat(1723);
    v___x_1725_ = lean_uint64_of_nat(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_x_1726_: *mut LeanObject,
    mut v_x_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1733_: u8 = 0;
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: u64 = 0;
    let mut v___x_1737_: u64 = 0;
    let mut v___x_1738_: u64 = 0;
    let mut v_fold_1739_: u64 = 0;
    let mut v___x_1740_: u64 = 0;
    let mut v___x_1741_: u64 = 0;
    let mut v___x_1742_: u64 = 0;
    let mut v___x_1743_: usize = 0;
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: usize = 0;
    let mut v___x_1746_: usize = 0;
    let mut v___x_1747_: usize = 0;
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u64 = 0;
    let mut v_hash_1755_: u64 = 0;
    let mut v_isSharedCheck_1756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1727_) == 0 {
                    return v_x_1726_;
                } else {
                    v_key_1728_ = lean_ctor_get(v_x_1727_, 0);
                    v_value_1729_ = lean_ctor_get(v_x_1727_, 1);
                    v_tail_1730_ = lean_ctor_get(v_x_1727_, 2);
                    v_isSharedCheck_1756_ = (!lean_is_exclusive(v_x_1727_)) as u8;
                    if v_isSharedCheck_1756_ == 0 {
                        v___x_1732_ = v_x_1727_;
                        v_isShared_1733_ = v_isSharedCheck_1756_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1730_);
                        lean_inc(v_value_1729_);
                        lean_inc(v_key_1728_);
                        lean_dec(v_x_1727_);
                        v___x_1732_ = lean_box(0);
                        v_isShared_1733_ = v_isSharedCheck_1756_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1734_ = lean_array_get_size(v_x_1726_);
                if lean_obj_tag(v_key_1728_) == 0 {
                    v___x_1754_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
                    v___y_1736_ = v___x_1754_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1755_ = lean_ctor_get_uint64(
                        v_key_1728_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1736_ = v_hash_1755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1737_ = 32u64;
                v___x_1738_ = lean_uint64_shift_right(v___y_1736_, v___x_1737_);
                v_fold_1739_ = lean_uint64_xor(v___y_1736_, v___x_1738_);
                v___x_1740_ = 16u64;
                v___x_1741_ = lean_uint64_shift_right(v_fold_1739_, v___x_1740_);
                v___x_1742_ = lean_uint64_xor(v_fold_1739_, v___x_1741_);
                v___x_1743_ = lean_uint64_to_usize(v___x_1742_);
                v___x_1744_ = lean_usize_of_nat(v___x_1734_);
                v___x_1745_ = 1usize;
                v___x_1746_ = lean_usize_sub(v___x_1744_, v___x_1745_);
                v___x_1747_ = lean_usize_land(v___x_1743_, v___x_1746_);
                v___x_1748_ = lean_array_uget_borrowed(v_x_1726_, v___x_1747_);
                lean_inc(v___x_1748_);
                if v_isShared_1733_ == 0 {
                    lean_ctor_set(v___x_1732_, 2, v___x_1748_);
                    v___x_1750_ = v___x_1732_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_key_1728_);
                    lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_value_1729_);
                    lean_ctor_set(v_reuseFailAlloc_1753_, 2, v___x_1748_);
                    v___x_1750_ = v_reuseFailAlloc_1753_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1751_ = lean_array_uset(v_x_1726_, v___x_1747_, v___x_1750_);
                v_x_1726_ = v___x_1751_;
                v_x_1727_ = v_tail_1730_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(
    mut v_i_1757_: *mut LeanObject,
    mut v_source_1758_: *mut LeanObject,
    mut v_target_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v_es_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1760_ = lean_array_get_size(v_source_1758_);
                v___x_1761_ = lean_nat_dec_lt(v_i_1757_, v___x_1760_);
                if v___x_1761_ == 0 {
                    lean_dec_ref(v_source_1758_);
                    lean_dec(v_i_1757_);
                    return v_target_1759_;
                } else {
                    v_es_1762_ = lean_array_fget(v_source_1758_, v_i_1757_);
                    v___x_1763_ = lean_box(0);
                    v_source_1764_ = lean_array_fset(v_source_1758_, v_i_1757_, v___x_1763_);
                    v_target_1765_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_target_1759_, v_es_1762_);
                    v___x_1766_ = lean_unsigned_to_nat(1);
                    v___x_1767_ = lean_nat_add(v_i_1757_, v___x_1766_);
                    lean_dec(v_i_1757_);
                    v_i_1757_ = v___x_1767_;
                    v_source_1758_ = v_source_1764_;
                    v_target_1759_ = v_target_1765_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_data_1769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    v___x_1770_ = lean_array_get_size(v_data_1769_);
    v___x_1771_ = lean_unsigned_to_nat(2);
    v_nbuckets_1772_ = lean_nat_mul(v___x_1770_, v___x_1771_);
    v___x_1773_ = lean_unsigned_to_nat(0);
    v___x_1774_ = lean_box(0);
    v___x_1775_ = lean_mk_array(v_nbuckets_1772_, v___x_1774_);
    v___x_1776_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_1773_, v_data_1769_, v___x_1775_);
    return v___x_1776_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(
    mut v_val_1779_: *mut LeanObject,
    mut v_x_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1780_) == 0 {
                    v___x_1785_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0;
                    v___y_1782_ = v___x_1785_;
                    state = 1;
                    continue;
                } else {
                    v_val_1786_ = lean_ctor_get(v_x_1780_, 0);
                    lean_inc(v_val_1786_);
                    lean_dec_ref_known(v_x_1780_, 1);
                    v___y_1782_ = v_val_1786_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1783_ = lean_array_push(v___y_1782_, v_val_1779_);
                v___x_1784_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1784_, 0, v___x_1783_);
                return v___x_1784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(
    mut v_val_1787_: *mut LeanObject,
    mut v_a_1788_: *mut LeanObject,
    mut v_x_1789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1800_: u8 = 0;
    let mut v_tail_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1811_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1789_) == 0 {
                    v___x_1790_ = lean_box(0);
                    v___x_1791_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_1787_, v___x_1790_);
                    v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
                    lean_inc(v_val_1792_);
                    lean_dec(v___x_1791_);
                    v___x_1793_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1793_, 0, v_a_1788_);
                    lean_ctor_set(v___x_1793_, 1, v_val_1792_);
                    lean_ctor_set(v___x_1793_, 2, v_x_1789_);
                    return v___x_1793_;
                } else {
                    v_key_1794_ = lean_ctor_get(v_x_1789_, 0);
                    v_value_1795_ = lean_ctor_get(v_x_1789_, 1);
                    v_tail_1796_ = lean_ctor_get(v_x_1789_, 2);
                    v_isSharedCheck_1811_ = (!lean_is_exclusive(v_x_1789_)) as u8;
                    if v_isSharedCheck_1811_ == 0 {
                        v___x_1798_ = v_x_1789_;
                        v_isShared_1799_ = v_isSharedCheck_1811_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1796_);
                        lean_inc(v_value_1795_);
                        lean_inc(v_key_1794_);
                        lean_dec(v_x_1789_);
                        v___x_1798_ = lean_box(0);
                        v_isShared_1799_ = v_isSharedCheck_1811_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1800_ = lean_name_eq(v_key_1794_, v_a_1788_);
                if v___x_1800_ == 0 {
                    v_tail_1801_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_1787_, v_a_1788_, v_tail_1796_);
                    if v_isShared_1799_ == 0 {
                        lean_ctor_set(v___x_1798_, 2, v_tail_1801_);
                        v___x_1803_ = v___x_1798_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_key_1794_);
                        lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_value_1795_);
                        lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_tail_1801_);
                        v___x_1803_ = v_reuseFailAlloc_1804_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_key_1794_);
                    v___x_1805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1805_, 0, v_value_1795_);
                    v___x_1806_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_1787_, v___x_1805_);
                    v_val_1807_ = lean_ctor_get(v___x_1806_, 0);
                    lean_inc(v_val_1807_);
                    lean_dec(v___x_1806_);
                    if v_isShared_1799_ == 0 {
                        lean_ctor_set(v___x_1798_, 1, v_val_1807_);
                        lean_ctor_set(v___x_1798_, 0, v_a_1788_);
                        v___x_1809_ = v___x_1798_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1788_);
                        lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_val_1807_);
                        lean_ctor_set(v_reuseFailAlloc_1810_, 2, v_tail_1796_);
                        v___x_1809_ = v_reuseFailAlloc_1810_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1803_;
            }
            3 => {
                return v___x_1809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_a_1812_: *mut LeanObject,
    mut v_x_1813_: *mut LeanObject,
) -> u8 {
    let mut v___x_1814_: u8 = 0;
    let mut v_key_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1813_) == 0 {
                    v___x_1814_ = 0;
                    return v___x_1814_;
                } else {
                    v_key_1815_ = lean_ctor_get(v_x_1813_, 0);
                    v_tail_1816_ = lean_ctor_get(v_x_1813_, 2);
                    v___x_1817_ = lean_name_eq(v_key_1815_, v_a_1812_);
                    if v___x_1817_ == 0 {
                        v_x_1813_ = v_tail_1816_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1817_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_a_1819_: *mut LeanObject,
    mut v_x_1820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1821_: u8 = 0;
    let mut v_r_1822_: *mut LeanObject = core::ptr::null_mut();
    v_res_1821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_1819_, v_x_1820_);
    lean_dec(v_x_1820_);
    lean_dec(v_a_1819_);
    v_r_1822_ = lean_box((v_res_1821_) as usize);
    return v_r_1822_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(
    mut v_val_1823_: *mut LeanObject,
    mut v_m_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1829_: usize = 0;
    let mut v___y_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1837_: u8 = 0;
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1840_: u64 = 0;
    let mut v___x_1841_: u64 = 0;
    let mut v___x_1842_: u64 = 0;
    let mut v_fold_1843_: u64 = 0;
    let mut v___x_1844_: u64 = 0;
    let mut v___x_1845_: u64 = 0;
    let mut v___x_1846_: u64 = 0;
    let mut v___x_1847_: usize = 0;
    let mut v___x_1848_: usize = 0;
    let mut v___x_1849_: usize = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: usize = 0;
    let mut v_bkt_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: u8 = 0;
    let mut v_val_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: u8 = 0;
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u64 = 0;
    let mut v_hash_1880_: u64 = 0;
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1833_ = lean_ctor_get(v_m_1824_, 0);
                v_buckets_1834_ = lean_ctor_get(v_m_1824_, 1);
                v_isSharedCheck_1881_ = (!lean_is_exclusive(v_m_1824_)) as u8;
                if v_isSharedCheck_1881_ == 0 {
                    v___x_1836_ = v_m_1824_;
                    v_isShared_1837_ = v_isSharedCheck_1881_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_buckets_1834_);
                    lean_inc(v_size_1833_);
                    lean_dec(v_m_1824_);
                    v___x_1836_ = lean_box(0);
                    v_isShared_1837_ = v_isSharedCheck_1881_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1831_ = lean_array_uset(v___y_1827_, v___y_1829_, v___y_1828_);
                v___x_1832_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1832_, 0, v___y_1830_);
                lean_ctor_set(v___x_1832_, 1, v___x_1831_);
                return v___x_1832_;
            }
            2 => {
                v___x_1838_ = lean_array_get_size(v_buckets_1834_);
                if lean_obj_tag(v_a_1825_) == 0 {
                    v___x_1879_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
                    v___y_1840_ = v___x_1879_;
                    state = 3;
                    continue;
                } else {
                    v_hash_1880_ = lean_ctor_get_uint64(
                        v_a_1825_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1840_ = v_hash_1880_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1841_ = 32u64;
                v___x_1842_ = lean_uint64_shift_right(v___y_1840_, v___x_1841_);
                v_fold_1843_ = lean_uint64_xor(v___y_1840_, v___x_1842_);
                v___x_1844_ = 16u64;
                v___x_1845_ = lean_uint64_shift_right(v_fold_1843_, v___x_1844_);
                v___x_1846_ = lean_uint64_xor(v_fold_1843_, v___x_1845_);
                v___x_1847_ = lean_uint64_to_usize(v___x_1846_);
                v___x_1848_ = lean_usize_of_nat(v___x_1838_);
                v___x_1849_ = 1usize;
                v___x_1850_ = lean_usize_sub(v___x_1848_, v___x_1849_);
                v___x_1851_ = lean_usize_land(v___x_1847_, v___x_1850_);
                v_bkt_1852_ = lean_array_uget_borrowed(v_buckets_1834_, v___x_1851_);
                v___x_1853_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_1825_, v_bkt_1852_);
                if v___x_1853_ == 0 {
                    v___x_1854_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0;
                    v___x_1855_ = lean_array_push(v___x_1854_, v_val_1823_);
                    v___x_1856_ = lean_unsigned_to_nat(1);
                    v_size_x27_1857_ = lean_nat_add(v_size_1833_, v___x_1856_);
                    lean_dec(v_size_1833_);
                    lean_inc(v_bkt_1852_);
                    v___x_1858_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1858_, 0, v_a_1825_);
                    lean_ctor_set(v___x_1858_, 1, v___x_1855_);
                    lean_ctor_set(v___x_1858_, 2, v_bkt_1852_);
                    v_buckets_x27_1859_ =
                        lean_array_uset(v_buckets_1834_, v___x_1851_, v___x_1858_);
                    v___x_1860_ = lean_unsigned_to_nat(4);
                    v___x_1861_ = lean_nat_mul(v_size_x27_1857_, v___x_1860_);
                    v___x_1862_ = lean_unsigned_to_nat(3);
                    v___x_1863_ = lean_nat_div(v___x_1861_, v___x_1862_);
                    lean_dec(v___x_1861_);
                    v___x_1864_ = lean_array_get_size(v_buckets_x27_1859_);
                    v___x_1865_ = lean_nat_dec_le(v___x_1863_, v___x_1864_);
                    lean_dec(v___x_1863_);
                    if v___x_1865_ == 0 {
                        v_val_1866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_1859_);
                        if v_isShared_1837_ == 0 {
                            lean_ctor_set(v___x_1836_, 1, v_val_1866_);
                            lean_ctor_set(v___x_1836_, 0, v_size_x27_1857_);
                            v___x_1868_ = v___x_1836_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_size_x27_1857_);
                            lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_val_1866_);
                            v___x_1868_ = v_reuseFailAlloc_1869_;
                            state = 4;
                            continue;
                        }
                    } else {
                        if v_isShared_1837_ == 0 {
                            lean_ctor_set(v___x_1836_, 1, v_buckets_x27_1859_);
                            lean_ctor_set(v___x_1836_, 0, v_size_x27_1857_);
                            v___x_1871_ = v___x_1836_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_size_x27_1857_);
                            lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_buckets_x27_1859_);
                            v___x_1871_ = v_reuseFailAlloc_1872_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1852_);
                    lean_del_object(v___x_1836_);
                    v___x_1873_ = lean_box(0);
                    v_buckets_x27_1874_ =
                        lean_array_uset(v_buckets_1834_, v___x_1851_, v___x_1873_);
                    lean_inc(v_a_1825_);
                    v_bkt_x27_1875_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_1823_, v_a_1825_, v_bkt_1852_);
                    v___x_1876_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_1825_, v_bkt_x27_1875_);
                    lean_dec(v_a_1825_);
                    if v___x_1876_ == 0 {
                        v___x_1877_ = lean_unsigned_to_nat(1);
                        v___x_1878_ = lean_nat_sub(v_size_1833_, v___x_1877_);
                        lean_dec(v_size_1833_);
                        v___y_1827_ = v_buckets_x27_1874_;
                        v___y_1828_ = v_bkt_x27_1875_;
                        v___y_1829_ = v___x_1851_;
                        v___y_1830_ = v___x_1878_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1827_ = v_buckets_x27_1874_;
                        v___y_1828_ = v_bkt_x27_1875_;
                        v___y_1829_ = v___x_1851_;
                        v___y_1830_ = v_size_1833_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1868_;
            }
            5 => {
                return v___x_1871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(
    mut v_val_1882_: *mut LeanObject,
    mut v_as_1883_: *mut LeanObject,
    mut v_sz_1884_: usize,
    mut v_i_1885_: usize,
    mut v_b_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1887_: u8 = 0;
    let mut v_a_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: usize = 0;
    let mut v___x_1892_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1887_ = lean_usize_dec_lt(v_i_1885_, v_sz_1884_);
                if v___x_1887_ == 0 {
                    lean_dec(v_val_1882_);
                    return v_b_1886_;
                } else {
                    v_a_1888_ = lean_array_uget_borrowed(v_as_1883_, v_i_1885_);
                    v_declName_1889_ = lean_ctor_get(v_a_1888_, 1);
                    lean_inc(v_declName_1889_);
                    lean_inc(v_val_1882_);
                    v___x_1890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(v_val_1882_, v_b_1886_, v_declName_1889_);
                    v___x_1891_ = 1usize;
                    v___x_1892_ = lean_usize_add(v_i_1885_, v___x_1891_);
                    v_i_1885_ = v___x_1892_;
                    v_b_1886_ = v___x_1890_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(
    mut v_val_1894_: *mut LeanObject,
    mut v_as_1895_: *mut LeanObject,
    mut v_sz_1896_: *mut LeanObject,
    mut v_i_1897_: *mut LeanObject,
    mut v_b_1898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1899_: usize = 0;
    let mut v_i_boxed_1900_: usize = 0;
    let mut v_res_1901_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1899_ = lean_unbox_usize(v_sz_1896_);
    lean_dec(v_sz_1896_);
    v_i_boxed_1900_ = lean_unbox_usize(v_i_1897_);
    lean_dec(v_i_1897_);
    v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_1894_, v_as_1895_, v_sz_boxed_1899_, v_i_boxed_1900_, v_b_1898_);
    lean_dec_ref(v_as_1895_);
    return v_res_1901_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(
    mut v_as_1902_: *mut LeanObject,
    mut v_sz_1903_: usize,
    mut v_i_1904_: usize,
    mut v_b_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1906_: u8 = 0;
    let mut v_snd_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v_unused_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v_val_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v_a_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1930_: usize = 0;
    let mut v___x_1931_: usize = 0;
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: usize = 0;
    let mut v___x_1936_: usize = 0;
    let mut v_reuseFailAlloc_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_isSharedCheck_1941_: u8 = 0;
    let mut v_unused_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1906_ = lean_usize_dec_lt(v_i_1904_, v_sz_1903_);
                if v___x_1906_ == 0 {
                    return v_b_1905_;
                } else {
                    v_snd_1907_ = lean_ctor_get(v_b_1905_, 1);
                    lean_inc(v_snd_1907_);
                    if lean_obj_tag(v_snd_1907_) == 0 {
                        v_fst_1908_ = lean_ctor_get(v_b_1905_, 0);
                        v_isSharedCheck_1915_ = (!lean_is_exclusive(v_b_1905_)) as u8;
                        if v_isSharedCheck_1915_ == 0 {
                            v_unused_1916_ = lean_ctor_get(v_b_1905_, 1);
                            lean_dec(v_unused_1916_);
                            v___x_1910_ = v_b_1905_;
                            v_isShared_1911_ = v_isSharedCheck_1915_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_fst_1908_);
                            lean_dec(v_b_1905_);
                            v___x_1910_ = lean_box(0);
                            v_isShared_1911_ = v_isSharedCheck_1915_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_fst_1917_ = lean_ctor_get(v_b_1905_, 0);
                        v_isSharedCheck_1941_ = (!lean_is_exclusive(v_b_1905_)) as u8;
                        if v_isSharedCheck_1941_ == 0 {
                            v_unused_1942_ = lean_ctor_get(v_b_1905_, 1);
                            lean_dec(v_unused_1942_);
                            v___x_1919_ = v_b_1905_;
                            v_isShared_1920_ = v_isSharedCheck_1941_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_fst_1917_);
                            lean_dec(v_b_1905_);
                            v___x_1919_ = lean_box(0);
                            v_isShared_1920_ = v_isSharedCheck_1941_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1911_ == 0 {
                    v___x_1913_ = v___x_1910_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_fst_1908_);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_snd_1907_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1913_;
            }
            3 => {
                v_val_1921_ = lean_ctor_get(v_snd_1907_, 0);
                v_isSharedCheck_1940_ = (!lean_is_exclusive(v_snd_1907_)) as u8;
                if v_isSharedCheck_1940_ == 0 {
                    v___x_1923_ = v_snd_1907_;
                    v_isShared_1924_ = v_isSharedCheck_1940_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_val_1921_);
                    lean_dec(v_snd_1907_);
                    v___x_1923_ = lean_box(0);
                    v_isShared_1924_ = v_isSharedCheck_1940_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_1925_ = lean_array_uget_borrowed(v_as_1902_, v_i_1904_);
                v___x_1926_ = lean_unsigned_to_nat(1);
                v___x_1927_ = lean_nat_add(v_val_1921_, v___x_1926_);
                if v_isShared_1924_ == 0 {
                    lean_ctor_set(v___x_1923_, 0, v___x_1927_);
                    v___x_1929_ = v___x_1923_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1927_);
                    v___x_1929_ = v_reuseFailAlloc_1939_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_sz_1930_ = lean_array_size(v_a_1925_);
                v___x_1931_ = 0usize;
                v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_1921_, v_a_1925_, v_sz_1930_, v___x_1931_, v_fst_1917_);
                if v_isShared_1920_ == 0 {
                    lean_ctor_set(v___x_1919_, 1, v___x_1929_);
                    lean_ctor_set(v___x_1919_, 0, v___x_1932_);
                    v___x_1934_ = v___x_1919_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1932_);
                    lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1929_);
                    v___x_1934_ = v_reuseFailAlloc_1938_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1935_ = 1usize;
                v___x_1936_ = lean_usize_add(v_i_1904_, v___x_1935_);
                v_i_1904_ = v___x_1936_;
                v_b_1905_ = v___x_1934_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(
    mut v_as_1943_: *mut LeanObject,
    mut v_sz_1944_: *mut LeanObject,
    mut v_i_1945_: *mut LeanObject,
    mut v_b_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1947_: usize = 0;
    let mut v_i_boxed_1948_: usize = 0;
    let mut v_res_1949_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1947_ = lean_unbox_usize(v_sz_1944_);
    lean_dec(v_sz_1944_);
    v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
    lean_dec(v_i_1945_);
    v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_as_1943_, v_sz_boxed_1947_, v_i_boxed_1948_, v_b_1946_);
    lean_dec_ref(v_as_1943_);
    return v_res_1949_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    v___x_1950_ = lean_box(0);
    v___x_1951_ = lean_unsigned_to_nat(16);
    v___x_1952_ = lean_mk_array(v___x_1951_, v___x_1950_);
    return v___x_1952_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1955_: *mut LeanObject = core::ptr::null_mut();
    v___x_1953_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once), _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
    v___x_1954_ = lean_unsigned_to_nat(0);
    v_s_1955_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_s_1955_, 0, v___x_1954_);
    lean_ctor_set(v_s_1955_, 1, v___x_1953_);
    return v_s_1955_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    v___x_1958_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
    v_s_1959_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once), _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
    v___x_1960_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1960_, 0, v_s_1959_);
    lean_ctor_set(v___x_1960_, 1, v___x_1958_);
    return v___x_1960_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(
    mut v_es_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1963_: usize = 0;
    let mut v___x_1964_: usize = 0;
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1966_: *mut LeanObject = core::ptr::null_mut();
    v___x_1962_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once), _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
    v_sz_1963_ = lean_array_size(v_es_1961_);
    v___x_1964_ = 0usize;
    v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_es_1961_, v_sz_1963_, v___x_1964_, v___x_1962_);
    v_fst_1966_ = lean_ctor_get(v___x_1965_, 0);
    lean_inc(v_fst_1966_);
    lean_dec_ref(v___x_1965_);
    return v_fst_1966_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(
    mut v_es_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1968_: *mut LeanObject = core::ptr::null_mut();
    v_res_1968_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_es_1967_);
    lean_dec_ref(v_es_1967_);
    return v_res_1968_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    v___x_1985_ = l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
    v___x_1986_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1985_);
    return v___x_1986_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(
    mut v_a_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1988_: *mut LeanObject = core::ptr::null_mut();
    v_res_1988_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
    return v_res_1988_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_1989_: *mut LeanObject,
    mut v_a_1990_: *mut LeanObject,
    mut v_x_1991_: *mut LeanObject,
) -> u8 {
    let mut v___x_1992_: u8 = 0;
    v___x_1992_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_1990_, v_x_1991_);
    return v___x_1992_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_1993_: *mut LeanObject,
    mut v_a_1994_: *mut LeanObject,
    mut v_x_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1996_: u8 = 0;
    let mut v_r_1997_: *mut LeanObject = core::ptr::null_mut();
    v_res_1996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1993_, v_a_1994_, v_x_1995_);
    lean_dec(v_x_1995_);
    lean_dec(v_a_1994_);
    v_r_1997_ = lean_box((v_res_1996_) as usize);
    return v_r_1997_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_1998_: *mut LeanObject,
    mut v_data_1999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___x_2000_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_1999_);
    return v___x_2000_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(
    mut v_00_u03b2_2001_: *mut LeanObject,
    mut v_i_2002_: *mut LeanObject,
    mut v_source_2003_: *mut LeanObject,
    mut v_target_2004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    v___x_2005_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_2002_, v_source_2003_, v_target_2004_);
    return v___x_2005_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2006_: *mut LeanObject,
    mut v_x_2007_: *mut LeanObject,
    mut v_x_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_x_2007_, v_x_2008_);
    return v___x_2009_;
}
pub unsafe fn _init_l_Lean_getIndirectModUses___closed__2() -> *mut LeanObject {
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Lean_getIndirectModUses___closed__1;
    v___x_2013_ = l_Lean_getIndirectModUses___closed__0;
    v___x_2014_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2013_, v___x_2012_);
    return v___x_2014_;
}
pub unsafe fn _init_l_Lean_getIndirectModUses___closed__3() -> *mut LeanObject {
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getIndirectModUses___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getIndirectModUses___closed__2_once),
        _init_l_Lean_getIndirectModUses___closed__2,
    );
    v___x_2016_ = lean_box(0);
    v___x_2017_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2017_, 0, v___x_2016_);
    lean_ctor_set(v___x_2017_, 1, v___x_2015_);
    return v___x_2017_;
}
pub unsafe fn l_Lean_getIndirectModUses(
    mut v_env_2018_: *mut LeanObject,
    mut v_modIdx_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    v___x_2020_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getIndirectModUses___closed__3),
        core::ptr::addr_of_mut!(l_Lean_getIndirectModUses___closed__3_once),
        _init_l_Lean_getIndirectModUses___closed__3,
    );
    v___x_2021_ = l_Lean_indirectModUseExt;
    v___x_2022_ = 0;
    v___x_2023_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
        v___x_2020_,
        v___x_2021_,
        v_env_2018_,
        v_modIdx_2019_,
        v___x_2022_,
    );
    return v___x_2023_;
}
pub unsafe fn l_Lean_getIndirectModUses___boxed(
    mut v_env_2024_: *mut LeanObject,
    mut v_modIdx_2025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2026_: *mut LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_Lean_getIndirectModUses(v_env_2024_, v_modIdx_2025_);
    lean_dec(v_modIdx_2025_);
    lean_dec_ref(v_env_2024_);
    return v_res_2026_;
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg___lam__0(
    mut v___x_2027_: *mut LeanObject,
    mut v___x_2028_: *mut LeanObject,
    mut v_x_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toEnvExtension_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    v_toEnvExtension_2030_ = lean_ctor_get(v___x_2027_, 0);
    v_asyncMode_2031_ = lean_ctor_get(v_toEnvExtension_2030_, 2);
    lean_inc(v_asyncMode_2031_);
    v___x_2032_ = lean_box(0);
    v___x_2033_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_2027_,
        v_x_2029_,
        v___x_2028_,
        v_asyncMode_2031_,
        v___x_2032_,
    );
    lean_dec(v_asyncMode_2031_);
    return v___x_2033_;
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg___lam__1(
    mut v_modifyEnv_2034_: *mut LeanObject,
    mut v___f_2035_: *mut LeanObject,
    mut v_____r_2036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    v___x_2037_ = lean_apply_1(v_modifyEnv_2034_, v___f_2035_);
    return v___x_2037_;
}
pub unsafe fn _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__1() -> *mut LeanObject {
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    v___x_2039_ = l_Lean_recordIndirectModUse___redArg___lam__2___closed__0;
    v___x_2040_ = l_Lean_stringToMessageData(v___x_2039_);
    return v___x_2040_;
}
pub unsafe fn _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__3() -> *mut LeanObject {
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    v___x_2042_ = l_Lean_recordIndirectModUse___redArg___lam__2___closed__2;
    v___x_2043_ = l_Lean_stringToMessageData(v___x_2042_);
    return v___x_2043_;
}
pub unsafe fn _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__5() -> *mut LeanObject {
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    v___x_2045_ = l_Lean_recordIndirectModUse___redArg___lam__2___closed__4;
    v___x_2046_ = l_Lean_stringToMessageData(v___x_2045_);
    return v___x_2046_;
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg___lam__2(
    mut v_modifyEnv_2047_: *mut LeanObject,
    mut v___f_2048_: *mut LeanObject,
    mut v_declName_2049_: *mut LeanObject,
    mut v_kind_2050_: *mut LeanObject,
    mut v_inst_2051_: *mut LeanObject,
    mut v_inst_2052_: *mut LeanObject,
    mut v_inst_2053_: *mut LeanObject,
    mut v_inst_2054_: *mut LeanObject,
    mut v_cls_2055_: *mut LeanObject,
    mut v_toBind_2056_: *mut LeanObject,
    mut v___f_2057_: *mut LeanObject,
    mut v_____do__lift_2058_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2058_ == 0 {
        let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2057_);
        lean_dec(v_toBind_2056_);
        lean_dec(v_cls_2055_);
        lean_dec(v_inst_2054_);
        lean_dec_ref(v_inst_2053_);
        lean_dec_ref(v_inst_2052_);
        lean_dec_ref(v_inst_2051_);
        lean_dec_ref(v_kind_2050_);
        lean_dec(v_declName_2049_);
        v___x_2059_ = lean_apply_1(v_modifyEnv_2047_, v___f_2048_);
        return v___x_2059_;
    } else {
        let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_2048_);
        lean_dec(v_modifyEnv_2047_);
        v___x_2060_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__1),
            core::ptr::addr_of_mut!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_once),
            _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__1,
        );
        v___x_2061_ = l_Lean_MessageData_ofName(v_declName_2049_);
        v___x_2062_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2062_, 0, v___x_2060_);
        lean_ctor_set(v___x_2062_, 1, v___x_2061_);
        v___x_2063_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__3),
            core::ptr::addr_of_mut!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__3_once),
            _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__3,
        );
        v___x_2064_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2064_, 0, v___x_2062_);
        lean_ctor_set(v___x_2064_, 1, v___x_2063_);
        v___x_2065_ = l_Lean_stringToMessageData(v_kind_2050_);
        v___x_2066_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2066_, 0, v___x_2064_);
        lean_ctor_set(v___x_2066_, 1, v___x_2065_);
        v___x_2067_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__5),
            core::ptr::addr_of_mut!(l_Lean_recordIndirectModUse___redArg___lam__2___closed__5_once),
            _init_l_Lean_recordIndirectModUse___redArg___lam__2___closed__5,
        );
        v___x_2068_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2068_, 0, v___x_2066_);
        lean_ctor_set(v___x_2068_, 1, v___x_2067_);
        v___x_2069_ = l_Lean_addTrace___redArg(
            v_inst_2051_,
            v_inst_2052_,
            v_inst_2053_,
            v_inst_2054_,
            v_cls_2055_,
            v___x_2068_,
        );
        v___x_2070_ = lean_apply_4(
            v_toBind_2056_,
            lean_box(0),
            lean_box(0),
            v___x_2069_,
            v___f_2057_,
        );
        return v___x_2070_;
    }
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg___lam__2___boxed(
    mut v_modifyEnv_2071_: *mut LeanObject,
    mut v___f_2072_: *mut LeanObject,
    mut v_declName_2073_: *mut LeanObject,
    mut v_kind_2074_: *mut LeanObject,
    mut v_inst_2075_: *mut LeanObject,
    mut v_inst_2076_: *mut LeanObject,
    mut v_inst_2077_: *mut LeanObject,
    mut v_inst_2078_: *mut LeanObject,
    mut v_cls_2079_: *mut LeanObject,
    mut v_toBind_2080_: *mut LeanObject,
    mut v___f_2081_: *mut LeanObject,
    mut v_____do__lift_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_579__boxed_2083_: u8 = 0;
    let mut v_res_2084_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_579__boxed_2083_ = (lean_unbox(v_____do__lift_2082_) as u8);
    v_res_2084_ = l_Lean_recordIndirectModUse___redArg___lam__2(
        v_modifyEnv_2071_,
        v___f_2072_,
        v_declName_2073_,
        v_kind_2074_,
        v_inst_2075_,
        v_inst_2076_,
        v_inst_2077_,
        v_inst_2078_,
        v_cls_2079_,
        v_toBind_2080_,
        v___f_2081_,
        v_____do__lift_579__boxed_2083_,
    );
    return v_res_2084_;
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg___lam__3(
    mut v_toPure_2088_: *mut LeanObject,
    mut v_cls_2089_: *mut LeanObject,
    mut v_____do__lift_2090_: *mut LeanObject,
    mut v_____do__lift_2091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasTrace_2092_: u8 = 0;
    v_hasTrace_2092_ = lean_ctor_get_uint8(
        v_____do__lift_2091_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_2092_ == 0 {
        let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_cls_2089_);
        v___x_2093_ = lean_box((v_hasTrace_2092_) as usize);
        v___x_2094_ = lean_apply_2(v_toPure_2088_, lean_box(0), v___x_2093_);
        return v___x_2094_;
    } else {
        let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: u8 = 0;
        let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
        v___x_2095_ = l_Lean_recordIndirectModUse___redArg___lam__3___closed__1;
        v___x_2096_ = l_Lean_Name_append(v___x_2095_, v_cls_2089_);
        v___x_2097_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_2090_,
            v_____do__lift_2091_,
            v___x_2096_,
        );
        lean_dec(v___x_2096_);
        v___x_2098_ = lean_box((v___x_2097_) as usize);
        v___x_2099_ = lean_apply_2(v_toPure_2088_, lean_box(0), v___x_2098_);
        return v___x_2099_;
    }
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg___lam__3___boxed(
    mut v_toPure_2100_: *mut LeanObject,
    mut v_cls_2101_: *mut LeanObject,
    mut v_____do__lift_2102_: *mut LeanObject,
    mut v_____do__lift_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2104_: *mut LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_Lean_recordIndirectModUse___redArg___lam__3(
        v_toPure_2100_,
        v_cls_2101_,
        v_____do__lift_2102_,
        v_____do__lift_2103_,
    );
    lean_dec_ref(v_____do__lift_2103_);
    lean_dec_ref(v_____do__lift_2102_);
    return v_res_2104_;
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg___lam__4(
    mut v_toPure_2105_: *mut LeanObject,
    mut v_cls_2106_: *mut LeanObject,
    mut v_toBind_2107_: *mut LeanObject,
    mut v_inst_2108_: *mut LeanObject,
    mut v_____do__lift_2109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    v___f_2110_ = lean_alloc_closure(
        l_Lean_recordIndirectModUse___redArg___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2110_, 0, v_toPure_2105_);
    lean_closure_set(v___f_2110_, 1, v_cls_2106_);
    lean_closure_set(v___f_2110_, 2, v_____do__lift_2109_);
    v___x_2111_ = lean_apply_4(
        v_toBind_2107_,
        lean_box(0),
        lean_box(0),
        v_inst_2108_,
        v___f_2110_,
    );
    return v___x_2111_;
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg___lam__5(
    mut v___x_2115_: *mut LeanObject,
    mut v_kind_2116_: *mut LeanObject,
    mut v_declName_2117_: *mut LeanObject,
    mut v___x_2118_: *mut LeanObject,
    mut v_inst_2119_: *mut LeanObject,
    mut v_toApplicative_2120_: *mut LeanObject,
    mut v_modifyEnv_2121_: *mut LeanObject,
    mut v_inst_2122_: *mut LeanObject,
    mut v_inst_2123_: *mut LeanObject,
    mut v_inst_2124_: *mut LeanObject,
    mut v_toBind_2125_: *mut LeanObject,
    mut v_inst_2126_: *mut LeanObject,
    mut v_____do__lift_2127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    v___x_2128_ = l_Lean_indirectModUseExt;
    v___x_2129_ = lean_box(2);
    v___x_2130_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
        v___x_2115_,
        v___x_2128_,
        v_____do__lift_2127_,
        v___x_2129_,
    );
    lean_inc(v_declName_2117_);
    lean_inc_ref(v_kind_2116_);
    v___x_2131_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2131_, 0, v_kind_2116_);
    lean_ctor_set(v___x_2131_, 1, v_declName_2117_);
    lean_inc_ref(v___x_2131_);
    v___x_2132_ = l_List_elem___redArg(v___x_2118_, v___x_2131_, v___x_2130_);
    if v___x_2132_ == 0 {
        let mut v_getInheritedTraceOptions_2133_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2136_: *mut LeanObject = core::ptr::null_mut();
        let mut v_cls_2137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_2133_ = lean_ctor_get(v_inst_2119_, 2);
        lean_inc(v_getInheritedTraceOptions_2133_);
        v_toPure_2134_ = lean_ctor_get(v_toApplicative_2120_, 1);
        lean_inc(v_toPure_2134_);
        lean_dec_ref(v_toApplicative_2120_);
        v___f_2135_ = lean_alloc_closure(
            l_Lean_recordIndirectModUse___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_2135_, 0, v___x_2128_);
        lean_closure_set(v___f_2135_, 1, v___x_2131_);
        lean_inc_ref(v___f_2135_);
        lean_inc(v_modifyEnv_2121_);
        v___f_2136_ = lean_alloc_closure(
            l_Lean_recordIndirectModUse___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_2136_, 0, v_modifyEnv_2121_);
        lean_closure_set(v___f_2136_, 1, v___f_2135_);
        v_cls_2137_ = l_Lean_recordIndirectModUse___redArg___lam__5___closed__1;
        lean_inc_n(v_toBind_2125_, 3);
        v___f_2138_ = lean_alloc_closure(
            l_Lean_recordIndirectModUse___redArg___lam__2___boxed as *mut core::ffi::c_void,
            12,
            11,
        );
        lean_closure_set(v___f_2138_, 0, v_modifyEnv_2121_);
        lean_closure_set(v___f_2138_, 1, v___f_2135_);
        lean_closure_set(v___f_2138_, 2, v_declName_2117_);
        lean_closure_set(v___f_2138_, 3, v_kind_2116_);
        lean_closure_set(v___f_2138_, 4, v_inst_2122_);
        lean_closure_set(v___f_2138_, 5, v_inst_2119_);
        lean_closure_set(v___f_2138_, 6, v_inst_2123_);
        lean_closure_set(v___f_2138_, 7, v_inst_2124_);
        lean_closure_set(v___f_2138_, 8, v_cls_2137_);
        lean_closure_set(v___f_2138_, 9, v_toBind_2125_);
        lean_closure_set(v___f_2138_, 10, v___f_2136_);
        v___f_2139_ = lean_alloc_closure(
            l_Lean_recordIndirectModUse___redArg___lam__4 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_2139_, 0, v_toPure_2134_);
        lean_closure_set(v___f_2139_, 1, v_cls_2137_);
        lean_closure_set(v___f_2139_, 2, v_toBind_2125_);
        lean_closure_set(v___f_2139_, 3, v_inst_2126_);
        v___x_2140_ = lean_apply_4(
            v_toBind_2125_,
            lean_box(0),
            lean_box(0),
            v_getInheritedTraceOptions_2133_,
            v___f_2139_,
        );
        v___x_2141_ = lean_apply_4(
            v_toBind_2125_,
            lean_box(0),
            lean_box(0),
            v___x_2140_,
            v___f_2138_,
        );
        return v___x_2141_;
    } else {
        let mut v_toPure_2142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2131_, 2);
        lean_dec(v_inst_2126_);
        lean_dec(v_toBind_2125_);
        lean_dec(v_inst_2124_);
        lean_dec_ref(v_inst_2123_);
        lean_dec_ref(v_inst_2122_);
        lean_dec(v_modifyEnv_2121_);
        lean_dec_ref(v_inst_2119_);
        lean_dec(v_declName_2117_);
        lean_dec_ref(v_kind_2116_);
        v_toPure_2142_ = lean_ctor_get(v_toApplicative_2120_, 1);
        lean_inc(v_toPure_2142_);
        lean_dec_ref(v_toApplicative_2120_);
        v___x_2143_ = lean_box(0);
        v___x_2144_ = lean_apply_2(v_toPure_2142_, lean_box(0), v___x_2143_);
        return v___x_2144_;
    }
}
pub unsafe fn l_Lean_recordIndirectModUse___redArg(
    mut v_inst_2145_: *mut LeanObject,
    mut v_inst_2146_: *mut LeanObject,
    mut v_inst_2147_: *mut LeanObject,
    mut v_inst_2148_: *mut LeanObject,
    mut v_inst_2149_: *mut LeanObject,
    mut v_inst_2150_: *mut LeanObject,
    mut v_kind_2151_: *mut LeanObject,
    mut v_declName_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2153_ = lean_ctor_get(v_inst_2145_, 0);
    lean_inc_ref(v_toApplicative_2153_);
    v_toBind_2154_ = lean_ctor_get(v_inst_2145_, 1);
    lean_inc_n(v_toBind_2154_, 2);
    v_getEnv_2155_ = lean_ctor_get(v_inst_2146_, 0);
    lean_inc(v_getEnv_2155_);
    v_modifyEnv_2156_ = lean_ctor_get(v_inst_2146_, 1);
    lean_inc(v_modifyEnv_2156_);
    lean_dec_ref(v_inst_2146_);
    v___x_2157_ = l_Lean_instBEqIndirectModUse___closed__0;
    v___x_2158_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getIndirectModUses___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getIndirectModUses___closed__2_once),
        _init_l_Lean_getIndirectModUses___closed__2,
    );
    v___f_2159_ = lean_alloc_closure(
        l_Lean_recordIndirectModUse___redArg___lam__5 as *mut core::ffi::c_void,
        13,
        12,
    );
    lean_closure_set(v___f_2159_, 0, v___x_2158_);
    lean_closure_set(v___f_2159_, 1, v_kind_2151_);
    lean_closure_set(v___f_2159_, 2, v_declName_2152_);
    lean_closure_set(v___f_2159_, 3, v___x_2157_);
    lean_closure_set(v___f_2159_, 4, v_inst_2147_);
    lean_closure_set(v___f_2159_, 5, v_toApplicative_2153_);
    lean_closure_set(v___f_2159_, 6, v_modifyEnv_2156_);
    lean_closure_set(v___f_2159_, 7, v_inst_2145_);
    lean_closure_set(v___f_2159_, 8, v_inst_2149_);
    lean_closure_set(v___f_2159_, 9, v_inst_2150_);
    lean_closure_set(v___f_2159_, 10, v_toBind_2154_);
    lean_closure_set(v___f_2159_, 11, v_inst_2148_);
    v___x_2160_ = lean_apply_4(
        v_toBind_2154_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2155_,
        v___f_2159_,
    );
    return v___x_2160_;
}
pub unsafe fn l_Lean_recordIndirectModUse(
    mut v_m_2161_: *mut LeanObject,
    mut v_inst_2162_: *mut LeanObject,
    mut v_inst_2163_: *mut LeanObject,
    mut v_inst_2164_: *mut LeanObject,
    mut v_inst_2165_: *mut LeanObject,
    mut v_inst_2166_: *mut LeanObject,
    mut v_inst_2167_: *mut LeanObject,
    mut v_kind_2168_: *mut LeanObject,
    mut v_declName_2169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    v___x_2170_ = l_Lean_recordIndirectModUse___redArg(
        v_inst_2162_,
        v_inst_2163_,
        v_inst_2164_,
        v_inst_2165_,
        v_inst_2166_,
        v_inst_2167_,
        v_kind_2168_,
        v_declName_2169_,
    );
    return v___x_2170_;
}
pub unsafe fn l_Lean_instBEqExtraModUse_beq(
    mut v_x_2171_: *mut LeanObject,
    mut v_x_2172_: *mut LeanObject,
) -> u8 {
    let mut v_module_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExported_2174_: u8 = 0;
    let mut v_isMeta_2175_: u8 = 0;
    let mut v_module_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExported_2177_: u8 = 0;
    let mut v_isMeta_2178_: u8 = 0;
    let mut v___y_2180_: u8 = 0;
    let mut v___x_2181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_2173_ = lean_ctor_get(v_x_2171_, 0);
                v_isExported_2174_ = lean_ctor_get_uint8(
                    v_x_2171_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isMeta_2175_ = lean_ctor_get_uint8(
                    v_x_2171_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_module_2176_ = lean_ctor_get(v_x_2172_, 0);
                v_isExported_2177_ = lean_ctor_get_uint8(
                    v_x_2172_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isMeta_2178_ = lean_ctor_get_uint8(
                    v_x_2172_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v___x_2181_ = lean_name_eq(v_module_2173_, v_module_2176_);
                if v___x_2181_ == 0 {
                    return v___x_2181_;
                } else {
                    if v_isExported_2174_ == 0 {
                        if v_isExported_2177_ == 0 {
                            v___y_2180_ = v___x_2181_;
                            state = 1;
                            continue;
                        } else {
                            return v_isExported_2174_;
                        }
                    } else {
                        v___y_2180_ = v_isExported_2177_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2180_ == 0 {
                    return v___y_2180_;
                } else {
                    if v_isMeta_2175_ == 0 {
                        if v_isMeta_2178_ == 0 {
                            return v___y_2180_;
                        } else {
                            return v_isMeta_2175_;
                        }
                    } else {
                        return v_isMeta_2178_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instBEqExtraModUse_beq___boxed(
    mut v_x_2182_: *mut LeanObject,
    mut v_x_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2184_: u8 = 0;
    let mut v_r_2185_: *mut LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Lean_instBEqExtraModUse_beq(v_x_2182_, v_x_2183_);
    lean_dec_ref(v_x_2183_);
    lean_dec_ref(v_x_2182_);
    v_r_2185_ = lean_box((v_res_2184_) as usize);
    return v_r_2185_;
}
pub unsafe fn l_Lean_instHashableExtraModUse_hash(mut v_x_2188_: *mut LeanObject) -> u64 {
    let mut v_module_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExported_2190_: u8 = 0;
    let mut v_isMeta_2191_: u8 = 0;
    let mut v___y_2193_: u64 = 0;
    let mut v___y_2194_: u64 = 0;
    let mut v___x_2195_: u64 = 0;
    let mut v___x_2196_: u64 = 0;
    let mut v___x_2197_: u64 = 0;
    let mut v___x_2198_: u64 = 0;
    let mut v___x_2199_: u64 = 0;
    let mut v___x_2200_: u64 = 0;
    let mut v___y_2202_: u64 = 0;
    let mut v___x_2203_: u64 = 0;
    let mut v___x_2204_: u64 = 0;
    let mut v___x_2205_: u64 = 0;
    let mut v___x_2206_: u64 = 0;
    let mut v_hash_2207_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_2189_ = lean_ctor_get(v_x_2188_, 0);
                v_isExported_2190_ = lean_ctor_get_uint8(
                    v_x_2188_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isMeta_2191_ = lean_ctor_get_uint8(
                    v_x_2188_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v___x_2200_ = 0u64;
                if lean_obj_tag(v_module_2189_) == 0 {
                    v___x_2206_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
                    v___y_2202_ = v___x_2206_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2207_ = lean_ctor_get_uint64(
                        v_module_2189_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2202_ = v_hash_2207_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2195_ = lean_uint64_mix_hash(v___y_2193_, v___y_2194_);
                if v_isMeta_2191_ == 0 {
                    v___x_2196_ = 13u64;
                    v___x_2197_ = lean_uint64_mix_hash(v___x_2195_, v___x_2196_);
                    return v___x_2197_;
                } else {
                    v___x_2198_ = 11u64;
                    v___x_2199_ = lean_uint64_mix_hash(v___x_2195_, v___x_2198_);
                    return v___x_2199_;
                }
            }
            2 => {
                v___x_2203_ = lean_uint64_mix_hash(v___x_2200_, v___y_2202_);
                if v_isExported_2190_ == 0 {
                    v___x_2204_ = 13u64;
                    v___y_2193_ = v___x_2203_;
                    v___y_2194_ = v___x_2204_;
                    state = 1;
                    continue;
                } else {
                    v___x_2205_ = 11u64;
                    v___y_2193_ = v___x_2203_;
                    v___y_2194_ = v___x_2205_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instHashableExtraModUse_hash___boxed(
    mut v_x_2208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2209_: u64 = 0;
    let mut v_r_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2209_ = l_Lean_instHashableExtraModUse_hash(v_x_2208_);
    lean_dec_ref(v_x_2208_);
    v_r_2210_ = lean_box_uint64(v_res_2209_);
    return v_r_2210_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(
    mut v_a_2213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    v___x_2214_ = lean_nat_to_int(v_a_2213_);
    return v___x_2214_;
}
pub unsafe fn _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    v___x_2228_ = lean_unsigned_to_nat(10);
    v___x_2229_ = lean_nat_to_int(v___x_2228_);
    return v___x_2229_;
}
pub unsafe fn _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    v___x_2236_ = lean_unsigned_to_nat(14);
    v___x_2237_ = lean_nat_to_int(v___x_2236_);
    return v___x_2237_;
}
pub unsafe fn _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16() -> *mut LeanObject {
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    v___x_2242_ = l_Lean_instReprExtraModUse_repr___redArg___closed__0;
    v___x_2243_ = lean_string_length(v___x_2242_);
    return v___x_2243_;
}
pub unsafe fn _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17() -> *mut LeanObject {
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    v___x_2244_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprExtraModUse_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_instReprExtraModUse_repr___redArg___closed__16_once),
        _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16,
    );
    v___x_2245_ = lean_nat_to_int(v___x_2244_);
    return v___x_2245_;
}
pub unsafe fn l_Lean_instReprExtraModUse_repr___redArg(
    mut v_x_2250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_module_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExported_2252_: u8 = 0;
    let mut v_isMeta_2253_: u8 = 0;
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    v_module_2251_ = lean_ctor_get(v_x_2250_, 0);
    lean_inc(v_module_2251_);
    v_isExported_2252_ = lean_ctor_get_uint8(
        v_x_2250_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_isMeta_2253_ = lean_ctor_get_uint8(
        v_x_2250_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
    );
    lean_dec_ref(v_x_2250_);
    v___x_2254_ = l_Lean_instReprExtraModUse_repr___redArg___closed__5;
    v___x_2255_ = l_Lean_instReprExtraModUse_repr___redArg___closed__6;
    v___x_2256_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprExtraModUse_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprExtraModUse_repr___redArg___closed__7_once),
        _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7,
    );
    v___x_2257_ = lean_unsigned_to_nat(0);
    v___x_2258_ = l_Lean_Name_reprPrec(v_module_2251_, v___x_2257_);
    v___x_2259_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2259_, 0, v___x_2256_);
    lean_ctor_set(v___x_2259_, 1, v___x_2258_);
    v___x_2260_ = 0;
    v___x_2261_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2261_, 0, v___x_2259_);
    lean_ctor_set_uint8(
        v___x_2261_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2260_,
    );
    v___x_2262_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2262_, 0, v___x_2255_);
    lean_ctor_set(v___x_2262_, 1, v___x_2261_);
    v___x_2263_ = l_Lean_instReprExtraModUse_repr___redArg___closed__9;
    v___x_2264_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2264_, 0, v___x_2262_);
    lean_ctor_set(v___x_2264_, 1, v___x_2263_);
    v___x_2265_ = lean_box(1);
    v___x_2266_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2266_, 0, v___x_2264_);
    lean_ctor_set(v___x_2266_, 1, v___x_2265_);
    v___x_2267_ = l_Lean_instReprExtraModUse_repr___redArg___closed__11;
    v___x_2268_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2268_, 0, v___x_2266_);
    lean_ctor_set(v___x_2268_, 1, v___x_2267_);
    v___x_2269_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2269_, 0, v___x_2268_);
    lean_ctor_set(v___x_2269_, 1, v___x_2254_);
    v___x_2270_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprExtraModUse_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instReprExtraModUse_repr___redArg___closed__12_once),
        _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12,
    );
    v___x_2271_ = l_Bool_repr___redArg(v_isExported_2252_);
    v___x_2272_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2272_, 0, v___x_2270_);
    lean_ctor_set(v___x_2272_, 1, v___x_2271_);
    v___x_2273_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2273_, 0, v___x_2272_);
    lean_ctor_set_uint8(
        v___x_2273_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2260_,
    );
    v___x_2274_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2274_, 0, v___x_2269_);
    lean_ctor_set(v___x_2274_, 1, v___x_2273_);
    v___x_2275_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2275_, 0, v___x_2274_);
    lean_ctor_set(v___x_2275_, 1, v___x_2263_);
    v___x_2276_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2276_, 0, v___x_2275_);
    lean_ctor_set(v___x_2276_, 1, v___x_2265_);
    v___x_2277_ = l_Lean_instReprExtraModUse_repr___redArg___closed__14;
    v___x_2278_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2278_, 0, v___x_2276_);
    lean_ctor_set(v___x_2278_, 1, v___x_2277_);
    v___x_2279_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2279_, 0, v___x_2278_);
    lean_ctor_set(v___x_2279_, 1, v___x_2254_);
    v___x_2280_ = l_Bool_repr___redArg(v_isMeta_2253_);
    v___x_2281_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2281_, 0, v___x_2256_);
    lean_ctor_set(v___x_2281_, 1, v___x_2280_);
    v___x_2282_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2282_, 0, v___x_2281_);
    lean_ctor_set_uint8(
        v___x_2282_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2260_,
    );
    v___x_2283_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2283_, 0, v___x_2279_);
    lean_ctor_set(v___x_2283_, 1, v___x_2282_);
    v___x_2284_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprExtraModUse_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_instReprExtraModUse_repr___redArg___closed__17_once),
        _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17,
    );
    v___x_2285_ = l_Lean_instReprExtraModUse_repr___redArg___closed__18;
    v___x_2286_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2286_, 0, v___x_2285_);
    lean_ctor_set(v___x_2286_, 1, v___x_2283_);
    v___x_2287_ = l_Lean_instReprExtraModUse_repr___redArg___closed__19;
    v___x_2288_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2288_, 0, v___x_2286_);
    lean_ctor_set(v___x_2288_, 1, v___x_2287_);
    v___x_2289_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2289_, 0, v___x_2284_);
    lean_ctor_set(v___x_2289_, 1, v___x_2288_);
    v___x_2290_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2290_, 0, v___x_2289_);
    lean_ctor_set_uint8(
        v___x_2290_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2260_,
    );
    return v___x_2290_;
}
pub unsafe fn l_Lean_instReprExtraModUse_repr(
    mut v_x_2291_: *mut LeanObject,
    mut v_prec_2292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Lean_instReprExtraModUse_repr___redArg(v_x_2291_);
    return v___x_2293_;
}
pub unsafe fn l_Lean_instReprExtraModUse_repr___boxed(
    mut v_x_2294_: *mut LeanObject,
    mut v_prec_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2296_: *mut LeanObject = core::ptr::null_mut();
    v_res_2296_ = l_Lean_instReprExtraModUse_repr(v_x_2294_, v_prec_2295_);
    lean_dec(v_prec_2295_);
    return v_res_2296_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2299_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2300_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
    v___x_2301_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2301_, 0, v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2303_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__1);
    return v___x_2303_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(
    mut v_x_2306_: *mut LeanObject,
    mut v_x_2307_: *mut LeanObject,
    mut v_entries_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    v___x_2309_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_;
    v___x_2310_ = lean_array_mk(v_entries_2308_);
    v___x_2311_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2311_, 0, v___x_2309_);
    lean_ctor_set(v___x_2311_, 1, v___x_2309_);
    lean_ctor_set(v___x_2311_, 2, v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(
    mut v_x_2312_: *mut LeanObject,
    mut v_x_2313_: *mut LeanObject,
    mut v_entries_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2315_: *mut LeanObject = core::ptr::null_mut();
    v_res_2315_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_2312_, v_x_2313_, v_entries_2314_);
    lean_dec_ref(v_x_2313_);
    lean_dec_ref(v_x_2312_);
    return v_res_2315_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(
    mut v_es_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    v___x_2317_ = lean_array_mk(v_es_2316_);
    return v___x_2317_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    v___x_2318_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_box(0));
    return v___x_2318_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(
    mut v_x_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    v___x_2320_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__once), _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_);
    return v___x_2320_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(
    mut v_x_2321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2322_: *mut LeanObject = core::ptr::null_mut();
    v_res_2322_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_2321_);
    lean_dec_ref(v_x_2321_);
    return v_res_2322_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(
    mut v_x_2323_: *mut LeanObject,
    mut v_x_2324_: *mut LeanObject,
    mut v_x_2325_: *mut LeanObject,
    mut v_x_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2331_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: u8 = 0;
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2327_ = lean_ctor_get(v_x_2323_, 0);
                v_vs_2328_ = lean_ctor_get(v_x_2323_, 1);
                v_isSharedCheck_2352_ = (!lean_is_exclusive(v_x_2323_)) as u8;
                if v_isSharedCheck_2352_ == 0 {
                    v___x_2330_ = v_x_2323_;
                    v_isShared_2331_ = v_isSharedCheck_2352_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2328_);
                    lean_inc(v_ks_2327_);
                    lean_dec(v_x_2323_);
                    v___x_2330_ = lean_box(0);
                    v_isShared_2331_ = v_isSharedCheck_2352_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2332_ = lean_array_get_size(v_ks_2327_);
                v___x_2333_ = lean_nat_dec_lt(v_x_2324_, v___x_2332_);
                if v___x_2333_ == 0 {
                    lean_dec(v_x_2324_);
                    v___x_2334_ = lean_array_push(v_ks_2327_, v_x_2325_);
                    v___x_2335_ = lean_array_push(v_vs_2328_, v_x_2326_);
                    if v_isShared_2331_ == 0 {
                        lean_ctor_set(v___x_2330_, 1, v___x_2335_);
                        lean_ctor_set(v___x_2330_, 0, v___x_2334_);
                        v___x_2337_ = v___x_2330_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2334_);
                        lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2335_);
                        v___x_2337_ = v_reuseFailAlloc_2338_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2339_ = lean_array_fget_borrowed(v_ks_2327_, v_x_2324_);
                    v___x_2340_ = l_Lean_instBEqExtraModUse_beq(v_x_2325_, v_k_x27_2339_);
                    if v___x_2340_ == 0 {
                        if v_isShared_2331_ == 0 {
                            v___x_2342_ = v___x_2330_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_ks_2327_);
                            lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_vs_2328_);
                            v___x_2342_ = v_reuseFailAlloc_2346_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2347_ = lean_array_fset(v_ks_2327_, v_x_2324_, v_x_2325_);
                        v___x_2348_ = lean_array_fset(v_vs_2328_, v_x_2324_, v_x_2326_);
                        lean_dec(v_x_2324_);
                        if v_isShared_2331_ == 0 {
                            lean_ctor_set(v___x_2330_, 1, v___x_2348_);
                            lean_ctor_set(v___x_2330_, 0, v___x_2347_);
                            v___x_2350_ = v___x_2330_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2347_);
                            lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_2348_);
                            v___x_2350_ = v_reuseFailAlloc_2351_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2337_;
            }
            3 => {
                v___x_2343_ = lean_unsigned_to_nat(1);
                v___x_2344_ = lean_nat_add(v_x_2324_, v___x_2343_);
                lean_dec(v_x_2324_);
                v_x_2323_ = v___x_2342_;
                v_x_2324_ = v___x_2344_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(
    mut v_n_2353_: *mut LeanObject,
    mut v_k_2354_: *mut LeanObject,
    mut v_v_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    v___x_2356_ = lean_unsigned_to_nat(0);
    v___x_2357_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_2353_, v___x_2356_, v_k_2354_, v_v_2355_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_2358_: usize = 0;
    let mut v___x_2359_: usize = 0;
    let mut v___x_2360_: usize = 0;
    v___x_2358_ = 5usize;
    v___x_2359_ = 1usize;
    v___x_2360_ = lean_usize_shift_left(v___x_2359_, v___x_2358_);
    return v___x_2360_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2363_: usize = 0;
    v___x_2361_ = 1usize;
    v___x_2362_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
    v___x_2363_ = lean_usize_sub(v___x_2362_, v___x_2361_);
    return v___x_2363_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2364_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2364_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(
    mut v_x_2365_: *mut LeanObject,
    mut v_x_2366_: usize,
    mut v_x_2367_: usize,
    mut v_x_2368_: *mut LeanObject,
    mut v_x_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: usize = 0;
    let mut v___x_2372_: usize = 0;
    let mut v___x_2373_: usize = 0;
    let mut v___x_2374_: usize = 0;
    let mut v_j_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v_v_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v___x_2395_: u8 = 0;
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_node_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2406_: usize = 0;
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2412_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_unused_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2420_: u8 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2425_: u8 = 0;
    let mut v_ks_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: usize = 0;
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    let mut v_reuseFailAlloc_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2365_) == 0 {
                    v_es_2370_ = lean_ctor_get(v_x_2365_, 0);
                    v___x_2371_ = 5usize;
                    v___x_2372_ = 1usize;
                    v___x_2373_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1);
                    v___x_2374_ = lean_usize_land(v_x_2366_, v___x_2373_);
                    v_j_2375_ = lean_usize_to_nat(v___x_2374_);
                    v___x_2376_ = lean_array_get_size(v_es_2370_);
                    v___x_2377_ = lean_nat_dec_lt(v_j_2375_, v___x_2376_);
                    if v___x_2377_ == 0 {
                        lean_dec(v_j_2375_);
                        lean_dec(v_x_2369_);
                        lean_dec_ref(v_x_2368_);
                        return v_x_2365_;
                    } else {
                        lean_inc_ref(v_es_2370_);
                        v_isSharedCheck_2414_ = (!lean_is_exclusive(v_x_2365_)) as u8;
                        if v_isSharedCheck_2414_ == 0 {
                            v_unused_2415_ = lean_ctor_get(v_x_2365_, 0);
                            lean_dec(v_unused_2415_);
                            v___x_2379_ = v_x_2365_;
                            v_isShared_2380_ = v_isSharedCheck_2414_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2365_);
                            v___x_2379_ = lean_box(0);
                            v_isShared_2380_ = v_isSharedCheck_2414_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2416_ = lean_ctor_get(v_x_2365_, 0);
                    v_vs_2417_ = lean_ctor_get(v_x_2365_, 1);
                    v_isSharedCheck_2437_ = (!lean_is_exclusive(v_x_2365_)) as u8;
                    if v_isSharedCheck_2437_ == 0 {
                        v___x_2419_ = v_x_2365_;
                        v_isShared_2420_ = v_isSharedCheck_2437_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2417_);
                        lean_inc(v_ks_2416_);
                        lean_dec(v_x_2365_);
                        v___x_2419_ = lean_box(0);
                        v_isShared_2420_ = v_isSharedCheck_2437_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2381_ = lean_array_fget(v_es_2370_, v_j_2375_);
                v___x_2382_ = lean_box(0);
                v_xs_x27_2383_ = lean_array_fset(v_es_2370_, v_j_2375_, v___x_2382_);
                match lean_obj_tag(v_v_2381_) {
                    0 => {
                        v_key_2390_ = lean_ctor_get(v_v_2381_, 0);
                        v_val_2391_ = lean_ctor_get(v_v_2381_, 1);
                        v_isSharedCheck_2401_ = (!lean_is_exclusive(v_v_2381_)) as u8;
                        if v_isSharedCheck_2401_ == 0 {
                            v___x_2393_ = v_v_2381_;
                            v_isShared_2394_ = v_isSharedCheck_2401_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2391_);
                            lean_inc(v_key_2390_);
                            lean_dec(v_v_2381_);
                            v___x_2393_ = lean_box(0);
                            v_isShared_2394_ = v_isSharedCheck_2401_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2402_ = lean_ctor_get(v_v_2381_, 0);
                        v_isSharedCheck_2412_ = (!lean_is_exclusive(v_v_2381_)) as u8;
                        if v_isSharedCheck_2412_ == 0 {
                            v___x_2404_ = v_v_2381_;
                            v_isShared_2405_ = v_isSharedCheck_2412_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2402_);
                            lean_dec(v_v_2381_);
                            v___x_2404_ = lean_box(0);
                            v_isShared_2405_ = v_isSharedCheck_2412_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2413_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2413_, 0, v_x_2368_);
                        lean_ctor_set(v___x_2413_, 1, v_x_2369_);
                        v___y_2385_ = v___x_2413_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2386_ = lean_array_fset(v_xs_x27_2383_, v_j_2375_, v___y_2385_);
                lean_dec(v_j_2375_);
                if v_isShared_2380_ == 0 {
                    lean_ctor_set(v___x_2379_, 0, v___x_2386_);
                    v___x_2388_ = v___x_2379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
                    v___x_2388_ = v_reuseFailAlloc_2389_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2388_;
            }
            4 => {
                v___x_2395_ = l_Lean_instBEqExtraModUse_beq(v_x_2368_, v_key_2390_);
                if v___x_2395_ == 0 {
                    lean_del_object(v___x_2393_);
                    v___x_2396_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2390_,
                        v_val_2391_,
                        v_x_2368_,
                        v_x_2369_,
                    );
                    v___x_2397_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2397_, 0, v___x_2396_);
                    v___y_2385_ = v___x_2397_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2391_);
                    lean_dec(v_key_2390_);
                    if v_isShared_2394_ == 0 {
                        lean_ctor_set(v___x_2393_, 1, v_x_2369_);
                        lean_ctor_set(v___x_2393_, 0, v_x_2368_);
                        v___x_2399_ = v___x_2393_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_x_2368_);
                        lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_x_2369_);
                        v___x_2399_ = v_reuseFailAlloc_2400_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2385_ = v___x_2399_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2406_ = lean_usize_shift_right(v_x_2366_, v___x_2371_);
                v___x_2407_ = lean_usize_add(v_x_2367_, v___x_2372_);
                v___x_2408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_2402_, v___x_2406_, v___x_2407_, v_x_2368_, v_x_2369_);
                if v_isShared_2405_ == 0 {
                    lean_ctor_set(v___x_2404_, 0, v___x_2408_);
                    v___x_2410_ = v___x_2404_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
                    v___x_2410_ = v_reuseFailAlloc_2411_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2385_ = v___x_2410_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2420_ == 0 {
                    v___x_2422_ = v___x_2419_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_ks_2416_);
                    lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_vs_2417_);
                    v___x_2422_ = v_reuseFailAlloc_2436_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2423_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_2422_, v_x_2368_, v_x_2369_);
                v___x_2431_ = 7usize;
                v___x_2432_ = lean_usize_dec_le(v___x_2431_, v_x_2367_);
                if v___x_2432_ == 0 {
                    v___x_2433_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2423_);
                    v___x_2434_ = lean_unsigned_to_nat(4);
                    v___x_2435_ = lean_nat_dec_lt(v___x_2433_, v___x_2434_);
                    lean_dec(v___x_2433_);
                    v___y_2425_ = v___x_2435_;
                    state = 10;
                    continue;
                } else {
                    v___y_2425_ = v___x_2432_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2425_ == 0 {
                    v_ks_2426_ = lean_ctor_get(v_newNode_2423_, 0);
                    lean_inc_ref(v_ks_2426_);
                    v_vs_2427_ = lean_ctor_get(v_newNode_2423_, 1);
                    lean_inc_ref(v_vs_2427_);
                    lean_dec_ref(v_newNode_2423_);
                    v___x_2428_ = lean_unsigned_to_nat(0);
                    v___x_2429_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__2);
                    v___x_2430_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_2367_, v_ks_2426_, v_vs_2427_, v___x_2428_, v___x_2429_);
                    lean_dec_ref(v_vs_2427_);
                    lean_dec_ref(v_ks_2426_);
                    return v___x_2430_;
                } else {
                    return v_newNode_2423_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(
    mut v_depth_2438_: usize,
    mut v_keys_2439_: *mut LeanObject,
    mut v_vals_2440_: *mut LeanObject,
    mut v_i_2441_: *mut LeanObject,
    mut v_entries_2442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v_k_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u64 = 0;
    let mut v_h_2448_: usize = 0;
    let mut v___x_2449_: usize = 0;
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: usize = 0;
    let mut v___x_2453_: usize = 0;
    let mut v_h_2454_: usize = 0;
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2443_ = lean_array_get_size(v_keys_2439_);
                v___x_2444_ = lean_nat_dec_lt(v_i_2441_, v___x_2443_);
                if v___x_2444_ == 0 {
                    lean_dec(v_i_2441_);
                    return v_entries_2442_;
                } else {
                    v_k_2445_ = lean_array_fget_borrowed(v_keys_2439_, v_i_2441_);
                    v_v_2446_ = lean_array_fget_borrowed(v_vals_2440_, v_i_2441_);
                    v___x_2447_ = l_Lean_instHashableExtraModUse_hash(v_k_2445_);
                    v_h_2448_ = lean_uint64_to_usize(v___x_2447_);
                    v___x_2449_ = 5usize;
                    v___x_2450_ = lean_unsigned_to_nat(1);
                    v___x_2451_ = 1usize;
                    v___x_2452_ = lean_usize_sub(v_depth_2438_, v___x_2451_);
                    v___x_2453_ = lean_usize_mul(v___x_2449_, v___x_2452_);
                    v_h_2454_ = lean_usize_shift_right(v_h_2448_, v___x_2453_);
                    v___x_2455_ = lean_nat_add(v_i_2441_, v___x_2450_);
                    lean_dec(v_i_2441_);
                    lean_inc(v_v_2446_);
                    lean_inc(v_k_2445_);
                    v___x_2456_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_2442_, v_h_2454_, v_depth_2438_, v_k_2445_, v_v_2446_);
                    v_i_2441_ = v___x_2455_;
                    v_entries_2442_ = v___x_2456_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(
    mut v_depth_2458_: *mut LeanObject,
    mut v_keys_2459_: *mut LeanObject,
    mut v_vals_2460_: *mut LeanObject,
    mut v_i_2461_: *mut LeanObject,
    mut v_entries_2462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2463_: usize = 0;
    let mut v_res_2464_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2463_ = lean_unbox_usize(v_depth_2458_);
    lean_dec(v_depth_2458_);
    v_res_2464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_2463_, v_keys_2459_, v_vals_2460_, v_i_2461_, v_entries_2462_);
    lean_dec_ref(v_vals_2460_);
    lean_dec_ref(v_keys_2459_);
    return v_res_2464_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(
    mut v_x_2465_: *mut LeanObject,
    mut v_x_2466_: *mut LeanObject,
    mut v_x_2467_: *mut LeanObject,
    mut v_x_2468_: *mut LeanObject,
    mut v_x_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_585__boxed_2470_: usize = 0;
    let mut v_x_586__boxed_2471_: usize = 0;
    let mut v_res_2472_: *mut LeanObject = core::ptr::null_mut();
    v_x_585__boxed_2470_ = lean_unbox_usize(v_x_2466_);
    lean_dec(v_x_2466_);
    v_x_586__boxed_2471_ = lean_unbox_usize(v_x_2467_);
    lean_dec(v_x_2467_);
    v_res_2472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_2465_, v_x_585__boxed_2470_, v_x_586__boxed_2471_, v_x_2468_, v_x_2469_);
    return v_res_2472_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(
    mut v_x_2473_: *mut LeanObject,
    mut v_x_2474_: *mut LeanObject,
    mut v_x_2475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2476_: u64 = 0;
    let mut v___x_2477_: usize = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Lean_instHashableExtraModUse_hash(v_x_2474_);
    v___x_2477_ = lean_uint64_to_usize(v___x_2476_);
    v___x_2478_ = 1usize;
    v___x_2479_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_2473_, v___x_2477_, v___x_2478_, v_x_2474_, v_x_2475_);
    return v___x_2479_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(
    mut v_m_2480_: *mut LeanObject,
    mut v_k_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2482_ = lean_box(0);
    v___x_2483_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_2480_, v_k_2481_, v___x_2482_);
    return v___x_2483_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(
    mut v_keys_2484_: *mut LeanObject,
    mut v_i_2485_: *mut LeanObject,
    mut v_k_2486_: *mut LeanObject,
) -> u8 {
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v_k_x27_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2487_ = lean_array_get_size(v_keys_2484_);
                v___x_2488_ = lean_nat_dec_lt(v_i_2485_, v___x_2487_);
                if v___x_2488_ == 0 {
                    lean_dec(v_i_2485_);
                    return v___x_2488_;
                } else {
                    v_k_x27_2489_ = lean_array_fget_borrowed(v_keys_2484_, v_i_2485_);
                    v___x_2490_ = l_Lean_instBEqExtraModUse_beq(v_k_2486_, v_k_x27_2489_);
                    if v___x_2490_ == 0 {
                        v___x_2491_ = lean_unsigned_to_nat(1);
                        v___x_2492_ = lean_nat_add(v_i_2485_, v___x_2491_);
                        lean_dec(v_i_2485_);
                        v_i_2485_ = v___x_2492_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_2485_);
                        return v___x_2490_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(
    mut v_keys_2494_: *mut LeanObject,
    mut v_i_2495_: *mut LeanObject,
    mut v_k_2496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2497_: u8 = 0;
    let mut v_r_2498_: *mut LeanObject = core::ptr::null_mut();
    v_res_2497_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_2494_, v_i_2495_, v_k_2496_);
    lean_dec_ref(v_k_2496_);
    lean_dec_ref(v_keys_2494_);
    v_r_2498_ = lean_box((v_res_2497_) as usize);
    return v_r_2498_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_2499_: *mut LeanObject,
    mut v_x_2500_: usize,
    mut v_x_2501_: *mut LeanObject,
) -> u8 {
    let mut v_es_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: usize = 0;
    let mut v___x_2505_: usize = 0;
    let mut v___x_2506_: usize = 0;
    let mut v_j_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v_node_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: usize = 0;
    let mut v___x_2514_: u8 = 0;
    let mut v_ks_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2499_) == 0 {
                    v_es_2502_ = lean_ctor_get(v_x_2499_, 0);
                    v___x_2503_ = lean_box(2);
                    v___x_2504_ = 5usize;
                    v___x_2505_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__1);
                    v___x_2506_ = lean_usize_land(v_x_2500_, v___x_2505_);
                    v_j_2507_ = lean_usize_to_nat(v___x_2506_);
                    v___x_2508_ = lean_array_get_borrowed(v___x_2503_, v_es_2502_, v_j_2507_);
                    lean_dec(v_j_2507_);
                    match lean_obj_tag(v___x_2508_) {
                        0 => {
                            v_key_2509_ = lean_ctor_get(v___x_2508_, 0);
                            v___x_2510_ = l_Lean_instBEqExtraModUse_beq(v_x_2501_, v_key_2509_);
                            return v___x_2510_;
                        }
                        1 => {
                            v_node_2511_ = lean_ctor_get(v___x_2508_, 0);
                            v___x_2512_ = lean_usize_shift_right(v_x_2500_, v___x_2504_);
                            v_x_2499_ = v_node_2511_;
                            v_x_2500_ = v___x_2512_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2514_ = 0;
                            return v___x_2514_;
                        }
                    }
                } else {
                    v_ks_2515_ = lean_ctor_get(v_x_2499_, 0);
                    v___x_2516_ = lean_unsigned_to_nat(0);
                    v___x_2517_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_2515_, v___x_2516_, v_x_2501_);
                    return v___x_2517_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_x_2518_: *mut LeanObject,
    mut v_x_2519_: *mut LeanObject,
    mut v_x_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_783__boxed_2521_: usize = 0;
    let mut v_res_2522_: u8 = 0;
    let mut v_r_2523_: *mut LeanObject = core::ptr::null_mut();
    v_x_783__boxed_2521_ = lean_unbox_usize(v_x_2519_);
    lean_dec(v_x_2519_);
    v_res_2522_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2518_, v_x_783__boxed_2521_, v_x_2520_);
    lean_dec_ref(v_x_2520_);
    lean_dec_ref(v_x_2518_);
    v_r_2523_ = lean_box((v_res_2522_) as usize);
    return v_r_2523_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_2524_: *mut LeanObject,
    mut v_x_2525_: *mut LeanObject,
) -> u8 {
    let mut v___x_2526_: u64 = 0;
    let mut v___x_2527_: usize = 0;
    let mut v___x_2528_: u8 = 0;
    v___x_2526_ = l_Lean_instHashableExtraModUse_hash(v_x_2525_);
    v___x_2527_ = lean_uint64_to_usize(v___x_2526_);
    v___x_2528_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2524_, v___x_2527_, v_x_2525_);
    return v___x_2528_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_x_2529_: *mut LeanObject,
    mut v_x_2530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2531_: u8 = 0;
    let mut v_r_2532_: *mut LeanObject = core::ptr::null_mut();
    v_res_2531_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_2529_, v_x_2530_);
    lean_dec_ref(v_x_2530_);
    lean_dec_ref(v_x_2529_);
    v_r_2532_ = lean_box((v_res_2531_) as usize);
    return v_r_2532_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    v___x_2574_ = l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_;
    v___x_2575_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2574_);
    return v___x_2575_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(
    mut v_a_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2577_: *mut LeanObject = core::ptr::null_mut();
    v_res_2577_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
    return v_res_2577_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_2578_: *mut LeanObject,
    mut v_x_2579_: *mut LeanObject,
    mut v_x_2580_: *mut LeanObject,
) -> u8 {
    let mut v___x_2581_: u8 = 0;
    v___x_2581_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_2579_, v_x_2580_);
    return v___x_2581_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b2_2582_: *mut LeanObject,
    mut v_x_2583_: *mut LeanObject,
    mut v_x_2584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2585_: u8 = 0;
    let mut v_r_2586_: *mut LeanObject = core::ptr::null_mut();
    v_res_2585_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_2582_, v_x_2583_, v_x_2584_);
    lean_dec_ref(v_x_2584_);
    lean_dec_ref(v_x_2583_);
    v_r_2586_ = lean_box((v_res_2585_) as usize);
    return v_r_2586_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(
    mut v_00_u03b2_2587_: *mut LeanObject,
    mut v_x_2588_: *mut LeanObject,
    mut v_x_2589_: *mut LeanObject,
    mut v_x_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    v___x_2591_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_2588_, v_x_2589_, v_x_2590_);
    return v___x_2591_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_2592_: *mut LeanObject,
    mut v_x_2593_: *mut LeanObject,
    mut v_x_2594_: usize,
    mut v_x_2595_: *mut LeanObject,
) -> u8 {
    let mut v___x_2596_: u8 = 0;
    v___x_2596_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2593_, v_x_2594_, v_x_2595_);
    return v___x_2596_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_2597_: *mut LeanObject,
    mut v_x_2598_: *mut LeanObject,
    mut v_x_2599_: *mut LeanObject,
    mut v_x_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_983__boxed_2601_: usize = 0;
    let mut v_res_2602_: u8 = 0;
    let mut v_r_2603_: *mut LeanObject = core::ptr::null_mut();
    v_x_983__boxed_2601_ = lean_unbox_usize(v_x_2599_);
    lean_dec(v_x_2599_);
    v_res_2602_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2597_, v_x_2598_, v_x_983__boxed_2601_, v_x_2600_);
    lean_dec_ref(v_x_2600_);
    lean_dec_ref(v_x_2598_);
    v_r_2603_ = lean_box((v_res_2602_) as usize);
    return v_r_2603_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(
    mut v_00_u03b2_2604_: *mut LeanObject,
    mut v_x_2605_: *mut LeanObject,
    mut v_x_2606_: usize,
    mut v_x_2607_: usize,
    mut v_x_2608_: *mut LeanObject,
    mut v_x_2609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    v___x_2610_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_2605_, v_x_2606_, v_x_2607_, v_x_2608_, v_x_2609_);
    return v___x_2610_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_00_u03b2_2611_: *mut LeanObject,
    mut v_x_2612_: *mut LeanObject,
    mut v_x_2613_: *mut LeanObject,
    mut v_x_2614_: *mut LeanObject,
    mut v_x_2615_: *mut LeanObject,
    mut v_x_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_994__boxed_2617_: usize = 0;
    let mut v_x_995__boxed_2618_: usize = 0;
    let mut v_res_2619_: *mut LeanObject = core::ptr::null_mut();
    v_x_994__boxed_2617_ = lean_unbox_usize(v_x_2613_);
    lean_dec(v_x_2613_);
    v_x_995__boxed_2618_ = lean_unbox_usize(v_x_2614_);
    lean_dec(v_x_2614_);
    v_res_2619_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_2611_, v_x_2612_, v_x_994__boxed_2617_, v_x_995__boxed_2618_, v_x_2615_, v_x_2616_);
    return v_res_2619_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(
    mut v_00_u03b2_2620_: *mut LeanObject,
    mut v_keys_2621_: *mut LeanObject,
    mut v_vals_2622_: *mut LeanObject,
    mut v_heq_2623_: *mut LeanObject,
    mut v_i_2624_: *mut LeanObject,
    mut v_k_2625_: *mut LeanObject,
) -> u8 {
    let mut v___x_2626_: u8 = 0;
    v___x_2626_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_2621_, v_i_2624_, v_k_2625_);
    return v___x_2626_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2627_: *mut LeanObject,
    mut v_keys_2628_: *mut LeanObject,
    mut v_vals_2629_: *mut LeanObject,
    mut v_heq_2630_: *mut LeanObject,
    mut v_i_2631_: *mut LeanObject,
    mut v_k_2632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2633_: u8 = 0;
    let mut v_r_2634_: *mut LeanObject = core::ptr::null_mut();
    v_res_2633_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_2627_, v_keys_2628_, v_vals_2629_, v_heq_2630_, v_i_2631_, v_k_2632_);
    lean_dec_ref(v_k_2632_);
    lean_dec_ref(v_vals_2629_);
    lean_dec_ref(v_keys_2628_);
    v_r_2634_ = lean_box((v_res_2633_) as usize);
    return v_r_2634_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(
    mut v_00_u03b2_2635_: *mut LeanObject,
    mut v_n_2636_: *mut LeanObject,
    mut v_k_2637_: *mut LeanObject,
    mut v_v_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_2636_, v_k_2637_, v_v_2638_);
    return v___x_2639_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(
    mut v_00_u03b2_2640_: *mut LeanObject,
    mut v_depth_2641_: usize,
    mut v_keys_2642_: *mut LeanObject,
    mut v_vals_2643_: *mut LeanObject,
    mut v_heq_2644_: *mut LeanObject,
    mut v_i_2645_: *mut LeanObject,
    mut v_entries_2646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    v___x_2647_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_2641_, v_keys_2642_, v_vals_2643_, v_i_2645_, v_entries_2646_);
    return v___x_2647_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b2_2648_: *mut LeanObject,
    mut v_depth_2649_: *mut LeanObject,
    mut v_keys_2650_: *mut LeanObject,
    mut v_vals_2651_: *mut LeanObject,
    mut v_heq_2652_: *mut LeanObject,
    mut v_i_2653_: *mut LeanObject,
    mut v_entries_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2655_: usize = 0;
    let mut v_res_2656_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2655_ = lean_unbox_usize(v_depth_2649_);
    lean_dec(v_depth_2649_);
    v_res_2656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_2648_, v_depth_boxed_2655_, v_keys_2650_, v_vals_2651_, v_heq_2652_, v_i_2653_, v_entries_2654_);
    lean_dec_ref(v_vals_2651_);
    lean_dec_ref(v_keys_2650_);
    return v_res_2656_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(
    mut v_00_u03b2_2657_: *mut LeanObject,
    mut v_x_2658_: *mut LeanObject,
    mut v_x_2659_: *mut LeanObject,
    mut v_x_2660_: *mut LeanObject,
    mut v_x_2661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    v___x_2662_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_2658_, v_x_2659_, v_x_2660_, v_x_2661_);
    return v___x_2662_;
}
pub unsafe fn _init_l_Lean_getExtraModUses___closed__0() -> *mut LeanObject {
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    v___x_2663_ = l_Lean_instHashableExtraModUse___closed__0;
    v___x_2664_ = l_Lean_instBEqExtraModUse___closed__0;
    v___x_2665_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2664_, v___x_2663_);
    return v___x_2665_;
}
pub unsafe fn _init_l_Lean_getExtraModUses___closed__1() -> *mut LeanObject {
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    v___x_2666_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__0),
        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__0_once),
        _init_l_Lean_getExtraModUses___closed__0,
    );
    v___x_2667_ = lean_box(0);
    v___x_2668_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2668_, 0, v___x_2667_);
    lean_ctor_set(v___x_2668_, 1, v___x_2666_);
    return v___x_2668_;
}
pub unsafe fn l_Lean_getExtraModUses(
    mut v_env_2669_: *mut LeanObject,
    mut v_modIdx_2670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    v___x_2671_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__1),
        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__1_once),
        _init_l_Lean_getExtraModUses___closed__1,
    );
    v___x_2672_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
    v___x_2673_ = 0;
    v___x_2674_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
        v___x_2671_,
        v___x_2672_,
        v_env_2669_,
        v_modIdx_2670_,
        v___x_2673_,
    );
    return v___x_2674_;
}
pub unsafe fn l_Lean_getExtraModUses___boxed(
    mut v_env_2675_: *mut LeanObject,
    mut v_modIdx_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2677_: *mut LeanObject = core::ptr::null_mut();
    v_res_2677_ = l_Lean_getExtraModUses(v_env_2675_, v_modIdx_2676_);
    lean_dec(v_modIdx_2676_);
    lean_dec_ref(v_env_2675_);
    return v_res_2677_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(
    mut v_as_x27_2678_: *mut LeanObject,
    mut v_b_2679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v_toEnvExtension_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2678_) == 0 {
                    return v_b_2679_;
                } else {
                    v_head_2680_ = lean_ctor_get(v_as_x27_2678_, 0);
                    v_tail_2681_ = lean_ctor_get(v_as_x27_2678_, 1);
                    v___x_2682_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__0_once),
                        _init_l_Lean_getExtraModUses___closed__0,
                    );
                    v___x_2683_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                    v___x_2684_ = lean_box(1);
                    v___x_2685_ = lean_box(0);
                    lean_inc_ref(v_b_2679_);
                    v___x_2686_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_2682_,
                        v___x_2683_,
                        v_b_2679_,
                        v___x_2684_,
                        v___x_2685_,
                    );
                    v___x_2687_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_2686_, v_head_2680_);
                    lean_dec(v___x_2686_);
                    if v___x_2687_ == 0 {
                        v_toEnvExtension_2688_ = lean_ctor_get(v___x_2683_, 0);
                        v_asyncMode_2689_ = lean_ctor_get(v_toEnvExtension_2688_, 2);
                        lean_inc(v_head_2680_);
                        v___x_2690_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                            v___x_2683_,
                            v_b_2679_,
                            v_head_2680_,
                            v_asyncMode_2689_,
                            v___x_2685_,
                        );
                        v_as_x27_2678_ = v_tail_2681_;
                        v_b_2679_ = v___x_2690_;
                        state = 0;
                        continue;
                    } else {
                        v_as_x27_2678_ = v_tail_2681_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(
    mut v_as_x27_2693_: *mut LeanObject,
    mut v_b_2694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2695_: *mut LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(
        v_as_x27_2693_,
        v_b_2694_,
    );
    lean_dec(v_as_x27_2693_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_copyExtraModUses(
    mut v_src_2696_: *mut LeanObject,
    mut v_dest_2697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    v___x_2698_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__0),
        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__0_once),
        _init_l_Lean_getExtraModUses___closed__0,
    );
    v___x_2699_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
    v___x_2700_ = lean_box(1);
    v___x_2701_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
        v___x_2698_,
        v___x_2699_,
        v_src_2696_,
        v___x_2700_,
    );
    v___x_2702_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(
        v___x_2701_,
        v_dest_2697_,
    );
    lean_dec(v___x_2701_);
    return v___x_2702_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(
    mut v_as_2703_: *mut LeanObject,
    mut v_as_x27_2704_: *mut LeanObject,
    mut v_b_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    v___x_2707_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(
        v_as_x27_2704_,
        v_b_2705_,
    );
    return v___x_2707_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(
    mut v_as_2708_: *mut LeanObject,
    mut v_as_x27_2709_: *mut LeanObject,
    mut v_b_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2712_: *mut LeanObject = core::ptr::null_mut();
    v_res_2712_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(
        v_as_2708_,
        v_as_x27_2709_,
        v_b_2710_,
        v_a_2711_,
    );
    lean_dec(v_as_x27_2709_);
    lean_dec(v_as_2708_);
    return v_res_2712_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(
    mut v___x_2713_: *mut LeanObject,
    mut v_entry_2714_: *mut LeanObject,
    mut v___x_2715_: *mut LeanObject,
    mut v_x_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toEnvExtension_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    v_toEnvExtension_2717_ = lean_ctor_get(v___x_2713_, 0);
    v_asyncMode_2718_ = lean_ctor_get(v_toEnvExtension_2717_, 2);
    lean_inc(v_asyncMode_2718_);
    v___x_2719_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_2713_,
        v_x_2716_,
        v_entry_2714_,
        v_asyncMode_2718_,
        v___x_2715_,
    );
    lean_dec(v_asyncMode_2718_);
    return v___x_2719_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    v___x_2721_ =
        l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__0;
    v___x_2722_ = l_Lean_stringToMessageData(v___x_2721_);
    return v___x_2722_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3()
-> *mut LeanObject {
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    v___x_2724_ =
        l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__2;
    v___x_2725_ = l_Lean_stringToMessageData(v___x_2724_);
    return v___x_2725_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5()
-> *mut LeanObject {
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    v___x_2727_ =
        l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__4;
    v___x_2728_ = l_Lean_stringToMessageData(v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7()
-> *mut LeanObject {
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    v___x_2730_ =
        l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__6;
    v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
    return v___x_2731_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9()
-> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ =
        l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__8;
    v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
    return v___x_2734_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(
    mut v_modifyEnv_2739_: *mut LeanObject,
    mut v___f_2740_: *mut LeanObject,
    mut v_inst_2741_: *mut LeanObject,
    mut v_inst_2742_: *mut LeanObject,
    mut v_inst_2743_: *mut LeanObject,
    mut v_inst_2744_: *mut LeanObject,
    mut v_cls_2745_: *mut LeanObject,
    mut v_toBind_2746_: *mut LeanObject,
    mut v___f_2747_: *mut LeanObject,
    mut v_mod_2748_: *mut LeanObject,
    mut v_hint_2749_: *mut LeanObject,
    mut v_isMeta_2750_: u8,
    mut v_isExporting_2751_: u8,
    mut v_____do__lift_2752_: u8,
) -> *mut LeanObject {
    let mut v___y_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_2752_ == 0 {
                    lean_dec(v_hint_2749_);
                    lean_dec(v_mod_2748_);
                    lean_dec(v___f_2747_);
                    lean_dec(v_toBind_2746_);
                    lean_dec(v_cls_2745_);
                    lean_dec(v_inst_2744_);
                    lean_dec_ref(v_inst_2743_);
                    lean_dec_ref(v_inst_2742_);
                    lean_dec_ref(v_inst_2741_);
                    v___x_2773_ = lean_apply_1(v_modifyEnv_2739_, v___f_2740_);
                    return v___x_2773_;
                } else {
                    lean_dec_ref(v___f_2740_);
                    lean_dec(v_modifyEnv_2739_);
                    v___x_2774_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__7);
                    if v_isExporting_2751_ == 0 {
                        v___x_2783_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__12;
                        v___y_2776_ = v___x_2783_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2784_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__13;
                        v___y_2776_ = v___x_2784_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2756_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2756_, 0, v___y_2754_);
                lean_ctor_set(v___x_2756_, 1, v___y_2755_);
                v___x_2757_ = l_Lean_addTrace___redArg(
                    v_inst_2741_,
                    v_inst_2742_,
                    v_inst_2743_,
                    v_inst_2744_,
                    v_cls_2745_,
                    v___x_2756_,
                );
                v___x_2758_ = lean_apply_4(
                    v_toBind_2746_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2757_,
                    v___f_2747_,
                );
                return v___x_2758_;
            }
            2 => {
                lean_inc_ref(v___y_2761_);
                v___x_2762_ = l_Lean_stringToMessageData(v___y_2761_);
                v___x_2763_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2763_, 0, v___y_2760_);
                lean_ctor_set(v___x_2763_, 1, v___x_2762_);
                v___x_2764_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__1);
                v___x_2765_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2765_, 0, v___x_2763_);
                lean_ctor_set(v___x_2765_, 1, v___x_2764_);
                v___x_2766_ = l_Lean_MessageData_ofName(v_mod_2748_);
                v___x_2767_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2767_, 0, v___x_2765_);
                lean_ctor_set(v___x_2767_, 1, v___x_2766_);
                v___x_2768_ = l_Lean_Name_isAnonymous(v_hint_2749_);
                if v___x_2768_ == 0 {
                    v___x_2769_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__3);
                    v___x_2770_ = l_Lean_MessageData_ofName(v_hint_2749_);
                    v___x_2771_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2771_, 0, v___x_2769_);
                    lean_ctor_set(v___x_2771_, 1, v___x_2770_);
                    v___y_2754_ = v___x_2767_;
                    v___y_2755_ = v___x_2771_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_hint_2749_);
                    v___x_2772_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__5);
                    v___y_2754_ = v___x_2767_;
                    v___y_2755_ = v___x_2772_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___y_2776_);
                v___x_2777_ = l_Lean_stringToMessageData(v___y_2776_);
                v___x_2778_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2778_, 0, v___x_2774_);
                lean_ctor_set(v___x_2778_, 1, v___x_2777_);
                v___x_2779_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__9);
                v___x_2780_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2780_, 0, v___x_2778_);
                lean_ctor_set(v___x_2780_, 1, v___x_2779_);
                if v_isMeta_2750_ == 0 {
                    v___x_2781_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__10;
                    v___y_2760_ = v___x_2780_;
                    v___y_2761_ = v___x_2781_;
                    state = 2;
                    continue;
                } else {
                    v___x_2782_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___closed__11;
                    v___y_2760_ = v___x_2780_;
                    v___y_2761_ = v___x_2782_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(
    mut v_modifyEnv_2785_: *mut LeanObject,
    mut v___f_2786_: *mut LeanObject,
    mut v_inst_2787_: *mut LeanObject,
    mut v_inst_2788_: *mut LeanObject,
    mut v_inst_2789_: *mut LeanObject,
    mut v_inst_2790_: *mut LeanObject,
    mut v_cls_2791_: *mut LeanObject,
    mut v_toBind_2792_: *mut LeanObject,
    mut v___f_2793_: *mut LeanObject,
    mut v_mod_2794_: *mut LeanObject,
    mut v_hint_2795_: *mut LeanObject,
    mut v_isMeta_2796_: *mut LeanObject,
    mut v_isExporting_2797_: *mut LeanObject,
    mut v_____do__lift_2798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_2799_: u8 = 0;
    let mut v_isExporting_boxed_2800_: u8 = 0;
    let mut v_____do__lift_963__boxed_2801_: u8 = 0;
    let mut v_res_2802_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2799_ = (lean_unbox(v_isMeta_2796_) as u8);
    v_isExporting_boxed_2800_ = (lean_unbox(v_isExporting_2797_) as u8);
    v_____do__lift_963__boxed_2801_ = (lean_unbox(v_____do__lift_2798_) as u8);
    v_res_2802_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(
        v_modifyEnv_2785_,
        v___f_2786_,
        v_inst_2787_,
        v_inst_2788_,
        v_inst_2789_,
        v_inst_2790_,
        v_cls_2791_,
        v_toBind_2792_,
        v___f_2793_,
        v_mod_2794_,
        v_hint_2795_,
        v_isMeta_boxed_2799_,
        v_isExporting_boxed_2800_,
        v_____do__lift_963__boxed_2801_,
    );
    return v_res_2802_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(
    mut v___x_2803_: *mut LeanObject,
    mut v___x_2804_: *mut LeanObject,
    mut v___x_2805_: *mut LeanObject,
    mut v_entry_2806_: *mut LeanObject,
    mut v_inst_2807_: *mut LeanObject,
    mut v_toApplicative_2808_: *mut LeanObject,
    mut v_modifyEnv_2809_: *mut LeanObject,
    mut v_inst_2810_: *mut LeanObject,
    mut v_inst_2811_: *mut LeanObject,
    mut v_inst_2812_: *mut LeanObject,
    mut v_toBind_2813_: *mut LeanObject,
    mut v_mod_2814_: *mut LeanObject,
    mut v_hint_2815_: *mut LeanObject,
    mut v_isMeta_2816_: u8,
    mut v_isExporting_2817_: u8,
    mut v_inst_2818_: *mut LeanObject,
    mut v_____do__lift_2819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    v___x_2820_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
    v___x_2821_ = lean_box(1);
    v___x_2822_ = lean_box(0);
    v___x_2823_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2803_,
        v___x_2820_,
        v_____do__lift_2819_,
        v___x_2821_,
        v___x_2822_,
    );
    lean_inc_ref(v_entry_2806_);
    v___x_2824_ = l_Lean_PersistentHashMap_contains___redArg(
        v___x_2804_,
        v___x_2805_,
        v___x_2823_,
        v_entry_2806_,
    );
    if v___x_2824_ == 0 {
        let mut v_getInheritedTraceOptions_2825_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2826_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2827_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2828_: *mut LeanObject = core::ptr::null_mut();
        let mut v_cls_2829_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_2825_ = lean_ctor_get(v_inst_2807_, 2);
        lean_inc(v_getInheritedTraceOptions_2825_);
        v_toPure_2826_ = lean_ctor_get(v_toApplicative_2808_, 1);
        lean_inc(v_toPure_2826_);
        lean_dec_ref(v_toApplicative_2808_);
        v___f_2827_ = lean_alloc_closure(
            l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_2827_, 0, v___x_2820_);
        lean_closure_set(v___f_2827_, 1, v_entry_2806_);
        lean_closure_set(v___f_2827_, 2, v___x_2822_);
        lean_inc_ref(v___f_2827_);
        lean_inc(v_modifyEnv_2809_);
        v___f_2828_ = lean_alloc_closure(
            l_Lean_recordIndirectModUse___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_2828_, 0, v_modifyEnv_2809_);
        lean_closure_set(v___f_2828_, 1, v___f_2827_);
        v_cls_2829_ = l_Lean_recordIndirectModUse___redArg___lam__5___closed__1;
        v___x_2830_ = lean_box((v_isMeta_2816_) as usize);
        v___x_2831_ = lean_box((v_isExporting_2817_) as usize);
        lean_inc_n(v_toBind_2813_, 3);
        v___f_2832_ = lean_alloc_closure(
            l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed
                as *mut core::ffi::c_void,
            14,
            13,
        );
        lean_closure_set(v___f_2832_, 0, v_modifyEnv_2809_);
        lean_closure_set(v___f_2832_, 1, v___f_2827_);
        lean_closure_set(v___f_2832_, 2, v_inst_2810_);
        lean_closure_set(v___f_2832_, 3, v_inst_2807_);
        lean_closure_set(v___f_2832_, 4, v_inst_2811_);
        lean_closure_set(v___f_2832_, 5, v_inst_2812_);
        lean_closure_set(v___f_2832_, 6, v_cls_2829_);
        lean_closure_set(v___f_2832_, 7, v_toBind_2813_);
        lean_closure_set(v___f_2832_, 8, v___f_2828_);
        lean_closure_set(v___f_2832_, 9, v_mod_2814_);
        lean_closure_set(v___f_2832_, 10, v_hint_2815_);
        lean_closure_set(v___f_2832_, 11, v___x_2830_);
        lean_closure_set(v___f_2832_, 12, v___x_2831_);
        v___f_2833_ = lean_alloc_closure(
            l_Lean_recordIndirectModUse___redArg___lam__4 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_2833_, 0, v_toPure_2826_);
        lean_closure_set(v___f_2833_, 1, v_cls_2829_);
        lean_closure_set(v___f_2833_, 2, v_toBind_2813_);
        lean_closure_set(v___f_2833_, 3, v_inst_2818_);
        v___x_2834_ = lean_apply_4(
            v_toBind_2813_,
            lean_box(0),
            lean_box(0),
            v_getInheritedTraceOptions_2825_,
            v___f_2833_,
        );
        v___x_2835_ = lean_apply_4(
            v_toBind_2813_,
            lean_box(0),
            lean_box(0),
            v___x_2834_,
            v___f_2832_,
        );
        return v___x_2835_;
    } else {
        let mut v_toPure_2836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_2818_);
        lean_dec(v_hint_2815_);
        lean_dec(v_mod_2814_);
        lean_dec(v_toBind_2813_);
        lean_dec(v_inst_2812_);
        lean_dec_ref(v_inst_2811_);
        lean_dec_ref(v_inst_2810_);
        lean_dec(v_modifyEnv_2809_);
        lean_dec_ref(v_inst_2807_);
        lean_dec_ref(v_entry_2806_);
        v_toPure_2836_ = lean_ctor_get(v_toApplicative_2808_, 1);
        lean_inc(v_toPure_2836_);
        lean_dec_ref(v_toApplicative_2808_);
        v___x_2837_ = lean_box(0);
        v___x_2838_ = lean_apply_2(v_toPure_2836_, lean_box(0), v___x_2837_);
        return v___x_2838_;
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2839_: *mut LeanObject = *_args.add(0);
    let mut v___x_2840_: *mut LeanObject = *_args.add(1);
    let mut v___x_2841_: *mut LeanObject = *_args.add(2);
    let mut v_entry_2842_: *mut LeanObject = *_args.add(3);
    let mut v_inst_2843_: *mut LeanObject = *_args.add(4);
    let mut v_toApplicative_2844_: *mut LeanObject = *_args.add(5);
    let mut v_modifyEnv_2845_: *mut LeanObject = *_args.add(6);
    let mut v_inst_2846_: *mut LeanObject = *_args.add(7);
    let mut v_inst_2847_: *mut LeanObject = *_args.add(8);
    let mut v_inst_2848_: *mut LeanObject = *_args.add(9);
    let mut v_toBind_2849_: *mut LeanObject = *_args.add(10);
    let mut v_mod_2850_: *mut LeanObject = *_args.add(11);
    let mut v_hint_2851_: *mut LeanObject = *_args.add(12);
    let mut v_isMeta_2852_: *mut LeanObject = *_args.add(13);
    let mut v_isExporting_2853_: *mut LeanObject = *_args.add(14);
    let mut v_inst_2854_: *mut LeanObject = *_args.add(15);
    let mut v_____do__lift_2855_: *mut LeanObject = *_args.add(16);
    let mut v_isMeta_boxed_2856_: u8 = 0;
    let mut v_isExporting_boxed_2857_: u8 = 0;
    let mut v_res_2858_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2856_ = (lean_unbox(v_isMeta_2852_) as u8);
    v_isExporting_boxed_2857_ = (lean_unbox(v_isExporting_2853_) as u8);
    v_res_2858_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(
        v___x_2839_,
        v___x_2840_,
        v___x_2841_,
        v_entry_2842_,
        v_inst_2843_,
        v_toApplicative_2844_,
        v_modifyEnv_2845_,
        v_inst_2846_,
        v_inst_2847_,
        v_inst_2848_,
        v_toBind_2849_,
        v_mod_2850_,
        v_hint_2851_,
        v_isMeta_boxed_2856_,
        v_isExporting_boxed_2857_,
        v_inst_2854_,
        v_____do__lift_2855_,
    );
    return v_res_2858_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(
    mut v_mod_2859_: *mut LeanObject,
    mut v_isMeta_2860_: u8,
    mut v___x_2861_: *mut LeanObject,
    mut v___x_2862_: *mut LeanObject,
    mut v___x_2863_: *mut LeanObject,
    mut v_inst_2864_: *mut LeanObject,
    mut v_toApplicative_2865_: *mut LeanObject,
    mut v_modifyEnv_2866_: *mut LeanObject,
    mut v_inst_2867_: *mut LeanObject,
    mut v_inst_2868_: *mut LeanObject,
    mut v_inst_2869_: *mut LeanObject,
    mut v_toBind_2870_: *mut LeanObject,
    mut v_hint_2871_: *mut LeanObject,
    mut v_inst_2872_: *mut LeanObject,
    mut v_getEnv_2873_: *mut LeanObject,
    mut v_____do__lift_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_2875_: u8 = 0;
    let mut v_entry_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_2875_ = lean_ctor_get_uint8(
        v_____do__lift_2874_,
        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
    );
    lean_inc(v_mod_2859_);
    v_entry_2876_ = lean_alloc_ctor(0, 1, (2) as u32);
    lean_ctor_set(v_entry_2876_, 0, v_mod_2859_);
    lean_ctor_set_uint8(
        v_entry_2876_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_isExporting_2875_,
    );
    lean_ctor_set_uint8(
        v_entry_2876_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
        v_isMeta_2860_,
    );
    v___x_2877_ = lean_box((v_isMeta_2860_) as usize);
    v___x_2878_ = lean_box((v_isExporting_2875_) as usize);
    lean_inc(v_toBind_2870_);
    v___f_2879_ = lean_alloc_closure(
        l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        17,
        16,
    );
    lean_closure_set(v___f_2879_, 0, v___x_2861_);
    lean_closure_set(v___f_2879_, 1, v___x_2862_);
    lean_closure_set(v___f_2879_, 2, v___x_2863_);
    lean_closure_set(v___f_2879_, 3, v_entry_2876_);
    lean_closure_set(v___f_2879_, 4, v_inst_2864_);
    lean_closure_set(v___f_2879_, 5, v_toApplicative_2865_);
    lean_closure_set(v___f_2879_, 6, v_modifyEnv_2866_);
    lean_closure_set(v___f_2879_, 7, v_inst_2867_);
    lean_closure_set(v___f_2879_, 8, v_inst_2868_);
    lean_closure_set(v___f_2879_, 9, v_inst_2869_);
    lean_closure_set(v___f_2879_, 10, v_toBind_2870_);
    lean_closure_set(v___f_2879_, 11, v_mod_2859_);
    lean_closure_set(v___f_2879_, 12, v_hint_2871_);
    lean_closure_set(v___f_2879_, 13, v___x_2877_);
    lean_closure_set(v___f_2879_, 14, v___x_2878_);
    lean_closure_set(v___f_2879_, 15, v_inst_2872_);
    v___x_2880_ = lean_apply_4(
        v_toBind_2870_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2873_,
        v___f_2879_,
    );
    return v___x_2880_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(
    mut v_mod_2881_: *mut LeanObject,
    mut v_isMeta_2882_: *mut LeanObject,
    mut v___x_2883_: *mut LeanObject,
    mut v___x_2884_: *mut LeanObject,
    mut v___x_2885_: *mut LeanObject,
    mut v_inst_2886_: *mut LeanObject,
    mut v_toApplicative_2887_: *mut LeanObject,
    mut v_modifyEnv_2888_: *mut LeanObject,
    mut v_inst_2889_: *mut LeanObject,
    mut v_inst_2890_: *mut LeanObject,
    mut v_inst_2891_: *mut LeanObject,
    mut v_toBind_2892_: *mut LeanObject,
    mut v_hint_2893_: *mut LeanObject,
    mut v_inst_2894_: *mut LeanObject,
    mut v_getEnv_2895_: *mut LeanObject,
    mut v_____do__lift_2896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_2897_: u8 = 0;
    let mut v_res_2898_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2897_ = (lean_unbox(v_isMeta_2882_) as u8);
    v_res_2898_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(
        v_mod_2881_,
        v_isMeta_boxed_2897_,
        v___x_2883_,
        v___x_2884_,
        v___x_2885_,
        v_inst_2886_,
        v_toApplicative_2887_,
        v_modifyEnv_2888_,
        v_inst_2889_,
        v_inst_2890_,
        v_inst_2891_,
        v_toBind_2892_,
        v_hint_2893_,
        v_inst_2894_,
        v_getEnv_2895_,
        v_____do__lift_2896_,
    );
    lean_dec_ref(v_____do__lift_2896_);
    return v_res_2898_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(
    mut v_inst_2899_: *mut LeanObject,
    mut v_inst_2900_: *mut LeanObject,
    mut v_inst_2901_: *mut LeanObject,
    mut v_inst_2902_: *mut LeanObject,
    mut v_inst_2903_: *mut LeanObject,
    mut v_inst_2904_: *mut LeanObject,
    mut v_mod_2905_: *mut LeanObject,
    mut v_isMeta_2906_: u8,
    mut v_hint_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2908_ = lean_ctor_get(v_inst_2899_, 0);
    lean_inc_ref(v_toApplicative_2908_);
    v_toBind_2909_ = lean_ctor_get(v_inst_2899_, 1);
    lean_inc_n(v_toBind_2909_, 2);
    v_getEnv_2910_ = lean_ctor_get(v_inst_2900_, 0);
    lean_inc_n(v_getEnv_2910_, 2);
    v_modifyEnv_2911_ = lean_ctor_get(v_inst_2900_, 1);
    lean_inc(v_modifyEnv_2911_);
    lean_dec_ref(v_inst_2900_);
    v___x_2912_ = l_Lean_instBEqExtraModUse___closed__0;
    v___x_2913_ = l_Lean_instHashableExtraModUse___closed__0;
    v___x_2914_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__0),
        core::ptr::addr_of_mut!(l_Lean_getExtraModUses___closed__0_once),
        _init_l_Lean_getExtraModUses___closed__0,
    );
    v___x_2915_ = lean_box((v_isMeta_2906_) as usize);
    v___f_2916_ = lean_alloc_closure(
        l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        16,
        15,
    );
    lean_closure_set(v___f_2916_, 0, v_mod_2905_);
    lean_closure_set(v___f_2916_, 1, v___x_2915_);
    lean_closure_set(v___f_2916_, 2, v___x_2914_);
    lean_closure_set(v___f_2916_, 3, v___x_2912_);
    lean_closure_set(v___f_2916_, 4, v___x_2913_);
    lean_closure_set(v___f_2916_, 5, v_inst_2901_);
    lean_closure_set(v___f_2916_, 6, v_toApplicative_2908_);
    lean_closure_set(v___f_2916_, 7, v_modifyEnv_2911_);
    lean_closure_set(v___f_2916_, 8, v_inst_2899_);
    lean_closure_set(v___f_2916_, 9, v_inst_2903_);
    lean_closure_set(v___f_2916_, 10, v_inst_2904_);
    lean_closure_set(v___f_2916_, 11, v_toBind_2909_);
    lean_closure_set(v___f_2916_, 12, v_hint_2907_);
    lean_closure_set(v___f_2916_, 13, v_inst_2902_);
    lean_closure_set(v___f_2916_, 14, v_getEnv_2910_);
    v___x_2917_ = lean_apply_4(
        v_toBind_2909_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2910_,
        v___f_2916_,
    );
    return v___x_2917_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(
    mut v_inst_2918_: *mut LeanObject,
    mut v_inst_2919_: *mut LeanObject,
    mut v_inst_2920_: *mut LeanObject,
    mut v_inst_2921_: *mut LeanObject,
    mut v_inst_2922_: *mut LeanObject,
    mut v_inst_2923_: *mut LeanObject,
    mut v_mod_2924_: *mut LeanObject,
    mut v_isMeta_2925_: *mut LeanObject,
    mut v_hint_2926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_2927_: u8 = 0;
    let mut v_res_2928_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2927_ = (lean_unbox(v_isMeta_2925_) as u8);
    v_res_2928_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(
        v_inst_2918_,
        v_inst_2919_,
        v_inst_2920_,
        v_inst_2921_,
        v_inst_2922_,
        v_inst_2923_,
        v_mod_2924_,
        v_isMeta_boxed_2927_,
        v_hint_2926_,
    );
    return v_res_2928_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(
    mut v_m_2929_: *mut LeanObject,
    mut v_inst_2930_: *mut LeanObject,
    mut v_inst_2931_: *mut LeanObject,
    mut v_inst_2932_: *mut LeanObject,
    mut v_inst_2933_: *mut LeanObject,
    mut v_inst_2934_: *mut LeanObject,
    mut v_inst_2935_: *mut LeanObject,
    mut v_mod_2936_: *mut LeanObject,
    mut v_isMeta_2937_: u8,
    mut v_hint_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    v___x_2939_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(
        v_inst_2930_,
        v_inst_2931_,
        v_inst_2932_,
        v_inst_2933_,
        v_inst_2934_,
        v_inst_2935_,
        v_mod_2936_,
        v_isMeta_2937_,
        v_hint_2938_,
    );
    return v___x_2939_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(
    mut v_m_2940_: *mut LeanObject,
    mut v_inst_2941_: *mut LeanObject,
    mut v_inst_2942_: *mut LeanObject,
    mut v_inst_2943_: *mut LeanObject,
    mut v_inst_2944_: *mut LeanObject,
    mut v_inst_2945_: *mut LeanObject,
    mut v_inst_2946_: *mut LeanObject,
    mut v_mod_2947_: *mut LeanObject,
    mut v_isMeta_2948_: *mut LeanObject,
    mut v_hint_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_2950_: u8 = 0;
    let mut v_res_2951_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2950_ = (lean_unbox(v_isMeta_2948_) as u8);
    v_res_2951_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(
        v_m_2940_,
        v_inst_2941_,
        v_inst_2942_,
        v_inst_2943_,
        v_inst_2944_,
        v_inst_2945_,
        v_inst_2946_,
        v_mod_2947_,
        v_isMeta_boxed_2950_,
        v_hint_2949_,
    );
    return v_res_2951_;
}
pub unsafe fn l_Lean_recordExtraModUse___redArg___lam__0(
    mut v_modName_2952_: *mut LeanObject,
    mut v_inst_2953_: *mut LeanObject,
    mut v_inst_2954_: *mut LeanObject,
    mut v_inst_2955_: *mut LeanObject,
    mut v_inst_2956_: *mut LeanObject,
    mut v_inst_2957_: *mut LeanObject,
    mut v_inst_2958_: *mut LeanObject,
    mut v_isMeta_2959_: u8,
    mut v_toApplicative_2960_: *mut LeanObject,
    mut v_____do__lift_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: u8 = 0;
    v___x_2962_ = l_Lean_Environment_mainModule(v_____do__lift_2961_);
    v___x_2963_ = lean_name_eq(v_modName_2952_, v___x_2962_);
    lean_dec(v___x_2962_);
    if v___x_2963_ == 0 {
        let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_2960_);
        v___x_2964_ = lean_box(0);
        v___x_2965_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(
            v_inst_2953_,
            v_inst_2954_,
            v_inst_2955_,
            v_inst_2956_,
            v_inst_2957_,
            v_inst_2958_,
            v_modName_2952_,
            v_isMeta_2959_,
            v___x_2964_,
        );
        return v___x_2965_;
    } else {
        let mut v_toPure_2966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_2958_);
        lean_dec_ref(v_inst_2957_);
        lean_dec(v_inst_2956_);
        lean_dec_ref(v_inst_2955_);
        lean_dec_ref(v_inst_2954_);
        lean_dec_ref(v_inst_2953_);
        lean_dec(v_modName_2952_);
        v_toPure_2966_ = lean_ctor_get(v_toApplicative_2960_, 1);
        lean_inc(v_toPure_2966_);
        lean_dec_ref(v_toApplicative_2960_);
        v___x_2967_ = lean_box(0);
        v___x_2968_ = lean_apply_2(v_toPure_2966_, lean_box(0), v___x_2967_);
        return v___x_2968_;
    }
}
pub unsafe fn l_Lean_recordExtraModUse___redArg___lam__0___boxed(
    mut v_modName_2969_: *mut LeanObject,
    mut v_inst_2970_: *mut LeanObject,
    mut v_inst_2971_: *mut LeanObject,
    mut v_inst_2972_: *mut LeanObject,
    mut v_inst_2973_: *mut LeanObject,
    mut v_inst_2974_: *mut LeanObject,
    mut v_inst_2975_: *mut LeanObject,
    mut v_isMeta_2976_: *mut LeanObject,
    mut v_toApplicative_2977_: *mut LeanObject,
    mut v_____do__lift_2978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_2979_: u8 = 0;
    let mut v_res_2980_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2979_ = (lean_unbox(v_isMeta_2976_) as u8);
    v_res_2980_ = l_Lean_recordExtraModUse___redArg___lam__0(
        v_modName_2969_,
        v_inst_2970_,
        v_inst_2971_,
        v_inst_2972_,
        v_inst_2973_,
        v_inst_2974_,
        v_inst_2975_,
        v_isMeta_boxed_2979_,
        v_toApplicative_2977_,
        v_____do__lift_2978_,
    );
    lean_dec_ref(v_____do__lift_2978_);
    return v_res_2980_;
}
pub unsafe fn l_Lean_recordExtraModUse___redArg(
    mut v_inst_2981_: *mut LeanObject,
    mut v_inst_2982_: *mut LeanObject,
    mut v_inst_2983_: *mut LeanObject,
    mut v_inst_2984_: *mut LeanObject,
    mut v_inst_2985_: *mut LeanObject,
    mut v_inst_2986_: *mut LeanObject,
    mut v_modName_2987_: *mut LeanObject,
    mut v_isMeta_2988_: u8,
) -> *mut LeanObject {
    let mut v_toApplicative_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2989_ = lean_ctor_get(v_inst_2981_, 0);
    lean_inc_ref(v_toApplicative_2989_);
    v_toBind_2990_ = lean_ctor_get(v_inst_2981_, 1);
    lean_inc(v_toBind_2990_);
    v_getEnv_2991_ = lean_ctor_get(v_inst_2982_, 0);
    lean_inc(v_getEnv_2991_);
    v___x_2992_ = lean_box((v_isMeta_2988_) as usize);
    v___f_2993_ = lean_alloc_closure(
        l_Lean_recordExtraModUse___redArg___lam__0___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_2993_, 0, v_modName_2987_);
    lean_closure_set(v___f_2993_, 1, v_inst_2981_);
    lean_closure_set(v___f_2993_, 2, v_inst_2982_);
    lean_closure_set(v___f_2993_, 3, v_inst_2983_);
    lean_closure_set(v___f_2993_, 4, v_inst_2984_);
    lean_closure_set(v___f_2993_, 5, v_inst_2985_);
    lean_closure_set(v___f_2993_, 6, v_inst_2986_);
    lean_closure_set(v___f_2993_, 7, v___x_2992_);
    lean_closure_set(v___f_2993_, 8, v_toApplicative_2989_);
    v___x_2994_ = lean_apply_4(
        v_toBind_2990_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2991_,
        v___f_2993_,
    );
    return v___x_2994_;
}
pub unsafe fn l_Lean_recordExtraModUse___redArg___boxed(
    mut v_inst_2995_: *mut LeanObject,
    mut v_inst_2996_: *mut LeanObject,
    mut v_inst_2997_: *mut LeanObject,
    mut v_inst_2998_: *mut LeanObject,
    mut v_inst_2999_: *mut LeanObject,
    mut v_inst_3000_: *mut LeanObject,
    mut v_modName_3001_: *mut LeanObject,
    mut v_isMeta_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3003_: u8 = 0;
    let mut v_res_3004_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3003_ = (lean_unbox(v_isMeta_3002_) as u8);
    v_res_3004_ = l_Lean_recordExtraModUse___redArg(
        v_inst_2995_,
        v_inst_2996_,
        v_inst_2997_,
        v_inst_2998_,
        v_inst_2999_,
        v_inst_3000_,
        v_modName_3001_,
        v_isMeta_boxed_3003_,
    );
    return v_res_3004_;
}
pub unsafe fn l_Lean_recordExtraModUse(
    mut v_m_3005_: *mut LeanObject,
    mut v_inst_3006_: *mut LeanObject,
    mut v_inst_3007_: *mut LeanObject,
    mut v_inst_3008_: *mut LeanObject,
    mut v_inst_3009_: *mut LeanObject,
    mut v_inst_3010_: *mut LeanObject,
    mut v_inst_3011_: *mut LeanObject,
    mut v_modName_3012_: *mut LeanObject,
    mut v_isMeta_3013_: u8,
) -> *mut LeanObject {
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    v___x_3014_ = l_Lean_recordExtraModUse___redArg(
        v_inst_3006_,
        v_inst_3007_,
        v_inst_3008_,
        v_inst_3009_,
        v_inst_3010_,
        v_inst_3011_,
        v_modName_3012_,
        v_isMeta_3013_,
    );
    return v___x_3014_;
}
pub unsafe fn l_Lean_recordExtraModUse___boxed(
    mut v_m_3015_: *mut LeanObject,
    mut v_inst_3016_: *mut LeanObject,
    mut v_inst_3017_: *mut LeanObject,
    mut v_inst_3018_: *mut LeanObject,
    mut v_inst_3019_: *mut LeanObject,
    mut v_inst_3020_: *mut LeanObject,
    mut v_inst_3021_: *mut LeanObject,
    mut v_modName_3022_: *mut LeanObject,
    mut v_isMeta_3023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3024_: u8 = 0;
    let mut v_res_3025_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3024_ = (lean_unbox(v_isMeta_3023_) as u8);
    v_res_3025_ = l_Lean_recordExtraModUse(
        v_m_3015_,
        v_inst_3016_,
        v_inst_3017_,
        v_inst_3018_,
        v_inst_3019_,
        v_inst_3020_,
        v_inst_3021_,
        v_modName_3022_,
        v_isMeta_boxed_3024_,
    );
    return v_res_3025_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__0(
    mut v_toPure_3026_: *mut LeanObject,
    mut v_____s_3027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    v___x_3028_ = lean_box(0);
    v___x_3029_ = lean_apply_2(v_toPure_3026_, lean_box(0), v___x_3028_);
    return v___x_3029_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__1(
    mut v___x_3030_: *mut LeanObject,
    mut v_toPure_3031_: *mut LeanObject,
    mut v_r_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    v___x_3033_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3033_, 0, v___x_3030_);
    v___x_3034_ = lean_apply_2(v_toPure_3031_, lean_box(0), v___x_3033_);
    return v___x_3034_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__2(
    mut v_env_3035_: *mut LeanObject,
    mut v___x_3036_: *mut LeanObject,
    mut v_inst_3037_: *mut LeanObject,
    mut v_inst_3038_: *mut LeanObject,
    mut v_inst_3039_: *mut LeanObject,
    mut v_inst_3040_: *mut LeanObject,
    mut v_inst_3041_: *mut LeanObject,
    mut v_inst_3042_: *mut LeanObject,
    mut v_declName_3043_: *mut LeanObject,
    mut v_toBind_3044_: *mut LeanObject,
    mut v___f_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
    mut v_x_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    v___x_3049_ = l_Lean_Environment_header(v_env_3035_);
    v_modules_3050_ = lean_ctor_get(v___x_3049_, 3);
    lean_inc_ref(v_modules_3050_);
    lean_dec_ref(v___x_3049_);
    v___x_3051_ = lean_array_get(v___x_3036_, v_modules_3050_, v_a_3046_);
    lean_dec_ref(v_modules_3050_);
    v_toImport_3052_ = lean_ctor_get(v___x_3051_, 0);
    lean_inc_ref(v_toImport_3052_);
    lean_dec(v___x_3051_);
    v_module_3053_ = lean_ctor_get(v_toImport_3052_, 0);
    lean_inc(v_module_3053_);
    lean_dec_ref(v_toImport_3052_);
    v___x_3054_ = 0;
    v___x_3055_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(
        v_inst_3037_,
        v_inst_3038_,
        v_inst_3039_,
        v_inst_3040_,
        v_inst_3041_,
        v_inst_3042_,
        v_module_3053_,
        v___x_3054_,
        v_declName_3043_,
    );
    v___x_3056_ = lean_apply_4(
        v_toBind_3044_,
        lean_box(0),
        lean_box(0),
        v___x_3055_,
        v___f_3045_,
    );
    return v___x_3056_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(
    mut v_env_3057_: *mut LeanObject,
    mut v___x_3058_: *mut LeanObject,
    mut v_inst_3059_: *mut LeanObject,
    mut v_inst_3060_: *mut LeanObject,
    mut v_inst_3061_: *mut LeanObject,
    mut v_inst_3062_: *mut LeanObject,
    mut v_inst_3063_: *mut LeanObject,
    mut v_inst_3064_: *mut LeanObject,
    mut v_declName_3065_: *mut LeanObject,
    mut v_toBind_3066_: *mut LeanObject,
    mut v___f_3067_: *mut LeanObject,
    mut v_a_3068_: *mut LeanObject,
    mut v_x_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3071_: *mut LeanObject = core::ptr::null_mut();
    v_res_3071_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(
        v_env_3057_,
        v___x_3058_,
        v_inst_3059_,
        v_inst_3060_,
        v_inst_3061_,
        v_inst_3062_,
        v_inst_3063_,
        v_inst_3064_,
        v_declName_3065_,
        v_toBind_3066_,
        v___f_3067_,
        v_a_3068_,
        v_x_3069_,
        v___y_3070_,
    );
    lean_dec(v_a_3068_);
    lean_dec_ref(v___x_3058_);
    lean_dec_ref(v_env_3057_);
    return v_res_3071_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__3(
    mut v_toPure_3072_: *mut LeanObject,
    mut v_env_3073_: *mut LeanObject,
    mut v___x_3074_: *mut LeanObject,
    mut v_inst_3075_: *mut LeanObject,
    mut v_inst_3076_: *mut LeanObject,
    mut v_inst_3077_: *mut LeanObject,
    mut v_inst_3078_: *mut LeanObject,
    mut v_inst_3079_: *mut LeanObject,
    mut v_inst_3080_: *mut LeanObject,
    mut v_declName_3081_: *mut LeanObject,
    mut v_toBind_3082_: *mut LeanObject,
    mut v___f_3083_: *mut LeanObject,
    mut v___x_3084_: *mut LeanObject,
    mut v___x_3085_: *mut LeanObject,
    mut v___x_3086_: *mut LeanObject,
    mut v_____r_3087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3093_: usize = 0;
    let mut v___x_3094_: usize = 0;
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3097_ = l_Lean_indirectModUseExt;
                v___x_3098_ = lean_box(1);
                v___x_3099_ = lean_box(0);
                lean_inc_ref(v_env_3073_);
                v___x_3100_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3084_,
                    v___x_3097_,
                    v_env_3073_,
                    v___x_3098_,
                    v___x_3099_,
                );
                lean_inc(v_declName_3081_);
                v___x_3101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___x_3085_,
                    v___x_3086_,
                    v___x_3100_,
                    v_declName_3081_,
                );
                lean_dec(v___x_3100_);
                if lean_obj_tag(v___x_3101_) == 0 {
                    v___x_3102_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0;
                    v___y_3089_ = v___x_3102_;
                    state = 1;
                    continue;
                } else {
                    v_val_3103_ = lean_ctor_get(v___x_3101_, 0);
                    lean_inc(v_val_3103_);
                    lean_dec_ref_known(v___x_3101_, 1);
                    v___y_3089_ = v_val_3103_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3090_ = lean_box(0);
                v___f_3091_ = lean_alloc_closure(
                    l_Lean_recordExtraModUseFromDecl___redArg___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3091_, 0, v___x_3090_);
                lean_closure_set(v___f_3091_, 1, v_toPure_3072_);
                lean_inc(v_toBind_3082_);
                lean_inc_ref(v_inst_3075_);
                v___f_3092_ = lean_alloc_closure(
                    l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    14,
                    11,
                );
                lean_closure_set(v___f_3092_, 0, v_env_3073_);
                lean_closure_set(v___f_3092_, 1, v___x_3074_);
                lean_closure_set(v___f_3092_, 2, v_inst_3075_);
                lean_closure_set(v___f_3092_, 3, v_inst_3076_);
                lean_closure_set(v___f_3092_, 4, v_inst_3077_);
                lean_closure_set(v___f_3092_, 5, v_inst_3078_);
                lean_closure_set(v___f_3092_, 6, v_inst_3079_);
                lean_closure_set(v___f_3092_, 7, v_inst_3080_);
                lean_closure_set(v___f_3092_, 8, v_declName_3081_);
                lean_closure_set(v___f_3092_, 9, v_toBind_3082_);
                lean_closure_set(v___f_3092_, 10, v___f_3091_);
                v_sz_3093_ = lean_array_size(v___y_3089_);
                v___x_3094_ = 0usize;
                v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_3075_,
                    v___y_3089_,
                    v___f_3092_,
                    v_sz_3093_,
                    v___x_3094_,
                    v___x_3090_,
                );
                v___x_3096_ = lean_apply_4(
                    v_toBind_3082_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3095_,
                    v___f_3083_,
                );
                return v___x_3096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__4(
    mut v___x_3104_: *mut LeanObject,
    mut v_inst_3105_: *mut LeanObject,
    mut v_inst_3106_: *mut LeanObject,
    mut v_inst_3107_: *mut LeanObject,
    mut v_inst_3108_: *mut LeanObject,
    mut v_inst_3109_: *mut LeanObject,
    mut v_inst_3110_: *mut LeanObject,
    mut v_declName_3111_: *mut LeanObject,
    mut v_toBind_3112_: *mut LeanObject,
    mut v___f_3113_: *mut LeanObject,
    mut v_isMeta_3114_: u8,
    mut v_____do__lift_3115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3117_: u8 = 0;
    let mut v_toImport_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_isMeta_3114_ == 0 {
                    lean_dec_ref(v_____do__lift_3115_);
                    v___y_3117_ = v_isMeta_3114_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_declName_3111_);
                    v___x_3122_ = l_Lean_isMarkedMeta(v_____do__lift_3115_, v_declName_3111_);
                    if v___x_3122_ == 0 {
                        v___y_3117_ = v_isMeta_3114_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3123_ = 0;
                        v___y_3117_ = v___x_3123_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toImport_3118_ = lean_ctor_get(v___x_3104_, 0);
                lean_inc_ref(v_toImport_3118_);
                lean_dec_ref(v___x_3104_);
                v_module_3119_ = lean_ctor_get(v_toImport_3118_, 0);
                lean_inc(v_module_3119_);
                lean_dec_ref(v_toImport_3118_);
                v___x_3120_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(
                    v_inst_3105_,
                    v_inst_3106_,
                    v_inst_3107_,
                    v_inst_3108_,
                    v_inst_3109_,
                    v_inst_3110_,
                    v_module_3119_,
                    v___y_3117_,
                    v_declName_3111_,
                );
                v___x_3121_ = lean_apply_4(
                    v_toBind_3112_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3120_,
                    v___f_3113_,
                );
                return v___x_3121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(
    mut v___x_3124_: *mut LeanObject,
    mut v_inst_3125_: *mut LeanObject,
    mut v_inst_3126_: *mut LeanObject,
    mut v_inst_3127_: *mut LeanObject,
    mut v_inst_3128_: *mut LeanObject,
    mut v_inst_3129_: *mut LeanObject,
    mut v_inst_3130_: *mut LeanObject,
    mut v_declName_3131_: *mut LeanObject,
    mut v_toBind_3132_: *mut LeanObject,
    mut v___f_3133_: *mut LeanObject,
    mut v_isMeta_3134_: *mut LeanObject,
    mut v_____do__lift_3135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3136_: u8 = 0;
    let mut v_res_3137_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3136_ = (lean_unbox(v_isMeta_3134_) as u8);
    v_res_3137_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(
        v___x_3124_,
        v_inst_3125_,
        v_inst_3126_,
        v_inst_3127_,
        v_inst_3128_,
        v_inst_3129_,
        v_inst_3130_,
        v_declName_3131_,
        v_toBind_3132_,
        v___f_3133_,
        v_isMeta_boxed_3136_,
        v_____do__lift_3135_,
    );
    return v_res_3137_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__5(
    mut v_toPure_3138_: *mut LeanObject,
    mut v_declName_3139_: *mut LeanObject,
    mut v___x_3140_: *mut LeanObject,
    mut v_inst_3141_: *mut LeanObject,
    mut v_inst_3142_: *mut LeanObject,
    mut v_inst_3143_: *mut LeanObject,
    mut v_inst_3144_: *mut LeanObject,
    mut v_inst_3145_: *mut LeanObject,
    mut v_inst_3146_: *mut LeanObject,
    mut v_toBind_3147_: *mut LeanObject,
    mut v___f_3148_: *mut LeanObject,
    mut v___x_3149_: *mut LeanObject,
    mut v___x_3150_: *mut LeanObject,
    mut v___x_3151_: *mut LeanObject,
    mut v_isMeta_3152_: u8,
    mut v_getEnv_3153_: *mut LeanObject,
    mut v_env_3154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u8 = 0;
    let mut v___f_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3158_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3154_, v_declName_3139_);
                if lean_obj_tag(v___x_3158_) == 0 {
                    lean_dec_ref(v_env_3154_);
                    lean_dec(v_getEnv_3153_);
                    lean_dec_ref(v___x_3151_);
                    lean_dec_ref(v___x_3150_);
                    lean_dec_ref(v___x_3149_);
                    lean_dec(v___f_3148_);
                    lean_dec(v_toBind_3147_);
                    lean_dec(v_inst_3146_);
                    lean_dec_ref(v_inst_3145_);
                    lean_dec(v_inst_3144_);
                    lean_dec_ref(v_inst_3143_);
                    lean_dec_ref(v_inst_3142_);
                    lean_dec_ref(v_inst_3141_);
                    lean_dec_ref(v___x_3140_);
                    lean_dec(v_declName_3139_);
                    state = 1;
                    continue;
                } else {
                    v_val_3159_ = lean_ctor_get(v___x_3158_, 0);
                    lean_inc(v_val_3159_);
                    lean_dec_ref_known(v___x_3158_, 1);
                    v___x_3160_ = l_Lean_Environment_header(v_env_3154_);
                    v_modules_3161_ = lean_ctor_get(v___x_3160_, 3);
                    lean_inc_ref(v_modules_3161_);
                    lean_dec_ref(v___x_3160_);
                    v___x_3162_ = lean_array_get_size(v_modules_3161_);
                    v___x_3163_ = lean_nat_dec_lt(v_val_3159_, v___x_3162_);
                    if v___x_3163_ == 0 {
                        lean_dec_ref(v_modules_3161_);
                        lean_dec(v_val_3159_);
                        lean_dec_ref(v_env_3154_);
                        lean_dec(v_getEnv_3153_);
                        lean_dec_ref(v___x_3151_);
                        lean_dec_ref(v___x_3150_);
                        lean_dec_ref(v___x_3149_);
                        lean_dec(v___f_3148_);
                        lean_dec(v_toBind_3147_);
                        lean_dec(v_inst_3146_);
                        lean_dec_ref(v_inst_3145_);
                        lean_dec(v_inst_3144_);
                        lean_dec_ref(v_inst_3143_);
                        lean_dec_ref(v_inst_3142_);
                        lean_dec_ref(v_inst_3141_);
                        lean_dec_ref(v___x_3140_);
                        lean_dec(v_declName_3139_);
                        state = 1;
                        continue;
                    } else {
                        lean_inc_n(v_toBind_3147_, 2);
                        lean_inc(v_declName_3139_);
                        lean_inc(v_inst_3146_);
                        lean_inc_ref(v_inst_3145_);
                        lean_inc(v_inst_3144_);
                        lean_inc_ref(v_inst_3143_);
                        lean_inc_ref(v_inst_3142_);
                        lean_inc_ref(v_inst_3141_);
                        v___f_3164_ = lean_alloc_closure(
                            l_Lean_recordExtraModUseFromDecl___redArg___lam__3
                                as *mut core::ffi::c_void,
                            16,
                            15,
                        );
                        lean_closure_set(v___f_3164_, 0, v_toPure_3138_);
                        lean_closure_set(v___f_3164_, 1, v_env_3154_);
                        lean_closure_set(v___f_3164_, 2, v___x_3140_);
                        lean_closure_set(v___f_3164_, 3, v_inst_3141_);
                        lean_closure_set(v___f_3164_, 4, v_inst_3142_);
                        lean_closure_set(v___f_3164_, 5, v_inst_3143_);
                        lean_closure_set(v___f_3164_, 6, v_inst_3144_);
                        lean_closure_set(v___f_3164_, 7, v_inst_3145_);
                        lean_closure_set(v___f_3164_, 8, v_inst_3146_);
                        lean_closure_set(v___f_3164_, 9, v_declName_3139_);
                        lean_closure_set(v___f_3164_, 10, v_toBind_3147_);
                        lean_closure_set(v___f_3164_, 11, v___f_3148_);
                        lean_closure_set(v___f_3164_, 12, v___x_3149_);
                        lean_closure_set(v___f_3164_, 13, v___x_3150_);
                        lean_closure_set(v___f_3164_, 14, v___x_3151_);
                        v___x_3165_ = lean_array_fget(v_modules_3161_, v_val_3159_);
                        lean_dec(v_val_3159_);
                        lean_dec_ref(v_modules_3161_);
                        v___x_3166_ = lean_box((v_isMeta_3152_) as usize);
                        v___f_3167_ = lean_alloc_closure(
                            l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed
                                as *mut core::ffi::c_void,
                            12,
                            11,
                        );
                        lean_closure_set(v___f_3167_, 0, v___x_3165_);
                        lean_closure_set(v___f_3167_, 1, v_inst_3141_);
                        lean_closure_set(v___f_3167_, 2, v_inst_3142_);
                        lean_closure_set(v___f_3167_, 3, v_inst_3143_);
                        lean_closure_set(v___f_3167_, 4, v_inst_3144_);
                        lean_closure_set(v___f_3167_, 5, v_inst_3145_);
                        lean_closure_set(v___f_3167_, 6, v_inst_3146_);
                        lean_closure_set(v___f_3167_, 7, v_declName_3139_);
                        lean_closure_set(v___f_3167_, 8, v_toBind_3147_);
                        lean_closure_set(v___f_3167_, 9, v___f_3164_);
                        lean_closure_set(v___f_3167_, 10, v___x_3166_);
                        v___x_3168_ = lean_apply_4(
                            v_toBind_3147_,
                            lean_box(0),
                            lean_box(0),
                            v_getEnv_3153_,
                            v___f_3167_,
                        );
                        return v___x_3168_;
                    }
                }
            }
            1 => {
                v___x_3156_ = lean_box(0);
                v___x_3157_ = lean_apply_2(v_toPure_3138_, lean_box(0), v___x_3156_);
                return v___x_3157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_3169_: *mut LeanObject = *_args.add(0);
    let mut v_declName_3170_: *mut LeanObject = *_args.add(1);
    let mut v___x_3171_: *mut LeanObject = *_args.add(2);
    let mut v_inst_3172_: *mut LeanObject = *_args.add(3);
    let mut v_inst_3173_: *mut LeanObject = *_args.add(4);
    let mut v_inst_3174_: *mut LeanObject = *_args.add(5);
    let mut v_inst_3175_: *mut LeanObject = *_args.add(6);
    let mut v_inst_3176_: *mut LeanObject = *_args.add(7);
    let mut v_inst_3177_: *mut LeanObject = *_args.add(8);
    let mut v_toBind_3178_: *mut LeanObject = *_args.add(9);
    let mut v___f_3179_: *mut LeanObject = *_args.add(10);
    let mut v___x_3180_: *mut LeanObject = *_args.add(11);
    let mut v___x_3181_: *mut LeanObject = *_args.add(12);
    let mut v___x_3182_: *mut LeanObject = *_args.add(13);
    let mut v_isMeta_3183_: *mut LeanObject = *_args.add(14);
    let mut v_getEnv_3184_: *mut LeanObject = *_args.add(15);
    let mut v_env_3185_: *mut LeanObject = *_args.add(16);
    let mut v_isMeta_boxed_3186_: u8 = 0;
    let mut v_res_3187_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3186_ = (lean_unbox(v_isMeta_3183_) as u8);
    v_res_3187_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(
        v_toPure_3169_,
        v_declName_3170_,
        v___x_3171_,
        v_inst_3172_,
        v_inst_3173_,
        v_inst_3174_,
        v_inst_3175_,
        v_inst_3176_,
        v_inst_3177_,
        v_toBind_3178_,
        v___f_3179_,
        v___x_3180_,
        v___x_3181_,
        v___x_3182_,
        v_isMeta_boxed_3186_,
        v_getEnv_3184_,
        v_env_3185_,
    );
    return v_res_3187_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg(
    mut v_inst_3188_: *mut LeanObject,
    mut v_inst_3189_: *mut LeanObject,
    mut v_inst_3190_: *mut LeanObject,
    mut v_inst_3191_: *mut LeanObject,
    mut v_inst_3192_: *mut LeanObject,
    mut v_inst_3193_: *mut LeanObject,
    mut v_declName_3194_: *mut LeanObject,
    mut v_isMeta_3195_: u8,
) -> *mut LeanObject {
    let mut v_toApplicative_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3196_ = lean_ctor_get(v_inst_3188_, 0);
    v_toBind_3197_ = lean_ctor_get(v_inst_3188_, 1);
    lean_inc_n(v_toBind_3197_, 2);
    v_getEnv_3198_ = lean_ctor_get(v_inst_3189_, 0);
    lean_inc_n(v_getEnv_3198_, 2);
    v_toPure_3199_ = lean_ctor_get(v_toApplicative_3196_, 1);
    lean_inc_n(v_toPure_3199_, 2);
    v___x_3200_ = l_Lean_getIndirectModUses___closed__0;
    v___x_3201_ = l_Lean_getIndirectModUses___closed__1;
    v___x_3202_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getIndirectModUses___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getIndirectModUses___closed__2_once),
        _init_l_Lean_getIndirectModUses___closed__2,
    );
    v___x_3203_ = l_Lean_instInhabitedEffectiveImport_default;
    v___f_3204_ = lean_alloc_closure(
        l_Lean_recordExtraModUseFromDecl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3204_, 0, v_toPure_3199_);
    v___x_3205_ = lean_box((v_isMeta_3195_) as usize);
    v___f_3206_ = lean_alloc_closure(
        l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    lean_closure_set(v___f_3206_, 0, v_toPure_3199_);
    lean_closure_set(v___f_3206_, 1, v_declName_3194_);
    lean_closure_set(v___f_3206_, 2, v___x_3203_);
    lean_closure_set(v___f_3206_, 3, v_inst_3188_);
    lean_closure_set(v___f_3206_, 4, v_inst_3189_);
    lean_closure_set(v___f_3206_, 5, v_inst_3190_);
    lean_closure_set(v___f_3206_, 6, v_inst_3191_);
    lean_closure_set(v___f_3206_, 7, v_inst_3192_);
    lean_closure_set(v___f_3206_, 8, v_inst_3193_);
    lean_closure_set(v___f_3206_, 9, v_toBind_3197_);
    lean_closure_set(v___f_3206_, 10, v___f_3204_);
    lean_closure_set(v___f_3206_, 11, v___x_3202_);
    lean_closure_set(v___f_3206_, 12, v___x_3200_);
    lean_closure_set(v___f_3206_, 13, v___x_3201_);
    lean_closure_set(v___f_3206_, 14, v___x_3205_);
    lean_closure_set(v___f_3206_, 15, v_getEnv_3198_);
    v___x_3207_ = lean_apply_4(
        v_toBind_3197_,
        lean_box(0),
        lean_box(0),
        v_getEnv_3198_,
        v___f_3206_,
    );
    return v___x_3207_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___redArg___boxed(
    mut v_inst_3208_: *mut LeanObject,
    mut v_inst_3209_: *mut LeanObject,
    mut v_inst_3210_: *mut LeanObject,
    mut v_inst_3211_: *mut LeanObject,
    mut v_inst_3212_: *mut LeanObject,
    mut v_inst_3213_: *mut LeanObject,
    mut v_declName_3214_: *mut LeanObject,
    mut v_isMeta_3215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3216_: u8 = 0;
    let mut v_res_3217_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3216_ = (lean_unbox(v_isMeta_3215_) as u8);
    v_res_3217_ = l_Lean_recordExtraModUseFromDecl___redArg(
        v_inst_3208_,
        v_inst_3209_,
        v_inst_3210_,
        v_inst_3211_,
        v_inst_3212_,
        v_inst_3213_,
        v_declName_3214_,
        v_isMeta_boxed_3216_,
    );
    return v_res_3217_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl(
    mut v_m_3218_: *mut LeanObject,
    mut v_inst_3219_: *mut LeanObject,
    mut v_inst_3220_: *mut LeanObject,
    mut v_inst_3221_: *mut LeanObject,
    mut v_inst_3222_: *mut LeanObject,
    mut v_inst_3223_: *mut LeanObject,
    mut v_inst_3224_: *mut LeanObject,
    mut v_declName_3225_: *mut LeanObject,
    mut v_isMeta_3226_: u8,
) -> *mut LeanObject {
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    v___x_3227_ = l_Lean_recordExtraModUseFromDecl___redArg(
        v_inst_3219_,
        v_inst_3220_,
        v_inst_3221_,
        v_inst_3222_,
        v_inst_3223_,
        v_inst_3224_,
        v_declName_3225_,
        v_isMeta_3226_,
    );
    return v___x_3227_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___boxed(
    mut v_m_3228_: *mut LeanObject,
    mut v_inst_3229_: *mut LeanObject,
    mut v_inst_3230_: *mut LeanObject,
    mut v_inst_3231_: *mut LeanObject,
    mut v_inst_3232_: *mut LeanObject,
    mut v_inst_3233_: *mut LeanObject,
    mut v_inst_3234_: *mut LeanObject,
    mut v_declName_3235_: *mut LeanObject,
    mut v_isMeta_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3237_: u8 = 0;
    let mut v_res_3238_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3237_ = (lean_unbox(v_isMeta_3236_) as u8);
    v_res_3238_ = l_Lean_recordExtraModUseFromDecl(
        v_m_3228_,
        v_inst_3229_,
        v_inst_3230_,
        v_inst_3231_,
        v_inst_3232_,
        v_inst_3233_,
        v_inst_3234_,
        v_declName_3235_,
        v_isMeta_boxed_3237_,
    );
    return v_res_3238_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(
    mut v_s_3239_: *mut LeanObject,
    mut v_e_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    v___x_3241_ = lean_box(0);
    return v___x_3241_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(
    mut v_x_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    v___x_3243_ = lean_box(0);
    return v___x_3243_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(
    mut v_x_3244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3245_: *mut LeanObject = core::ptr::null_mut();
    v_res_3245_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_3244_);
    lean_dec_ref(v_x_3244_);
    return v_res_3245_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(
    mut v_es_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    v___x_3247_ = lean_array_mk(v_es_3246_);
    return v___x_3247_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    v___x_3263_ = l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_;
    v___x_3264_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_3263_);
    return v___x_3264_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(
    mut v_a_3265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3266_: *mut LeanObject = core::ptr::null_mut();
    v_res_3266_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
    return v_res_3266_;
}
pub unsafe fn l_Lean_isExtraRevModUse(
    mut v_env_3270_: *mut LeanObject,
    mut v_modIdx_3271_: *mut LeanObject,
) -> u8 {
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: u8 = 0;
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: u8 = 0;
    v___x_3272_ = l_Lean_isExtraRevModUse___closed__0;
    v___x_3273_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
    v___x_3274_ = 0;
    v___x_3275_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
        v___x_3272_,
        v___x_3273_,
        v_env_3270_,
        v_modIdx_3271_,
        v___x_3274_,
    );
    v___x_3276_ = lean_array_get_size(v___x_3275_);
    lean_dec_ref(v___x_3275_);
    v___x_3277_ = lean_unsigned_to_nat(0);
    v___x_3278_ = lean_nat_dec_eq(v___x_3276_, v___x_3277_);
    if v___x_3278_ == 0 {
        let mut v___x_3279_: u8 = 0;
        v___x_3279_ = 1;
        return v___x_3279_;
    } else {
        let mut v___x_3280_: u8 = 0;
        v___x_3280_ = 0;
        return v___x_3280_;
    }
}
pub unsafe fn l_Lean_isExtraRevModUse___boxed(
    mut v_env_3281_: *mut LeanObject,
    mut v_modIdx_3282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3283_: u8 = 0;
    let mut v_r_3284_: *mut LeanObject = core::ptr::null_mut();
    v_res_3283_ = l_Lean_isExtraRevModUse(v_env_3281_, v_modIdx_3282_);
    lean_dec(v_modIdx_3282_);
    lean_dec_ref(v_env_3281_);
    v_r_3284_ = lean_box((v_res_3283_) as usize);
    return v_r_3284_;
}
pub unsafe fn l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(
    mut v___x_3285_: *mut LeanObject,
    mut v_x_3286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toEnvExtension_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    v_toEnvExtension_3287_ = lean_ctor_get(v___x_3285_, 0);
    v_asyncMode_3288_ = lean_ctor_get(v_toEnvExtension_3287_, 2);
    lean_inc(v_asyncMode_3288_);
    v___x_3289_ = lean_box(0);
    v___x_3290_ = lean_box(0);
    v___x_3291_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_3285_,
        v_x_3286_,
        v___x_3289_,
        v_asyncMode_3288_,
        v___x_3290_,
    );
    lean_dec(v_asyncMode_3288_);
    return v___x_3291_;
}
pub unsafe fn _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    v___x_3293_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__0;
    v___x_3294_ = l_Lean_stringToMessageData(v___x_3293_);
    return v___x_3294_;
}
pub unsafe fn l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(
    mut v_modifyEnv_3295_: *mut LeanObject,
    mut v___f_3296_: *mut LeanObject,
    mut v_inst_3297_: *mut LeanObject,
    mut v_inst_3298_: *mut LeanObject,
    mut v_inst_3299_: *mut LeanObject,
    mut v_inst_3300_: *mut LeanObject,
    mut v_cls_3301_: *mut LeanObject,
    mut v_toBind_3302_: *mut LeanObject,
    mut v___f_3303_: *mut LeanObject,
    mut v_____do__lift_3304_: u8,
) -> *mut LeanObject {
    if v_____do__lift_3304_ == 0 {
        let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_3303_);
        lean_dec(v_toBind_3302_);
        lean_dec(v_cls_3301_);
        lean_dec(v_inst_3300_);
        lean_dec_ref(v_inst_3299_);
        lean_dec_ref(v_inst_3298_);
        lean_dec_ref(v_inst_3297_);
        v___x_3305_ = lean_apply_1(v_modifyEnv_3295_, v___f_3296_);
        return v___x_3305_;
    } else {
        let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_3296_);
        lean_dec(v_modifyEnv_3295_);
        v___x_3306_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1_once
            ),
            _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___closed__1,
        );
        v___x_3307_ = l_Lean_addTrace___redArg(
            v_inst_3297_,
            v_inst_3298_,
            v_inst_3299_,
            v_inst_3300_,
            v_cls_3301_,
            v___x_3306_,
        );
        v___x_3308_ = lean_apply_4(
            v_toBind_3302_,
            lean_box(0),
            lean_box(0),
            v___x_3307_,
            v___f_3303_,
        );
        return v___x_3308_;
    }
}
pub unsafe fn l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed(
    mut v_modifyEnv_3309_: *mut LeanObject,
    mut v___f_3310_: *mut LeanObject,
    mut v_inst_3311_: *mut LeanObject,
    mut v_inst_3312_: *mut LeanObject,
    mut v_inst_3313_: *mut LeanObject,
    mut v_inst_3314_: *mut LeanObject,
    mut v_cls_3315_: *mut LeanObject,
    mut v_toBind_3316_: *mut LeanObject,
    mut v___f_3317_: *mut LeanObject,
    mut v_____do__lift_3318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_328__boxed_3319_: u8 = 0;
    let mut v_res_3320_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_328__boxed_3319_ = (lean_unbox(v_____do__lift_3318_) as u8);
    v_res_3320_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2(
        v_modifyEnv_3309_,
        v___f_3310_,
        v_inst_3311_,
        v_inst_3312_,
        v_inst_3313_,
        v_inst_3314_,
        v_cls_3315_,
        v_toBind_3316_,
        v___f_3317_,
        v_____do__lift_328__boxed_3319_,
    );
    return v_res_3320_;
}
pub unsafe fn _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0()
-> *mut LeanObject {
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3322_: *mut LeanObject = core::ptr::null_mut();
    v___x_3321_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
    v___f_3322_ = lean_alloc_closure(
        l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3322_, 0, v___x_3321_);
    return v___f_3322_;
}
pub unsafe fn l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(
    mut v___x_3323_: *mut LeanObject,
    mut v_toApplicative_3324_: *mut LeanObject,
    mut v_inst_3325_: *mut LeanObject,
    mut v_modifyEnv_3326_: *mut LeanObject,
    mut v_inst_3327_: *mut LeanObject,
    mut v_inst_3328_: *mut LeanObject,
    mut v_inst_3329_: *mut LeanObject,
    mut v_toBind_3330_: *mut LeanObject,
    mut v_inst_3331_: *mut LeanObject,
    mut v_____do__lift_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: u8 = 0;
    v___x_3333_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
    v___x_3334_ = lean_box(1);
    v___x_3335_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(
        v___x_3323_,
        v___x_3333_,
        v_____do__lift_3332_,
        v___x_3334_,
    );
    v___x_3336_ = l_List_isEmpty___redArg(v___x_3335_);
    lean_dec(v___x_3335_);
    if v___x_3336_ == 0 {
        let mut v_toPure_3337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_3331_);
        lean_dec(v_toBind_3330_);
        lean_dec(v_inst_3329_);
        lean_dec_ref(v_inst_3328_);
        lean_dec_ref(v_inst_3327_);
        lean_dec(v_modifyEnv_3326_);
        lean_dec_ref(v_inst_3325_);
        v_toPure_3337_ = lean_ctor_get(v_toApplicative_3324_, 1);
        lean_inc(v_toPure_3337_);
        lean_dec_ref(v_toApplicative_3324_);
        v___x_3338_ = lean_box(0);
        v___x_3339_ = lean_apply_2(v_toPure_3337_, lean_box(0), v___x_3338_);
        return v___x_3339_;
    } else {
        let mut v_getInheritedTraceOptions_3340_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_3341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3343_: *mut LeanObject = core::ptr::null_mut();
        let mut v_cls_3344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
        v_getInheritedTraceOptions_3340_ = lean_ctor_get(v_inst_3325_, 2);
        lean_inc(v_getInheritedTraceOptions_3340_);
        v_toPure_3341_ = lean_ctor_get(v_toApplicative_3324_, 1);
        lean_inc(v_toPure_3341_);
        lean_dec_ref(v_toApplicative_3324_);
        v___f_3342_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0
            ),
            core::ptr::addr_of_mut!(
                l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_once
            ),
            _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0,
        );
        lean_inc(v_modifyEnv_3326_);
        v___f_3343_ = lean_alloc_closure(
            l_Lean_recordIndirectModUse___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_3343_, 0, v_modifyEnv_3326_);
        lean_closure_set(v___f_3343_, 1, v___f_3342_);
        v_cls_3344_ = l_Lean_recordIndirectModUse___redArg___lam__5___closed__1;
        lean_inc_n(v_toBind_3330_, 3);
        v___f_3345_ = lean_alloc_closure(
            l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__2___boxed
                as *mut core::ffi::c_void,
            10,
            9,
        );
        lean_closure_set(v___f_3345_, 0, v_modifyEnv_3326_);
        lean_closure_set(v___f_3345_, 1, v___f_3342_);
        lean_closure_set(v___f_3345_, 2, v_inst_3327_);
        lean_closure_set(v___f_3345_, 3, v_inst_3325_);
        lean_closure_set(v___f_3345_, 4, v_inst_3328_);
        lean_closure_set(v___f_3345_, 5, v_inst_3329_);
        lean_closure_set(v___f_3345_, 6, v_cls_3344_);
        lean_closure_set(v___f_3345_, 7, v_toBind_3330_);
        lean_closure_set(v___f_3345_, 8, v___f_3343_);
        v___f_3346_ = lean_alloc_closure(
            l_Lean_recordIndirectModUse___redArg___lam__4 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_3346_, 0, v_toPure_3341_);
        lean_closure_set(v___f_3346_, 1, v_cls_3344_);
        lean_closure_set(v___f_3346_, 2, v_toBind_3330_);
        lean_closure_set(v___f_3346_, 3, v_inst_3331_);
        v___x_3347_ = lean_apply_4(
            v_toBind_3330_,
            lean_box(0),
            lean_box(0),
            v_getInheritedTraceOptions_3340_,
            v___f_3346_,
        );
        v___x_3348_ = lean_apply_4(
            v_toBind_3330_,
            lean_box(0),
            lean_box(0),
            v___x_3347_,
            v___f_3345_,
        );
        return v___x_3348_;
    }
}
pub unsafe fn l_Lean_recordExtraRevUseOfCurrentModule___redArg(
    mut v_inst_3349_: *mut LeanObject,
    mut v_inst_3350_: *mut LeanObject,
    mut v_inst_3351_: *mut LeanObject,
    mut v_inst_3352_: *mut LeanObject,
    mut v_inst_3353_: *mut LeanObject,
    mut v_inst_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3355_ = lean_ctor_get(v_inst_3349_, 0);
    lean_inc_ref(v_toApplicative_3355_);
    v_toBind_3356_ = lean_ctor_get(v_inst_3349_, 1);
    lean_inc_n(v_toBind_3356_, 2);
    v_getEnv_3357_ = lean_ctor_get(v_inst_3350_, 0);
    lean_inc(v_getEnv_3357_);
    v_modifyEnv_3358_ = lean_ctor_get(v_inst_3350_, 1);
    lean_inc(v_modifyEnv_3358_);
    lean_dec_ref(v_inst_3350_);
    v___x_3359_ = lean_box(0);
    v___f_3360_ = lean_alloc_closure(
        l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_3360_, 0, v___x_3359_);
    lean_closure_set(v___f_3360_, 1, v_toApplicative_3355_);
    lean_closure_set(v___f_3360_, 2, v_inst_3351_);
    lean_closure_set(v___f_3360_, 3, v_modifyEnv_3358_);
    lean_closure_set(v___f_3360_, 4, v_inst_3349_);
    lean_closure_set(v___f_3360_, 5, v_inst_3353_);
    lean_closure_set(v___f_3360_, 6, v_inst_3354_);
    lean_closure_set(v___f_3360_, 7, v_toBind_3356_);
    lean_closure_set(v___f_3360_, 8, v_inst_3352_);
    v___x_3361_ = lean_apply_4(
        v_toBind_3356_,
        lean_box(0),
        lean_box(0),
        v_getEnv_3357_,
        v___f_3360_,
    );
    return v___x_3361_;
}
pub unsafe fn l_Lean_recordExtraRevUseOfCurrentModule(
    mut v_m_3362_: *mut LeanObject,
    mut v_inst_3363_: *mut LeanObject,
    mut v_inst_3364_: *mut LeanObject,
    mut v_inst_3365_: *mut LeanObject,
    mut v_inst_3366_: *mut LeanObject,
    mut v_inst_3367_: *mut LeanObject,
    mut v_inst_3368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    v___x_3369_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(
        v_inst_3363_,
        v_inst_3364_,
        v_inst_3365_,
        v_inst_3366_,
        v_inst_3367_,
        v_inst_3368_,
    );
    return v___x_3369_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    v___x_3384_ = lean_unsigned_to_nat(4259277863);
    v___x_3385_ = l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
    v___x_3386_ = l_Lean_Name_num___override(v___x_3385_, v___x_3384_);
    return v___x_3386_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    v___x_3388_ = l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
    v___x_3389_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once), _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
    v___x_3390_ = l_Lean_Name_str___override(v___x_3389_, v___x_3388_);
    return v___x_3390_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    v___x_3392_ = l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
    v___x_3393_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once), _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
    v___x_3394_ = l_Lean_Name_str___override(v___x_3393_, v___x_3392_);
    return v___x_3394_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    v___x_3395_ = lean_unsigned_to_nat(2);
    v___x_3396_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once), _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
    v___x_3397_ = l_Lean_Name_num___override(v___x_3396_, v___x_3395_);
    return v___x_3397_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_recordIndirectModUse___redArg___lam__5___closed__1;
    v___x_3400_ = 0;
    v___x_3401_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once), _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
    v___x_3402_ = l_Lean_registerTraceClass(v___x_3399_, v___x_3400_, v___x_3401_);
    return v___x_3402_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(
    mut v_a_3403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3404_: *mut LeanObject = core::ptr::null_mut();
    v_res_3404_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
    return v_res_3404_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ExtraModUses(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_indirectModUseExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_indirectModUseExt);
    lean_dec_ref(res);
    res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_ExtraModUses_0__Lean_extraModUses = lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_extraModUses);
    lean_dec_ref(res);
    res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt = lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt);
    lean_dec_ref(res);
    res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ExtraModUses(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ExtraModUses(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_MetaAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_ExtraModUses(builtin);
}
