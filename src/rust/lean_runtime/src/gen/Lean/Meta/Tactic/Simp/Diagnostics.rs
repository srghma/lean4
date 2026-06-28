// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Diagnostics
// Imports: Lean.Meta.Diagnostics Lean.Meta.Tactic.Simp.Types
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_diagnostics_threshold, l_Lean_isDiagnosticsEnabled___redArg,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_isEmpty___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_setExporting,
};
use crate::r#gen::Lean::Expr::l_Lean_mkFVar;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Diagnostics::{
    initialize_Lean_Meta_Diagnostics, l_Lean_Meta_DiagSummary_isEmpty, l_Lean_Meta_appendSection,
    l_Lean_Meta_mkDiagSummary, runtime_initialize_Lean_Meta_Diagnostics,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::l_Lean_Meta_DiscrTree_keysAsPattern;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_Origin_key, l_Lean_Meta_Origin_lt___boxed, l_Lean_Meta_instInhabitedOrigin_default,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    initialize_Lean_Meta_Tactic_Simp_Types, runtime_initialize_Lean_Meta_Tactic_Simp_Types,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_crossEmoji;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_dec_eq, lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_5, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [32, 40, 98, 117, 105, 108, 116, 105, 110, 32, 115, 105, 109, 112, 114, 111, 99, 41, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0: u64 = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__1_value) as *mut LeanObject,13994041031692860867 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 166, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [44, 32, 115, 117, 99, 99, 101, 101, 100, 101, 100, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Origin_lt___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [44, 32, 107, 101, 121, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkDiagMessages___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_mkDiagMessages___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkDiagMessages___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_mkDiagMessages___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            117, 115, 101, 100, 32, 116, 104, 101, 111, 114, 101, 109, 115, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkDiagMessages___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_mkDiagMessages___closed__2_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            116, 114, 105, 101, 100, 32, 116, 104, 101, 111, 114, 101, 109, 115, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkDiagMessages___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_mkDiagMessages___closed__3_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            116, 114, 105, 101, 100, 32, 99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 116,
            104, 101, 111, 114, 101, 109, 115, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkDiagMessages___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_mkDiagMessages___closed__4_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            116, 104, 101, 111, 114, 101, 109, 115, 32, 119, 105, 116, 104, 32, 98, 97, 100, 32,
            107, 101, 121, 115, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkDiagMessages___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_mkDiagMessages___closed__5_value: LeanStringObject<89> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 89,
        m_capacity: 89,
        m_length: 88,
        m_data: [
            117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105,
            97, 103, 110, 111, 115, 116, 105, 99, 115, 46, 116, 104, 114, 101, 115, 104, 111, 108,
            100, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 99, 111, 110, 116, 114, 111, 108,
            32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 102, 111, 114, 32, 114, 101, 112,
            111, 114, 116, 105, 110, 103, 32, 99, 111, 117, 110, 116, 101, 114, 115, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkDiagMessages___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_mkDiagMessages___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_mkDiagMessages___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkDiagMessages___closed__6_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_mkDiagMessages___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_reportDiag___lam__0___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 0],
    };
static mut l_Lean_Meta_Simp_reportDiag___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_reportDiag___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_reportDiag___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_reportDiag___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_reportDiag___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_reportDiag___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_reportDiag___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_reportDiag___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    v___x_1930_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__0;
    v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(
    mut v_thmId_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1950_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1956_: u8 = 0;
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_thmId_1932_) {
                0 => {
                    v_declName_1935_ = lean_ctor_get(v_thmId_1932_, 0);
                    lean_inc_n(v_declName_1935_, 2);
                    lean_dec_ref_known(v_thmId_1932_, 1);
                    v___x_1936_ = lean_st_ref_get(v_a_1933_);
                    v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
                    lean_inc_ref(v_env_1937_);
                    lean_dec(v___x_1936_);
                    v___x_1938_ = 1;
                    v___x_1939_ =
                        l_Lean_Environment_contains(v_env_1937_, v_declName_1935_, v___x_1938_);
                    if v___x_1939_ == 0 {
                        v___x_1940_ = l_Lean_MessageData_ofName(v_declName_1935_);
                        v___x_1941_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1);
                        v___x_1942_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1942_, 0, v___x_1940_);
                        lean_ctor_set(v___x_1942_, 1, v___x_1941_);
                        v___x_1943_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1943_, 0, v___x_1942_);
                        return v___x_1943_;
                    } else {
                        v___x_1944_ = 0;
                        v___x_1945_ = l_Lean_MessageData_ofConstName(v_declName_1935_, v___x_1944_);
                        v___x_1946_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1946_, 0, v___x_1945_);
                        return v___x_1946_;
                    }
                }
                1 => {
                    v_fvarId_1947_ = lean_ctor_get(v_thmId_1932_, 0);
                    v_isSharedCheck_1956_ = (!lean_is_exclusive(v_thmId_1932_)) as u8;
                    if v_isSharedCheck_1956_ == 0 {
                        v___x_1949_ = v_thmId_1932_;
                        v_isShared_1950_ = v_isSharedCheck_1956_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_1947_);
                        lean_dec(v_thmId_1932_);
                        v___x_1949_ = lean_box(0);
                        v_isShared_1950_ = v_isSharedCheck_1956_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v___x_1957_ = l_Lean_Meta_Origin_key(v_thmId_1932_);
                    lean_dec_ref(v_thmId_1932_);
                    v___x_1958_ = l_Lean_MessageData_ofName(v___x_1957_);
                    v___x_1959_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1959_, 0, v___x_1958_);
                    return v___x_1959_;
                }
            },
            1 => {
                v___x_1951_ = l_Lean_mkFVar(v_fvarId_1947_);
                v___x_1952_ = l_Lean_MessageData_ofExpr(v___x_1951_);
                if v_isShared_1950_ == 0 {
                    lean_ctor_set_tag(v___x_1949_, 0);
                    lean_ctor_set(v___x_1949_, 0, v___x_1952_);
                    v___x_1954_ = v___x_1949_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
                    v___x_1954_ = v_reuseFailAlloc_1955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___boxed(
    mut v_thmId_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1963_: *mut LeanObject = core::ptr::null_mut();
    v_res_1963_ =
        l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(
            v_thmId_1960_,
            v_a_1961_,
        );
    lean_dec(v_a_1961_);
    return v_res_1963_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey(
    mut v_thmId_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
    mut v_a_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    v___x_1970_ =
        l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(
            v_thmId_1964_,
            v_a_1968_,
        );
    return v___x_1970_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___boxed(
    mut v_thmId_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_a_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1977_: *mut LeanObject = core::ptr::null_mut();
    v_res_1977_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey(
        v_thmId_1971_,
        v_a_1972_,
        v_a_1973_,
        v_a_1974_,
        v_a_1975_,
    );
    lean_dec(v_a_1975_);
    lean_dec_ref(v_a_1974_);
    lean_dec(v_a_1973_);
    lean_dec_ref(v_a_1972_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(
    mut v_opts_1978_: *mut LeanObject,
    mut v_opt_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    v_name_1980_ = lean_ctor_get(v_opt_1979_, 0);
    v_defValue_1981_ = lean_ctor_get(v_opt_1979_, 1);
    v_map_1982_ = lean_ctor_get(v_opts_1978_, 0);
    v___x_1983_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1982_,
            v_name_1980_,
        );
    if lean_obj_tag(v___x_1983_) == 0 {
        lean_inc(v_defValue_1981_);
        return v_defValue_1981_;
    } else {
        let mut v_val_1984_: *mut LeanObject = core::ptr::null_mut();
        v_val_1984_ = lean_ctor_get(v___x_1983_, 0);
        lean_inc(v_val_1984_);
        lean_dec_ref_known(v___x_1983_, 1);
        if lean_obj_tag(v_val_1984_) == 3 {
            let mut v_v_1985_: *mut LeanObject = core::ptr::null_mut();
            v_v_1985_ = lean_ctor_get(v_val_1984_, 0);
            lean_inc(v_v_1985_);
            lean_dec_ref_known(v_val_1984_, 1);
            return v_v_1985_;
        } else {
            lean_dec(v_val_1984_);
            lean_inc(v_defValue_1981_);
            return v_defValue_1981_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0___boxed(
    mut v_opts_1986_: *mut LeanObject,
    mut v_opt_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1988_: *mut LeanObject = core::ptr::null_mut();
    v_res_1988_ = l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(
        v_opts_1986_,
        v_opt_1987_,
    );
    lean_dec_ref(v_opt_1987_);
    lean_dec_ref(v_opts_1986_);
    return v_res_1988_;
}
pub unsafe fn l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0(mut v_x_1989_: *mut LeanObject) -> u8 {
    let mut v___x_1990_: u8 = 0;
    v___x_1990_ = 1;
    return v___x_1990_;
}
pub unsafe fn l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0___boxed(
    mut v_x_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1992_: u8 = 0;
    let mut v_r_1993_: *mut LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0(v_x_1991_);
    lean_dec_ref(v_x_1991_);
    v_r_1993_ = lean_box((v_res_1992_) as usize);
    return v_r_1993_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___lam__0(
    mut v_f_1994_: *mut LeanObject,
    mut v_s_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
    mut v_b_1997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_a_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1998_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1998_, 0, v_a_1996_);
                lean_ctor_set(v___x_1998_, 1, v_b_1997_);
                v___x_1999_ = lean_apply_2(v_f_1994_, v___x_1998_, v_s_1995_);
                if lean_obj_tag(v___x_1999_) == 0 {
                    v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
                    v_isSharedCheck_2007_ = (!lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2007_ == 0 {
                        v___x_2002_ = v___x_1999_;
                        v_isShared_2003_ = v_isSharedCheck_2007_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2000_);
                        lean_dec(v___x_1999_);
                        v___x_2002_ = lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2007_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2008_ = lean_ctor_get(v___x_1999_, 0);
                    v_isSharedCheck_2015_ = (!lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2015_ == 0 {
                        v___x_2010_ = v___x_1999_;
                        v_isShared_2011_ = v_isSharedCheck_2015_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2008_);
                        lean_dec(v___x_1999_);
                        v___x_2010_ = lean_box(0);
                        v_isShared_2011_ = v_isSharedCheck_2015_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2003_ == 0 {
                    v___x_2005_ = v___x_2002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
                    v___x_2005_ = v_reuseFailAlloc_2006_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2005_;
            }
            3 => {
                if v_isShared_2011_ == 0 {
                    v___x_2013_ = v___x_2010_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
                    v___x_2013_ = v_reuseFailAlloc_2014_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(
    mut v_f_2016_: *mut LeanObject,
    mut v_keys_2017_: *mut LeanObject,
    mut v_vals_2018_: *mut LeanObject,
    mut v_i_2019_: *mut LeanObject,
    mut v_acc_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2021_ = lean_array_get_size(v_keys_2017_);
                v___x_2022_ = lean_nat_dec_lt(v_i_2019_, v___x_2021_);
                if v___x_2022_ == 0 {
                    lean_dec(v_i_2019_);
                    lean_dec_ref(v_f_2016_);
                    v___x_2023_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2023_, 0, v_acc_2020_);
                    return v___x_2023_;
                } else {
                    v_k_2024_ = lean_array_fget_borrowed(v_keys_2017_, v_i_2019_);
                    v_v_2025_ = lean_array_fget_borrowed(v_vals_2018_, v_i_2019_);
                    lean_inc_ref(v_f_2016_);
                    lean_inc(v_v_2025_);
                    lean_inc(v_k_2024_);
                    v___x_2026_ = lean_apply_3(v_f_2016_, v_acc_2020_, v_k_2024_, v_v_2025_);
                    if lean_obj_tag(v___x_2026_) == 0 {
                        lean_dec(v_i_2019_);
                        lean_dec_ref(v_f_2016_);
                        return v___x_2026_;
                    } else {
                        v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
                        lean_inc(v_a_2027_);
                        lean_dec_ref_known(v___x_2026_, 1);
                        v___x_2028_ = lean_unsigned_to_nat(1);
                        v___x_2029_ = lean_nat_add(v_i_2019_, v___x_2028_);
                        lean_dec(v_i_2019_);
                        v_i_2019_ = v___x_2029_;
                        v_acc_2020_ = v_a_2027_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg___boxed(
    mut v_f_2031_: *mut LeanObject,
    mut v_keys_2032_: *mut LeanObject,
    mut v_vals_2033_: *mut LeanObject,
    mut v_i_2034_: *mut LeanObject,
    mut v_acc_2035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2036_: *mut LeanObject = core::ptr::null_mut();
    v_res_2036_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_2031_, v_keys_2032_, v_vals_2033_, v_i_2034_, v_acc_2035_);
    lean_dec_ref(v_vals_2033_);
    lean_dec_ref(v_keys_2032_);
    return v_res_2036_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(
    mut v_f_2037_: *mut LeanObject,
    mut v_x_2038_: *mut LeanObject,
    mut v_x_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: usize = 0;
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: usize = 0;
    let mut v___x_2058_: usize = 0;
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2060_: u8 = 0;
    let mut v_ks_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2038_) == 0 {
                    v_es_2040_ = lean_ctor_get(v_x_2038_, 0);
                    v_isSharedCheck_2060_ = (!lean_is_exclusive(v_x_2038_)) as u8;
                    if v_isSharedCheck_2060_ == 0 {
                        v___x_2042_ = v_x_2038_;
                        v_isShared_2043_ = v_isSharedCheck_2060_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_2040_);
                        lean_dec(v_x_2038_);
                        v___x_2042_ = lean_box(0);
                        v_isShared_2043_ = v_isSharedCheck_2060_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_2061_ = lean_ctor_get(v_x_2038_, 0);
                    lean_inc_ref(v_ks_2061_);
                    v_vs_2062_ = lean_ctor_get(v_x_2038_, 1);
                    lean_inc_ref(v_vs_2062_);
                    lean_dec_ref_known(v_x_2038_, 2);
                    v___x_2063_ = lean_unsigned_to_nat(0);
                    v___x_2064_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_2037_, v_ks_2061_, v_vs_2062_, v___x_2063_, v_x_2039_);
                    lean_dec_ref(v_vs_2062_);
                    lean_dec_ref(v_ks_2061_);
                    return v___x_2064_;
                }
            }
            1 => {
                v___x_2044_ = lean_unsigned_to_nat(0);
                v___x_2045_ = lean_array_get_size(v_es_2040_);
                v___x_2046_ = lean_nat_dec_lt(v___x_2044_, v___x_2045_);
                if v___x_2046_ == 0 {
                    lean_dec_ref(v_es_2040_);
                    lean_dec_ref(v_f_2037_);
                    if v_isShared_2043_ == 0 {
                        lean_ctor_set_tag(v___x_2042_, 1);
                        lean_ctor_set(v___x_2042_, 0, v_x_2039_);
                        v___x_2048_ = v___x_2042_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_x_2039_);
                        v___x_2048_ = v_reuseFailAlloc_2049_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2050_ = lean_nat_dec_le(v___x_2045_, v___x_2045_);
                    if v___x_2050_ == 0 {
                        if v___x_2046_ == 0 {
                            lean_dec_ref(v_es_2040_);
                            lean_dec_ref(v_f_2037_);
                            if v_isShared_2043_ == 0 {
                                lean_ctor_set_tag(v___x_2042_, 1);
                                lean_ctor_set(v___x_2042_, 0, v_x_2039_);
                                v___x_2052_ = v___x_2042_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_x_2039_);
                                v___x_2052_ = v_reuseFailAlloc_2053_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2042_);
                            v___x_2054_ = 0usize;
                            v___x_2055_ = lean_usize_of_nat(v___x_2045_);
                            v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_2037_, v_es_2040_, v___x_2054_, v___x_2055_, v_x_2039_);
                            lean_dec_ref(v_es_2040_);
                            return v___x_2056_;
                        }
                    } else {
                        lean_del_object(v___x_2042_);
                        v___x_2057_ = 0usize;
                        v___x_2058_ = lean_usize_of_nat(v___x_2045_);
                        v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_2037_, v_es_2040_, v___x_2057_, v___x_2058_, v_x_2039_);
                        lean_dec_ref(v_es_2040_);
                        return v___x_2059_;
                    }
                }
            }
            2 => {
                return v___x_2048_;
            }
            3 => {
                return v___x_2052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(
    mut v_f_2065_: *mut LeanObject,
    mut v_as_2066_: *mut LeanObject,
    mut v_i_2067_: usize,
    mut v_stop_2068_: usize,
    mut v_b_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: usize = 0;
    let mut v___x_2073_: usize = 0;
    let mut v___y_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2078_ = lean_usize_dec_eq(v_i_2067_, v_stop_2068_);
                if v___x_2078_ == 0 {
                    v___x_2079_ = lean_array_uget_borrowed(v_as_2066_, v_i_2067_);
                    match lean_obj_tag(v___x_2079_) {
                        0 => {
                            v_key_2080_ = lean_ctor_get(v___x_2079_, 0);
                            v_val_2081_ = lean_ctor_get(v___x_2079_, 1);
                            lean_inc_ref(v_f_2065_);
                            lean_inc(v_val_2081_);
                            lean_inc(v_key_2080_);
                            v___x_2082_ =
                                lean_apply_3(v_f_2065_, v_b_2069_, v_key_2080_, v_val_2081_);
                            v___y_2076_ = v___x_2082_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_2083_ = lean_ctor_get(v___x_2079_, 0);
                            lean_inc(v_node_2083_);
                            lean_inc_ref(v_f_2065_);
                            v___x_2084_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_2065_, v_node_2083_, v_b_2069_);
                            v___y_2076_ = v___x_2084_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_2071_ = v_b_2069_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_2065_);
                    v___x_2085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2085_, 0, v_b_2069_);
                    return v___x_2085_;
                }
            }
            1 => {
                v___x_2072_ = 1usize;
                v___x_2073_ = lean_usize_add(v_i_2067_, v___x_2072_);
                v_i_2067_ = v___x_2073_;
                v_b_2069_ = v_a_2071_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_2076_) == 0 {
                    lean_dec_ref(v_f_2065_);
                    return v___y_2076_;
                } else {
                    v_a_2077_ = lean_ctor_get(v___y_2076_, 0);
                    lean_inc(v_a_2077_);
                    lean_dec_ref_known(v___y_2076_, 1);
                    v_a_2071_ = v_a_2077_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_f_2086_: *mut LeanObject,
    mut v_as_2087_: *mut LeanObject,
    mut v_i_2088_: *mut LeanObject,
    mut v_stop_2089_: *mut LeanObject,
    mut v_b_2090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2091_: usize = 0;
    let mut v_stop_boxed_2092_: usize = 0;
    let mut v_res_2093_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2091_ = lean_unbox_usize(v_i_2088_);
    lean_dec(v_i_2088_);
    v_stop_boxed_2092_ = lean_unbox_usize(v_stop_2089_);
    lean_dec(v_stop_2089_);
    v_res_2093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_2086_, v_as_2087_, v_i_boxed_2091_, v_stop_boxed_2092_, v_b_2090_);
    lean_dec_ref(v_as_2087_);
    return v_res_2093_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(
    mut v_map_2094_: *mut LeanObject,
    mut v_init_2095_: *mut LeanObject,
    mut v_f_2096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2099_: *mut LeanObject = core::ptr::null_mut();
    v___f_2097_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_2097_, 0, v_f_2096_);
    lean_inc_ref(v_map_2094_);
    v___x_2098_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v___f_2097_, v_map_2094_, v_init_2095_);
    v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
    lean_inc(v_a_2099_);
    lean_dec_ref(v___x_2098_);
    return v_a_2099_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___boxed(
    mut v_map_2100_: *mut LeanObject,
    mut v_init_2101_: *mut LeanObject,
    mut v_f_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2103_: *mut LeanObject = core::ptr::null_mut();
    v_res_2103_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_map_2100_, v_init_2101_, v_f_2102_);
    lean_dec_ref(v_map_2100_);
    return v_res_2103_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(
    mut v_lt_2104_: *mut LeanObject,
    mut v_x_2105_: *mut LeanObject,
    mut v_x_2106_: *mut LeanObject,
) -> u8 {
    let mut v_fst_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: u8 = 0;
    v_fst_2107_ = lean_ctor_get(v_x_2105_, 0);
    lean_inc(v_fst_2107_);
    v_snd_2108_ = lean_ctor_get(v_x_2105_, 1);
    lean_inc(v_snd_2108_);
    lean_dec_ref(v_x_2105_);
    v_fst_2109_ = lean_ctor_get(v_x_2106_, 0);
    lean_inc(v_fst_2109_);
    v_snd_2110_ = lean_ctor_get(v_x_2106_, 1);
    lean_inc(v_snd_2110_);
    lean_dec_ref(v_x_2106_);
    v___x_2111_ = lean_nat_dec_eq(v_snd_2108_, v_snd_2110_);
    if v___x_2111_ == 0 {
        let mut v___x_2112_: u8 = 0;
        lean_dec(v_fst_2109_);
        lean_dec(v_fst_2107_);
        lean_dec_ref(v_lt_2104_);
        v___x_2112_ = lean_nat_dec_lt(v_snd_2110_, v_snd_2108_);
        lean_dec(v_snd_2108_);
        lean_dec(v_snd_2110_);
        return v___x_2112_;
    } else {
        let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: u8 = 0;
        lean_dec(v_snd_2110_);
        lean_dec(v_snd_2108_);
        v___x_2113_ = lean_apply_2(v_lt_2104_, v_fst_2107_, v_fst_2109_);
        v___x_2114_ = (lean_unbox(v___x_2113_) as u8);
        return v___x_2114_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0___boxed(
    mut v_lt_2115_: *mut LeanObject,
    mut v_x_2116_: *mut LeanObject,
    mut v_x_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2118_: u8 = 0;
    let mut v_r_2119_: *mut LeanObject = core::ptr::null_mut();
    v_res_2118_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_2115_, v_x_2116_, v_x_2117_);
    v_r_2119_ = lean_box((v_res_2118_) as usize);
    return v_r_2119_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(
    mut v_lt_2120_: *mut LeanObject,
    mut v_hi_2121_: *mut LeanObject,
    mut v_pivot_2122_: *mut LeanObject,
    mut v_as_2123_: *mut LeanObject,
    mut v_i_2124_: *mut LeanObject,
    mut v_k_2125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2127_: u8 = 0;
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: u8 = 0;
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2136_ = lean_nat_dec_lt(v_k_2125_, v_hi_2121_);
                if v___x_2136_ == 0 {
                    lean_dec(v_k_2125_);
                    lean_dec_ref(v_pivot_2122_);
                    lean_dec_ref(v_lt_2120_);
                    v___x_2137_ = lean_array_fswap(v_as_2123_, v_i_2124_, v_hi_2121_);
                    v___x_2138_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2138_, 0, v_i_2124_);
                    lean_ctor_set(v___x_2138_, 1, v___x_2137_);
                    return v___x_2138_;
                } else {
                    v___x_2139_ = lean_array_fget_borrowed(v_as_2123_, v_k_2125_);
                    v_fst_2140_ = lean_ctor_get(v___x_2139_, 0);
                    v_snd_2141_ = lean_ctor_get(v___x_2139_, 1);
                    v_fst_2142_ = lean_ctor_get(v_pivot_2122_, 0);
                    v_snd_2143_ = lean_ctor_get(v_pivot_2122_, 1);
                    v___x_2144_ = lean_nat_dec_eq(v_snd_2141_, v_snd_2143_);
                    if v___x_2144_ == 0 {
                        v___x_2145_ = lean_nat_dec_lt(v_snd_2143_, v_snd_2141_);
                        v___y_2127_ = v___x_2145_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v_lt_2120_);
                        lean_inc(v_fst_2142_);
                        lean_inc(v_fst_2140_);
                        v___x_2146_ = lean_apply_2(v_lt_2120_, v_fst_2140_, v_fst_2142_);
                        v___x_2147_ = (lean_unbox(v___x_2146_) as u8);
                        v___y_2127_ = v___x_2147_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2127_ == 0 {
                    v___x_2128_ = lean_unsigned_to_nat(1);
                    v___x_2129_ = lean_nat_add(v_k_2125_, v___x_2128_);
                    lean_dec(v_k_2125_);
                    v_k_2125_ = v___x_2129_;
                    state = 0;
                    continue;
                } else {
                    v___x_2131_ = lean_array_fswap(v_as_2123_, v_i_2124_, v_k_2125_);
                    v___x_2132_ = lean_unsigned_to_nat(1);
                    v___x_2133_ = lean_nat_add(v_i_2124_, v___x_2132_);
                    lean_dec(v_i_2124_);
                    v___x_2134_ = lean_nat_add(v_k_2125_, v___x_2132_);
                    lean_dec(v_k_2125_);
                    v_as_2123_ = v___x_2131_;
                    v_i_2124_ = v___x_2133_;
                    v_k_2125_ = v___x_2134_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_lt_2148_: *mut LeanObject,
    mut v_hi_2149_: *mut LeanObject,
    mut v_pivot_2150_: *mut LeanObject,
    mut v_as_2151_: *mut LeanObject,
    mut v_i_2152_: *mut LeanObject,
    mut v_k_2153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2154_: *mut LeanObject = core::ptr::null_mut();
    v_res_2154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_2148_, v_hi_2149_, v_pivot_2150_, v_as_2151_, v_i_2152_, v_k_2153_);
    lean_dec(v_hi_2149_);
    return v_res_2154_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(
    mut v_lt_2155_: *mut LeanObject,
    mut v_n_2156_: *mut LeanObject,
    mut v_as_2157_: *mut LeanObject,
    mut v_lo_2158_: *mut LeanObject,
    mut v_hi_2159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2171_ = lean_nat_dec_lt(v_lo_2158_, v_hi_2159_);
                if v___x_2171_ == 0 {
                    lean_dec(v_lo_2158_);
                    lean_dec_ref(v_lt_2155_);
                    return v_as_2157_;
                } else {
                    v___x_2172_ = lean_nat_add(v_lo_2158_, v_hi_2159_);
                    v___x_2173_ = lean_unsigned_to_nat(1);
                    v_mid_2174_ = lean_nat_shiftr(v___x_2172_, v___x_2173_);
                    lean_dec(v___x_2172_);
                    v___x_2187_ = lean_array_fget_borrowed(v_as_2157_, v_mid_2174_);
                    v___x_2188_ = lean_array_fget_borrowed(v_as_2157_, v_lo_2158_);
                    lean_inc(v___x_2188_);
                    lean_inc(v___x_2187_);
                    lean_inc_ref(v_lt_2155_);
                    v___x_2189_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_2155_, v___x_2187_, v___x_2188_);
                    if v___x_2189_ == 0 {
                        v___y_2182_ = v_as_2157_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2190_ = lean_array_fswap(v_as_2157_, v_lo_2158_, v_mid_2174_);
                        v___y_2182_ = v___x_2190_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2162_ = lean_array_fget(v___y_2161_, v_hi_2159_);
                lean_inc_n(v_lo_2158_, 2);
                lean_inc_ref(v_lt_2155_);
                v___x_2163_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_2155_, v_hi_2159_, v_pivot_2162_, v___y_2161_, v_lo_2158_, v_lo_2158_);
                v_fst_2164_ = lean_ctor_get(v___x_2163_, 0);
                lean_inc(v_fst_2164_);
                v_snd_2165_ = lean_ctor_get(v___x_2163_, 1);
                lean_inc(v_snd_2165_);
                lean_dec_ref(v___x_2163_);
                v___x_2166_ = lean_nat_dec_le(v_hi_2159_, v_fst_2164_);
                if v___x_2166_ == 0 {
                    lean_inc_ref(v_lt_2155_);
                    v___x_2167_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_2155_, v_n_2156_, v_snd_2165_, v_lo_2158_, v_fst_2164_);
                    v___x_2168_ = lean_unsigned_to_nat(1);
                    v___x_2169_ = lean_nat_add(v_fst_2164_, v___x_2168_);
                    lean_dec(v_fst_2164_);
                    v_as_2157_ = v___x_2167_;
                    v_lo_2158_ = v___x_2169_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_2164_);
                    lean_dec(v_lo_2158_);
                    lean_dec_ref(v_lt_2155_);
                    return v_snd_2165_;
                }
            }
            2 => {
                v___x_2177_ = lean_array_fget_borrowed(v___y_2176_, v_mid_2174_);
                v___x_2178_ = lean_array_fget_borrowed(v___y_2176_, v_hi_2159_);
                lean_inc(v___x_2178_);
                lean_inc(v___x_2177_);
                lean_inc_ref(v_lt_2155_);
                v___x_2179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_2155_, v___x_2177_, v___x_2178_);
                if v___x_2179_ == 0 {
                    lean_dec(v_mid_2174_);
                    v___y_2161_ = v___y_2176_;
                    state = 1;
                    continue;
                } else {
                    v___x_2180_ = lean_array_fswap(v___y_2176_, v_mid_2174_, v_hi_2159_);
                    lean_dec(v_mid_2174_);
                    v___y_2161_ = v___x_2180_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2183_ = lean_array_fget_borrowed(v___y_2182_, v_hi_2159_);
                v___x_2184_ = lean_array_fget_borrowed(v___y_2182_, v_lo_2158_);
                lean_inc(v___x_2184_);
                lean_inc(v___x_2183_);
                lean_inc_ref(v_lt_2155_);
                v___x_2185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_2155_, v___x_2183_, v___x_2184_);
                if v___x_2185_ == 0 {
                    v___y_2176_ = v___y_2182_;
                    state = 2;
                    continue;
                } else {
                    v___x_2186_ = lean_array_fswap(v___y_2182_, v_lo_2158_, v_hi_2159_);
                    v___y_2176_ = v___x_2186_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___boxed(
    mut v_lt_2191_: *mut LeanObject,
    mut v_n_2192_: *mut LeanObject,
    mut v_as_2193_: *mut LeanObject,
    mut v_lo_2194_: *mut LeanObject,
    mut v_hi_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2196_: *mut LeanObject = core::ptr::null_mut();
    v_res_2196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_2191_, v_n_2192_, v_as_2193_, v_lo_2194_, v_hi_2195_);
    lean_dec(v_hi_2195_);
    lean_dec(v_n_2192_);
    return v_res_2196_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(
    mut v_threshold_2197_: *mut LeanObject,
    mut v_p_2198_: *mut LeanObject,
    mut v_x_2199_: *mut LeanObject,
    mut v_____s_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    v_fst_2201_ = lean_ctor_get(v_x_2199_, 0);
    v_snd_2202_ = lean_ctor_get(v_x_2199_, 1);
    v___x_2203_ = lean_nat_dec_lt(v_threshold_2197_, v_snd_2202_);
    if v___x_2203_ == 0 {
        let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_x_2199_);
        lean_dec_ref(v_p_2198_);
        v___x_2204_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2204_, 0, v_____s_2200_);
        return v___x_2204_;
    } else {
        let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2206_: u8 = 0;
        lean_inc(v_fst_2201_);
        v___x_2205_ = lean_apply_1(v_p_2198_, v_fst_2201_);
        v___x_2206_ = (lean_unbox(v___x_2205_) as u8);
        if v___x_2206_ == 0 {
            let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_x_2199_);
            v___x_2207_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_2207_, 0, v_____s_2200_);
            return v___x_2207_;
        } else {
            let mut v_r_2208_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
            v_r_2208_ = lean_array_push(v_____s_2200_, v_x_2199_);
            v___x_2209_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_2209_, 0, v_r_2208_);
            return v___x_2209_;
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed(
    mut v_threshold_2210_: *mut LeanObject,
    mut v_p_2211_: *mut LeanObject,
    mut v_x_2212_: *mut LeanObject,
    mut v_____s_2213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2214_: *mut LeanObject = core::ptr::null_mut();
    v_res_2214_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(v_threshold_2210_, v_p_2211_, v_x_2212_, v_____s_2213_);
    lean_dec(v_threshold_2210_);
    return v_res_2214_;
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(
    mut v_counters_2217_: *mut LeanObject,
    mut v_threshold_2218_: *mut LeanObject,
    mut v_p_2219_: *mut LeanObject,
    mut v_lt_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2221_ = lean_alloc_closure(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_2221_, 0, v_threshold_2218_);
                lean_closure_set(v___f_2221_, 1, v_p_2219_);
                v___x_2222_ = lean_unsigned_to_nat(0);
                v_r_2223_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0;
                v___x_2224_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_counters_2217_, v_r_2223_, v___f_2221_);
                v___x_2225_ = lean_array_get_size(v___x_2224_);
                v___x_2226_ = lean_nat_dec_eq(v___x_2225_, v___x_2222_);
                if v___x_2226_ == 0 {
                    v___x_2227_ = lean_unsigned_to_nat(1);
                    v___x_2228_ = lean_nat_sub(v___x_2225_, v___x_2227_);
                    v___x_2234_ = lean_nat_dec_le(v___x_2222_, v___x_2228_);
                    if v___x_2234_ == 0 {
                        lean_inc(v___x_2228_);
                        v___y_2230_ = v___x_2228_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2230_ = v___x_2222_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_lt_2220_);
                    return v___x_2224_;
                }
            }
            1 => {
                v___x_2231_ = lean_nat_dec_le(v___y_2230_, v___x_2228_);
                if v___x_2231_ == 0 {
                    lean_dec(v___x_2228_);
                    lean_inc(v___y_2230_);
                    v___x_2232_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_2220_, v___x_2225_, v___x_2224_, v___y_2230_, v___y_2230_);
                    lean_dec(v___y_2230_);
                    return v___x_2232_;
                } else {
                    v___x_2233_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_2220_, v___x_2225_, v___x_2224_, v___y_2230_, v___x_2228_);
                    lean_dec(v___x_2228_);
                    return v___x_2233_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___boxed(
    mut v_counters_2235_: *mut LeanObject,
    mut v_threshold_2236_: *mut LeanObject,
    mut v_p_2237_: *mut LeanObject,
    mut v_lt_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2239_: *mut LeanObject = core::ptr::null_mut();
    v_res_2239_ =
        l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(
            v_counters_2235_,
            v_threshold_2236_,
            v_p_2237_,
            v_lt_2238_,
        );
    lean_dec_ref(v_counters_2235_);
    return v_res_2239_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(
    mut v_keys_2240_: *mut LeanObject,
    mut v_vals_2241_: *mut LeanObject,
    mut v_i_2242_: *mut LeanObject,
    mut v_k_2243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: u8 = 0;
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inv_2257_: u8 = 0;
    let mut v_declName_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inv_2259_: u8 = 0;
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2252_ = lean_array_get_size(v_keys_2240_);
                v___x_2253_ = lean_nat_dec_lt(v_i_2242_, v___x_2252_);
                if v___x_2253_ == 0 {
                    lean_dec(v_i_2242_);
                    v___x_2254_ = lean_box(0);
                    return v___x_2254_;
                } else {
                    v_k_x27_2255_ = lean_array_fget_borrowed(v_keys_2240_, v_i_2242_);
                    if lean_obj_tag(v_k_2243_) == 0 {
                        if lean_obj_tag(v_k_x27_2255_) == 0 {
                            v_declName_2256_ = lean_ctor_get(v_k_2243_, 0);
                            v_inv_2257_ = lean_ctor_get_uint8(
                                v_k_2243_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                            );
                            v_declName_2258_ = lean_ctor_get(v_k_x27_2255_, 0);
                            v_inv_2259_ = lean_ctor_get_uint8(
                                v_k_x27_2255_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                            );
                            v___x_2260_ = lean_name_eq(v_declName_2256_, v_declName_2258_);
                            if v___x_2260_ == 0 {
                                v___y_2249_ = v___x_2260_;
                                state = 2;
                                continue;
                            } else {
                                if v_inv_2257_ == 0 {
                                    if v_inv_2259_ == 0 {
                                        v___y_2249_ = v___x_2260_;
                                        state = 2;
                                        continue;
                                    } else {
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_2249_ = v_inv_2259_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_k_x27_2255_) == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_2261_ = l_Lean_Meta_Origin_key(v_k_2243_);
                            v___x_2262_ = l_Lean_Meta_Origin_key(v_k_x27_2255_);
                            v___x_2263_ = lean_name_eq(v___x_2261_, v___x_2262_);
                            lean_dec(v___x_2262_);
                            lean_dec(v___x_2261_);
                            v___y_2249_ = v___x_2263_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2245_ = lean_unsigned_to_nat(1);
                v___x_2246_ = lean_nat_add(v_i_2242_, v___x_2245_);
                lean_dec(v_i_2242_);
                v_i_2242_ = v___x_2246_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2249_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_2250_ = lean_array_fget_borrowed(v_vals_2241_, v_i_2242_);
                    lean_dec(v_i_2242_);
                    lean_inc(v___x_2250_);
                    v___x_2251_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                    return v___x_2251_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_keys_2264_: *mut LeanObject,
    mut v_vals_2265_: *mut LeanObject,
    mut v_i_2266_: *mut LeanObject,
    mut v_k_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2268_: *mut LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_keys_2264_, v_vals_2265_, v_i_2266_, v_k_2267_);
    lean_dec_ref(v_k_2267_);
    lean_dec_ref(v_vals_2265_);
    lean_dec_ref(v_keys_2264_);
    return v_res_2268_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_2269_: usize = 0;
    let mut v___x_2270_: usize = 0;
    let mut v___x_2271_: usize = 0;
    v___x_2269_ = 5usize;
    v___x_2270_ = 1usize;
    v___x_2271_ = lean_usize_shift_left(v___x_2270_, v___x_2269_);
    return v___x_2271_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: usize = 0;
    let mut v___x_2274_: usize = 0;
    v___x_2272_ = 1usize;
    v___x_2273_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__0);
    v___x_2274_ = lean_usize_sub(v___x_2273_, v___x_2272_);
    return v___x_2274_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(
    mut v_x_2275_: *mut LeanObject,
    mut v_x_2276_: usize,
    mut v_x_2277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: usize = 0;
    let mut v___x_2281_: usize = 0;
    let mut v___x_2282_: usize = 0;
    let mut v_j_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2288_: u8 = 0;
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inv_2292_: u8 = 0;
    let mut v_declName_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inv_2294_: u8 = 0;
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: u8 = 0;
    let mut v_node_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: usize = 0;
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2275_) == 0 {
                    v_es_2278_ = lean_ctor_get(v_x_2275_, 0);
                    v___x_2279_ = lean_box(2);
                    v___x_2280_ = 5usize;
                    v___x_2281_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___closed__1);
                    v___x_2282_ = lean_usize_land(v_x_2276_, v___x_2281_);
                    v_j_2283_ = lean_usize_to_nat(v___x_2282_);
                    v___x_2284_ = lean_array_get_borrowed(v___x_2279_, v_es_2278_, v_j_2283_);
                    lean_dec(v_j_2283_);
                    match lean_obj_tag(v___x_2284_) {
                        0 => {
                            v_key_2285_ = lean_ctor_get(v___x_2284_, 0);
                            v_val_2286_ = lean_ctor_get(v___x_2284_, 1);
                            if lean_obj_tag(v_x_2277_) == 0 {
                                if lean_obj_tag(v_key_2285_) == 0 {
                                    v_declName_2291_ = lean_ctor_get(v_x_2277_, 0);
                                    v_inv_2292_ = lean_ctor_get_uint8(
                                        v_x_2277_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                    );
                                    v_declName_2293_ = lean_ctor_get(v_key_2285_, 0);
                                    v_inv_2294_ = lean_ctor_get_uint8(
                                        v_key_2285_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                    );
                                    v___x_2295_ = lean_name_eq(v_declName_2291_, v_declName_2293_);
                                    if v___x_2295_ == 0 {
                                        v___y_2288_ = v___x_2295_;
                                        state = 1;
                                        continue;
                                    } else {
                                        if v_inv_2292_ == 0 {
                                            if v_inv_2294_ == 0 {
                                                v___y_2288_ = v___x_2295_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_2296_ = lean_box(0);
                                                return v___x_2296_;
                                            }
                                        } else {
                                            v___y_2288_ = v_inv_2294_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_2297_ = lean_box(0);
                                    return v___x_2297_;
                                }
                            } else {
                                if lean_obj_tag(v_key_2285_) == 0 {
                                    v___x_2298_ = lean_box(0);
                                    return v___x_2298_;
                                } else {
                                    v___x_2299_ = l_Lean_Meta_Origin_key(v_x_2277_);
                                    v___x_2300_ = l_Lean_Meta_Origin_key(v_key_2285_);
                                    v___x_2301_ = lean_name_eq(v___x_2299_, v___x_2300_);
                                    lean_dec(v___x_2300_);
                                    lean_dec(v___x_2299_);
                                    v___y_2288_ = v___x_2301_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_node_2302_ = lean_ctor_get(v___x_2284_, 0);
                            v___x_2303_ = lean_usize_shift_right(v_x_2276_, v___x_2280_);
                            v_x_2275_ = v_node_2302_;
                            v_x_2276_ = v___x_2303_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2305_ = lean_box(0);
                            return v___x_2305_;
                        }
                    }
                } else {
                    v_ks_2306_ = lean_ctor_get(v_x_2275_, 0);
                    v_vs_2307_ = lean_ctor_get(v_x_2275_, 1);
                    v___x_2308_ = lean_unsigned_to_nat(0);
                    v___x_2309_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_ks_2306_, v_vs_2307_, v___x_2308_, v_x_2277_);
                    return v___x_2309_;
                }
            }
            1 => {
                if v___y_2288_ == 0 {
                    v___x_2289_ = lean_box(0);
                    return v___x_2289_;
                } else {
                    lean_inc(v_val_2286_);
                    v___x_2290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2290_, 0, v_val_2286_);
                    return v___x_2290_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___boxed(
    mut v_x_2310_: *mut LeanObject,
    mut v_x_2311_: *mut LeanObject,
    mut v_x_2312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4647__boxed_2313_: usize = 0;
    let mut v_res_2314_: *mut LeanObject = core::ptr::null_mut();
    v_x_4647__boxed_2313_ = lean_unbox_usize(v_x_2311_);
    lean_dec(v_x_2311_);
    v_res_2314_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_2310_, v_x_4647__boxed_2313_, v_x_2312_);
    lean_dec_ref(v_x_2312_);
    lean_dec_ref(v_x_2310_);
    return v_res_2314_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u64 = 0;
    v___x_2315_ = lean_unsigned_to_nat(1723);
    v___x_2316_ = lean_uint64_of_nat(v___x_2315_);
    return v___x_2316_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(
    mut v_x_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2320_: u64 = 0;
    let mut v___x_2321_: usize = 0;
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: u64 = 0;
    let mut v___x_2325_: u64 = 0;
    let mut v___x_2326_: u64 = 0;
    let mut v___y_2328_: u64 = 0;
    let mut v___x_2329_: u64 = 0;
    let mut v___x_2330_: u64 = 0;
    let mut v_inv_2331_: u8 = 0;
    let mut v_declName_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: u64 = 0;
    let mut v_hash_2334_: u64 = 0;
    let mut v_declName_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u64 = 0;
    let mut v_hash_2337_: u64 = 0;
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u64 = 0;
    let mut v_hash_2340_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2318_) == 0 {
                    v_inv_2331_ = lean_ctor_get_uint8(
                        v_x_2318_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    if v_inv_2331_ == 0 {
                        v_declName_2332_ = lean_ctor_get(v_x_2318_, 0);
                        if lean_obj_tag(v_declName_2332_) == 0 {
                            v___x_2333_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0);
                            v___y_2324_ = v___x_2333_;
                            state = 2;
                            continue;
                        } else {
                            v_hash_2334_ = lean_ctor_get_uint64(
                                v_declName_2332_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            );
                            v___y_2324_ = v_hash_2334_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_declName_2335_ = lean_ctor_get(v_x_2318_, 0);
                        if lean_obj_tag(v_declName_2335_) == 0 {
                            v___x_2336_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0);
                            v___y_2328_ = v___x_2336_;
                            state = 3;
                            continue;
                        } else {
                            v_hash_2337_ = lean_ctor_get_uint64(
                                v_declName_2335_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            );
                            v___y_2328_ = v_hash_2337_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_2338_ = l_Lean_Meta_Origin_key(v_x_2318_);
                    if lean_obj_tag(v___x_2338_) == 0 {
                        v___x_2339_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___closed__0);
                        v___y_2320_ = v___x_2339_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2340_ = lean_ctor_get_uint64(
                            v___x_2338_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        lean_dec(v___x_2338_);
                        v___y_2320_ = v_hash_2340_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2321_ = lean_uint64_to_usize(v___y_2320_);
                v___x_2322_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_2317_, v___x_2321_, v_x_2318_);
                return v___x_2322_;
            }
            2 => {
                v___x_2325_ = 13u64;
                v___x_2326_ = lean_uint64_mix_hash(v___y_2324_, v___x_2325_);
                v___y_2320_ = v___x_2326_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2329_ = 11u64;
                v___x_2330_ = lean_uint64_mix_hash(v___y_2328_, v___x_2329_);
                v___y_2320_ = v___x_2330_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___boxed(
    mut v_x_2341_: *mut LeanObject,
    mut v_x_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2343_: *mut LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_x_2341_, v_x_2342_);
    lean_dec_ref(v_x_2342_);
    lean_dec_ref(v_x_2341_);
    return v_res_2343_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3()
-> f64 {
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: f64 = 0.0;
    v___x_2349_ = lean_unsigned_to_nat(0);
    v___x_2350_ = lean_float_of_nat(v___x_2349_);
    return v___x_2350_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5;
    v___x_2354_ = l_Lean_stringToMessageData(v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    v___x_2357_ = l_Lean_crossEmoji;
    v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8;
    v___x_2359_ = lean_string_append(v___x_2358_, v___x_2357_);
    return v___x_2359_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(
    mut v_usedCounters_x3f_2360_: *mut LeanObject,
    mut v_as_2361_: *mut LeanObject,
    mut v_sz_2362_: usize,
    mut v_i_2363_: usize,
    mut v_b_2364_: *mut LeanObject,
    mut v___y_2365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedMsg_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: f64 = 0.0;
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: usize = 0;
    let mut v___x_2397_: usize = 0;
    let mut v_reuseFailAlloc_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2411_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2367_ = lean_usize_dec_lt(v_i_2363_, v_sz_2362_);
                if v___x_2367_ == 0 {
                    v___x_2368_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2368_, 0, v_b_2364_);
                    return v___x_2368_;
                } else {
                    v_a_2369_ = lean_array_uget(v_as_2361_, v_i_2363_);
                    v_fst_2370_ = lean_ctor_get(v_a_2369_, 0);
                    v_snd_2371_ = lean_ctor_get(v_a_2369_, 1);
                    v_isSharedCheck_2416_ = (!lean_is_exclusive(v_a_2369_)) as u8;
                    if v_isSharedCheck_2416_ == 0 {
                        v___x_2373_ = v_a_2369_;
                        v_isShared_2374_ = v_isSharedCheck_2416_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2371_);
                        lean_inc(v_fst_2370_);
                        lean_dec(v_a_2369_);
                        v___x_2373_ = lean_box(0);
                        v_isShared_2374_ = v_isSharedCheck_2416_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_fst_2370_);
                v___x_2375_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_fst_2370_, v___y_2365_);
                if lean_obj_tag(v___x_2375_) == 0 {
                    v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
                    lean_inc(v_a_2376_);
                    lean_dec_ref_known(v___x_2375_, 1);
                    v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                    if lean_obj_tag(v_usedCounters_x3f_2360_) == 1 {
                        v_val_2400_ = lean_ctor_get(v_usedCounters_x3f_2360_, 0);
                        v___x_2401_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_val_2400_, v_fst_2370_);
                        lean_dec(v_fst_2370_);
                        if lean_obj_tag(v___x_2401_) == 1 {
                            v_val_2402_ = lean_ctor_get(v___x_2401_, 0);
                            lean_inc(v_val_2402_);
                            lean_dec_ref_known(v___x_2401_, 1);
                            v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7;
                            v___x_2404_ = l_Nat_reprFast(v_val_2402_);
                            v___x_2405_ = lean_string_append(v___x_2403_, v___x_2404_);
                            lean_dec_ref(v___x_2404_);
                            v_usedMsg_2379_ = v___x_2405_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_2401_);
                            v___x_2406_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9);
                            v_usedMsg_2379_ = v___x_2406_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_fst_2370_);
                        v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4;
                        v_usedMsg_2379_ = v___x_2407_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2373_);
                    lean_dec(v_snd_2371_);
                    lean_dec(v_fst_2370_);
                    lean_dec_ref(v_b_2364_);
                    v_a_2408_ = lean_ctor_get(v___x_2375_, 0);
                    v_isSharedCheck_2415_ = (!lean_is_exclusive(v___x_2375_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2410_ = v___x_2375_;
                        v_isShared_2411_ = v_isSharedCheck_2415_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2408_);
                        lean_dec(v___x_2375_);
                        v___x_2410_ = lean_box(0);
                        v_isShared_2411_ = v_isSharedCheck_2415_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2;
                v___x_2381_ = lean_box(0);
                v___x_2382_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
                v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4;
                v___x_2384_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2384_, 0, v___x_2380_);
                lean_ctor_set(v___x_2384_, 1, v___x_2381_);
                lean_ctor_set(v___x_2384_, 2, v___x_2383_);
                lean_ctor_set_float(
                    v___x_2384_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2382_,
                );
                lean_ctor_set_float(
                    v___x_2384_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2382_,
                );
                lean_ctor_set_uint8(
                    v___x_2384_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2367_,
                );
                v___x_2385_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6);
                if v_isShared_2374_ == 0 {
                    lean_ctor_set_tag(v___x_2373_, 7);
                    lean_ctor_set(v___x_2373_, 1, v___x_2385_);
                    lean_ctor_set(v___x_2373_, 0, v_a_2376_);
                    v___x_2387_ = v___x_2373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2376_);
                    lean_ctor_set(v_reuseFailAlloc_2399_, 1, v___x_2385_);
                    v___x_2387_ = v_reuseFailAlloc_2399_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2388_ = l_Nat_reprFast(v_snd_2371_);
                v___x_2389_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2389_, 0, v___x_2388_);
                v___x_2390_ = l_Lean_MessageData_ofFormat(v___x_2389_);
                v___x_2391_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2391_, 0, v___x_2387_);
                lean_ctor_set(v___x_2391_, 1, v___x_2390_);
                v___x_2392_ = l_Lean_stringToMessageData(v_usedMsg_2379_);
                v___x_2393_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2393_, 0, v___x_2391_);
                lean_ctor_set(v___x_2393_, 1, v___x_2392_);
                v___x_2394_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2394_, 0, v___x_2384_);
                lean_ctor_set(v___x_2394_, 1, v___x_2393_);
                lean_ctor_set(v___x_2394_, 2, v___x_2377_);
                v___x_2395_ = lean_array_push(v_b_2364_, v___x_2394_);
                v___x_2396_ = 1usize;
                v___x_2397_ = lean_usize_add(v_i_2363_, v___x_2396_);
                v_i_2363_ = v___x_2397_;
                v_b_2364_ = v___x_2395_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2411_ == 0 {
                    v___x_2413_ = v___x_2410_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
                    v___x_2413_ = v_reuseFailAlloc_2414_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___boxed(
    mut v_usedCounters_x3f_2417_: *mut LeanObject,
    mut v_as_2418_: *mut LeanObject,
    mut v_sz_2419_: *mut LeanObject,
    mut v_i_2420_: *mut LeanObject,
    mut v_b_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2424_: usize = 0;
    let mut v_i_boxed_2425_: usize = 0;
    let mut v_res_2426_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2424_ = lean_unbox_usize(v_sz_2419_);
    lean_dec(v_sz_2419_);
    v_i_boxed_2425_ = lean_unbox_usize(v_i_2420_);
    lean_dec(v_i_2420_);
    v_res_2426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_2417_, v_as_2418_, v_sz_boxed_2424_, v_i_boxed_2425_, v_b_2421_, v___y_2422_);
    lean_dec(v___y_2422_);
    lean_dec_ref(v_as_2418_);
    lean_dec(v_usedCounters_x3f_2417_);
    return v_res_2426_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2() -> *mut LeanObject {
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    v___x_2429_ = lean_unsigned_to_nat(0);
    v___x_2430_ = l_Lean_Meta_instInhabitedOrigin_default;
    v___x_2431_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2431_, 0, v___x_2430_);
    lean_ctor_set(v___x_2431_, 1, v___x_2429_);
    return v___x_2431_;
}
pub unsafe fn l_Lean_Meta_Simp_mkSimpDiagSummary(
    mut v_counters_2435_: *mut LeanObject,
    mut v_usedCounters_x3f_2436_: *mut LeanObject,
    mut v_a_2437_: *mut LeanObject,
    mut v_a_2438_: *mut LeanObject,
    mut v_a_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2452_: usize = 0;
    let mut v___x_2453_: usize = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2458_: u8 = 0;
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_unused_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v_a_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2477_: u8 = 0;
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2442_ = lean_ctor_get(v_a_2439_, 2);
                v___f_2443_ = l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0;
                v___f_2444_ = l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1;
                v___x_2445_ = l_Lean_diagnostics_threshold;
                v___x_2446_ = l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(
                    v_options_2442_,
                    v___x_2445_,
                );
                v___x_2447_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(v_counters_2435_, v___x_2446_, v___f_2444_, v___f_2443_);
                v___x_2448_ = lean_array_get_size(v___x_2447_);
                v___x_2449_ = lean_unsigned_to_nat(0);
                v___x_2450_ = lean_nat_dec_eq(v___x_2448_, v___x_2449_);
                if v___x_2450_ == 0 {
                    v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                    v_sz_2452_ = lean_array_size(v___x_2447_);
                    v___x_2453_ = 0usize;
                    v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_2436_, v___x_2447_, v_sz_2452_, v___x_2453_, v___x_2451_, v_a_2440_);
                    if lean_obj_tag(v___x_2454_) == 0 {
                        v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
                        v_isSharedCheck_2473_ = (!lean_is_exclusive(v___x_2454_)) as u8;
                        if v_isSharedCheck_2473_ == 0 {
                            v___x_2457_ = v___x_2454_;
                            v_isShared_2458_ = v_isSharedCheck_2473_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2455_);
                            lean_dec(v___x_2454_);
                            v___x_2457_ = lean_box(0);
                            v_isShared_2458_ = v_isSharedCheck_2473_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2447_);
                        v_a_2474_ = lean_ctor_get(v___x_2454_, 0);
                        v_isSharedCheck_2481_ = (!lean_is_exclusive(v___x_2454_)) as u8;
                        if v_isSharedCheck_2481_ == 0 {
                            v___x_2476_ = v___x_2454_;
                            v_isShared_2477_ = v_isSharedCheck_2481_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2474_);
                            lean_dec(v___x_2454_);
                            v___x_2476_ = lean_box(0);
                            v_isShared_2477_ = v_isSharedCheck_2481_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2447_);
                    v___x_2482_ = l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3;
                    v___x_2483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2483_, 0, v___x_2482_);
                    return v___x_2483_;
                }
            }
            1 => {
                v___x_2459_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2_once),
                    _init_l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2,
                );
                v___x_2460_ = lean_array_get(v___x_2459_, v___x_2447_, v___x_2449_);
                lean_dec_ref(v___x_2447_);
                v_snd_2461_ = lean_ctor_get(v___x_2460_, 1);
                v_isSharedCheck_2471_ = (!lean_is_exclusive(v___x_2460_)) as u8;
                if v_isSharedCheck_2471_ == 0 {
                    v_unused_2472_ = lean_ctor_get(v___x_2460_, 0);
                    lean_dec(v_unused_2472_);
                    v___x_2463_ = v___x_2460_;
                    v_isShared_2464_ = v_isSharedCheck_2471_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2461_);
                    lean_dec(v___x_2460_);
                    v___x_2463_ = lean_box(0);
                    v_isShared_2464_ = v_isSharedCheck_2471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2464_ == 0 {
                    lean_ctor_set(v___x_2463_, 0, v_a_2455_);
                    v___x_2466_ = v___x_2463_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2455_);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_snd_2461_);
                    v___x_2466_ = v_reuseFailAlloc_2470_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2458_ == 0 {
                    lean_ctor_set(v___x_2457_, 0, v___x_2466_);
                    v___x_2468_ = v___x_2457_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
                    v___x_2468_ = v_reuseFailAlloc_2469_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2468_;
            }
            5 => {
                if v_isShared_2477_ == 0 {
                    v___x_2479_ = v___x_2476_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
                    v___x_2479_ = v_reuseFailAlloc_2480_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_mkSimpDiagSummary___boxed(
    mut v_counters_2484_: *mut LeanObject,
    mut v_usedCounters_x3f_2485_: *mut LeanObject,
    mut v_a_2486_: *mut LeanObject,
    mut v_a_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2491_: *mut LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Lean_Meta_Simp_mkSimpDiagSummary(
        v_counters_2484_,
        v_usedCounters_x3f_2485_,
        v_a_2486_,
        v_a_2487_,
        v_a_2488_,
        v_a_2489_,
    );
    lean_dec(v_a_2489_);
    lean_dec_ref(v_a_2488_);
    lean_dec(v_a_2487_);
    lean_dec_ref(v_a_2486_);
    lean_dec(v_usedCounters_x3f_2485_);
    lean_dec_ref(v_counters_2484_);
    return v_res_2491_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(
    mut v_00_u03b2_2492_: *mut LeanObject,
    mut v_x_2493_: *mut LeanObject,
    mut v_x_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    v___x_2495_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_x_2493_, v_x_2494_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___boxed(
    mut v_00_u03b2_2496_: *mut LeanObject,
    mut v_x_2497_: *mut LeanObject,
    mut v_x_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2499_: *mut LeanObject = core::ptr::null_mut();
    v_res_2499_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(
            v_00_u03b2_2496_,
            v_x_2497_,
            v_x_2498_,
        );
    lean_dec_ref(v_x_2498_);
    lean_dec_ref(v_x_2497_);
    return v_res_2499_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(
    mut v_usedCounters_x3f_2500_: *mut LeanObject,
    mut v_as_2501_: *mut LeanObject,
    mut v_sz_2502_: usize,
    mut v_i_2503_: usize,
    mut v_b_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_2500_, v_as_2501_, v_sz_2502_, v_i_2503_, v_b_2504_, v___y_2508_);
    return v___x_2510_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___boxed(
    mut v_usedCounters_x3f_2511_: *mut LeanObject,
    mut v_as_2512_: *mut LeanObject,
    mut v_sz_2513_: *mut LeanObject,
    mut v_i_2514_: *mut LeanObject,
    mut v_b_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
    mut v___y_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2521_: usize = 0;
    let mut v_i_boxed_2522_: usize = 0;
    let mut v_res_2523_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2521_ = lean_unbox_usize(v_sz_2513_);
    lean_dec(v_sz_2513_);
    v_i_boxed_2522_ = lean_unbox_usize(v_i_2514_);
    lean_dec(v_i_2514_);
    v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(v_usedCounters_x3f_2511_, v_as_2512_, v_sz_boxed_2521_, v_i_boxed_2522_, v_b_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
    lean_dec(v___y_2519_);
    lean_dec_ref(v___y_2518_);
    lean_dec(v___y_2517_);
    lean_dec_ref(v___y_2516_);
    lean_dec_ref(v_as_2512_);
    lean_dec(v_usedCounters_x3f_2511_);
    return v_res_2523_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(
    mut v_00_u03c3_2524_: *mut LeanObject,
    mut v_00_u03b2_2525_: *mut LeanObject,
    mut v_map_2526_: *mut LeanObject,
    mut v_init_2527_: *mut LeanObject,
    mut v_f_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    v___x_2529_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_map_2526_, v_init_2527_, v_f_2528_);
    return v___x_2529_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___boxed(
    mut v_00_u03c3_2530_: *mut LeanObject,
    mut v_00_u03b2_2531_: *mut LeanObject,
    mut v_map_2532_: *mut LeanObject,
    mut v_init_2533_: *mut LeanObject,
    mut v_f_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2535_: *mut LeanObject = core::ptr::null_mut();
    v_res_2535_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(v_00_u03c3_2530_, v_00_u03b2_2531_, v_map_2532_, v_init_2533_, v_f_2534_);
    lean_dec_ref(v_map_2532_);
    return v_res_2535_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(
    mut v_lt_2536_: *mut LeanObject,
    mut v_n_2537_: *mut LeanObject,
    mut v_as_2538_: *mut LeanObject,
    mut v_lo_2539_: *mut LeanObject,
    mut v_hi_2540_: *mut LeanObject,
    mut v_w_2541_: *mut LeanObject,
    mut v_hlo_2542_: *mut LeanObject,
    mut v_hhi_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    v___x_2544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_2536_, v_n_2537_, v_as_2538_, v_lo_2539_, v_hi_2540_);
    return v___x_2544_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___boxed(
    mut v_lt_2545_: *mut LeanObject,
    mut v_n_2546_: *mut LeanObject,
    mut v_as_2547_: *mut LeanObject,
    mut v_lo_2548_: *mut LeanObject,
    mut v_hi_2549_: *mut LeanObject,
    mut v_w_2550_: *mut LeanObject,
    mut v_hlo_2551_: *mut LeanObject,
    mut v_hhi_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2553_: *mut LeanObject = core::ptr::null_mut();
    v_res_2553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(v_lt_2545_, v_n_2546_, v_as_2547_, v_lo_2548_, v_hi_2549_, v_w_2550_, v_hlo_2551_, v_hhi_2552_);
    lean_dec(v_hi_2549_);
    lean_dec(v_n_2546_);
    return v_res_2553_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(
    mut v_00_u03b2_2554_: *mut LeanObject,
    mut v_x_2555_: *mut LeanObject,
    mut v_x_2556_: usize,
    mut v_x_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    v___x_2558_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_2555_, v_x_2556_, v_x_2557_);
    return v___x_2558_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___boxed(
    mut v_00_u03b2_2559_: *mut LeanObject,
    mut v_x_2560_: *mut LeanObject,
    mut v_x_2561_: *mut LeanObject,
    mut v_x_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5071__boxed_2563_: usize = 0;
    let mut v_res_2564_: *mut LeanObject = core::ptr::null_mut();
    v_x_5071__boxed_2563_ = lean_unbox_usize(v_x_2561_);
    lean_dec(v_x_2561_);
    v_res_2564_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(v_00_u03b2_2559_, v_x_2560_, v_x_5071__boxed_2563_, v_x_2562_);
    lean_dec_ref(v_x_2562_);
    lean_dec_ref(v_x_2560_);
    return v_res_2564_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2___redArg(
    mut v_map_2565_: *mut LeanObject,
    mut v_f_2566_: *mut LeanObject,
    mut v_init_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    v___x_2568_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_2566_, v_map_2565_, v_init_2567_);
    return v___x_2568_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2(
    mut v_00_u03c3_2569_: *mut LeanObject,
    mut v_00_u03c3_2570_: *mut LeanObject,
    mut v_00_u03b2_2571_: *mut LeanObject,
    mut v_map_2572_: *mut LeanObject,
    mut v_f_2573_: *mut LeanObject,
    mut v_init_2574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    v___x_2575_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_2573_, v_map_2572_, v_init_2574_);
    return v___x_2575_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(
    mut v_lt_2576_: *mut LeanObject,
    mut v_n_2577_: *mut LeanObject,
    mut v_lo_2578_: *mut LeanObject,
    mut v_hi_2579_: *mut LeanObject,
    mut v_hhi_2580_: *mut LeanObject,
    mut v_pivot_2581_: *mut LeanObject,
    mut v_as_2582_: *mut LeanObject,
    mut v_i_2583_: *mut LeanObject,
    mut v_k_2584_: *mut LeanObject,
    mut v_ilo_2585_: *mut LeanObject,
    mut v_ik_2586_: *mut LeanObject,
    mut v_w_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    v___x_2588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_2576_, v_hi_2579_, v_pivot_2581_, v_as_2582_, v_i_2583_, v_k_2584_);
    return v___x_2588_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___boxed(
    mut v_lt_2589_: *mut LeanObject,
    mut v_n_2590_: *mut LeanObject,
    mut v_lo_2591_: *mut LeanObject,
    mut v_hi_2592_: *mut LeanObject,
    mut v_hhi_2593_: *mut LeanObject,
    mut v_pivot_2594_: *mut LeanObject,
    mut v_as_2595_: *mut LeanObject,
    mut v_i_2596_: *mut LeanObject,
    mut v_k_2597_: *mut LeanObject,
    mut v_ilo_2598_: *mut LeanObject,
    mut v_ik_2599_: *mut LeanObject,
    mut v_w_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2601_: *mut LeanObject = core::ptr::null_mut();
    v_res_2601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(v_lt_2589_, v_n_2590_, v_lo_2591_, v_hi_2592_, v_hhi_2593_, v_pivot_2594_, v_as_2595_, v_i_2596_, v_k_2597_, v_ilo_2598_, v_ik_2599_, v_w_2600_);
    lean_dec(v_hi_2592_);
    lean_dec(v_lo_2591_);
    lean_dec(v_n_2590_);
    return v_res_2601_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(
    mut v_00_u03b2_2602_: *mut LeanObject,
    mut v_keys_2603_: *mut LeanObject,
    mut v_vals_2604_: *mut LeanObject,
    mut v_heq_2605_: *mut LeanObject,
    mut v_i_2606_: *mut LeanObject,
    mut v_k_2607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    v___x_2608_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_keys_2603_, v_vals_2604_, v_i_2606_, v_k_2607_);
    return v___x_2608_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_2609_: *mut LeanObject,
    mut v_keys_2610_: *mut LeanObject,
    mut v_vals_2611_: *mut LeanObject,
    mut v_heq_2612_: *mut LeanObject,
    mut v_i_2613_: *mut LeanObject,
    mut v_k_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2615_: *mut LeanObject = core::ptr::null_mut();
    v_res_2615_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(v_00_u03b2_2609_, v_keys_2610_, v_vals_2611_, v_heq_2612_, v_i_2613_, v_k_2614_);
    lean_dec_ref(v_k_2614_);
    lean_dec_ref(v_vals_2611_);
    lean_dec_ref(v_keys_2610_);
    return v_res_2615_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5(
    mut v_00_u03c3_2616_: *mut LeanObject,
    mut v_00_u03c3_2617_: *mut LeanObject,
    mut v_00_u03b1_2618_: *mut LeanObject,
    mut v_00_u03b2_2619_: *mut LeanObject,
    mut v_f_2620_: *mut LeanObject,
    mut v_x_2621_: *mut LeanObject,
    mut v_x_2622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    v___x_2623_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_2620_, v_x_2621_, v_x_2622_);
    return v___x_2623_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(
    mut v_00_u03b1_2624_: *mut LeanObject,
    mut v_00_u03b2_2625_: *mut LeanObject,
    mut v_00_u03c3_2626_: *mut LeanObject,
    mut v_00_u03c3_2627_: *mut LeanObject,
    mut v_f_2628_: *mut LeanObject,
    mut v_as_2629_: *mut LeanObject,
    mut v_i_2630_: usize,
    mut v_stop_2631_: usize,
    mut v_b_2632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_2628_, v_as_2629_, v_i_2630_, v_stop_2631_, v_b_2632_);
    return v___x_2633_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(
    mut v_00_u03b1_2634_: *mut LeanObject,
    mut v_00_u03b2_2635_: *mut LeanObject,
    mut v_00_u03c3_2636_: *mut LeanObject,
    mut v_00_u03c3_2637_: *mut LeanObject,
    mut v_f_2638_: *mut LeanObject,
    mut v_as_2639_: *mut LeanObject,
    mut v_i_2640_: *mut LeanObject,
    mut v_stop_2641_: *mut LeanObject,
    mut v_b_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2643_: usize = 0;
    let mut v_stop_boxed_2644_: usize = 0;
    let mut v_res_2645_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2643_ = lean_unbox_usize(v_i_2640_);
    lean_dec(v_i_2640_);
    v_stop_boxed_2644_ = lean_unbox_usize(v_stop_2641_);
    lean_dec(v_stop_2641_);
    v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b1_2634_, v_00_u03b2_2635_, v_00_u03c3_2636_, v_00_u03c3_2637_, v_f_2638_, v_as_2639_, v_i_boxed_2643_, v_stop_boxed_2644_, v_b_2642_);
    lean_dec_ref(v_as_2639_);
    return v_res_2645_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(
    mut v_00_u03c3_2646_: *mut LeanObject,
    mut v_00_u03c3_2647_: *mut LeanObject,
    mut v_00_u03b1_2648_: *mut LeanObject,
    mut v_00_u03b2_2649_: *mut LeanObject,
    mut v_f_2650_: *mut LeanObject,
    mut v_keys_2651_: *mut LeanObject,
    mut v_vals_2652_: *mut LeanObject,
    mut v_heq_2653_: *mut LeanObject,
    mut v_i_2654_: *mut LeanObject,
    mut v_acc_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    v___x_2656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_2650_, v_keys_2651_, v_vals_2652_, v_i_2654_, v_acc_2655_);
    return v___x_2656_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(
    mut v_00_u03c3_2657_: *mut LeanObject,
    mut v_00_u03c3_2658_: *mut LeanObject,
    mut v_00_u03b1_2659_: *mut LeanObject,
    mut v_00_u03b2_2660_: *mut LeanObject,
    mut v_f_2661_: *mut LeanObject,
    mut v_keys_2662_: *mut LeanObject,
    mut v_vals_2663_: *mut LeanObject,
    mut v_heq_2664_: *mut LeanObject,
    mut v_i_2665_: *mut LeanObject,
    mut v_acc_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2667_: *mut LeanObject = core::ptr::null_mut();
    v_res_2667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(v_00_u03c3_2657_, v_00_u03c3_2658_, v_00_u03b1_2659_, v_00_u03b2_2660_, v_f_2661_, v_keys_2662_, v_vals_2663_, v_heq_2664_, v_i_2665_, v_acc_2666_);
    lean_dec_ref(v_vals_2663_);
    lean_dec_ref(v_keys_2662_);
    return v_res_2667_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    v___x_2669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0;
    v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
    return v___x_2670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_as_2671_: *mut LeanObject,
    mut v_sz_2672_: usize,
    mut v_i_2673_: usize,
    mut v_b_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v_a_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: f64 = 0.0;
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: usize = 0;
    let mut v_reuseFailAlloc_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v_a_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut v_unused_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2678_ = lean_usize_dec_lt(v_i_2673_, v_sz_2672_);
                if v___x_2678_ == 0 {
                    v___x_2679_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2679_, 0, v_b_2674_);
                    return v___x_2679_;
                } else {
                    v_snd_2680_ = lean_ctor_get(v_b_2674_, 1);
                    v_isSharedCheck_2724_ = (!lean_is_exclusive(v_b_2674_)) as u8;
                    if v_isSharedCheck_2724_ == 0 {
                        v_unused_2725_ = lean_ctor_get(v_b_2674_, 0);
                        lean_dec(v_unused_2725_);
                        v___x_2682_ = v_b_2674_;
                        v_isShared_2683_ = v_isSharedCheck_2724_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2680_);
                        lean_dec(v_b_2674_);
                        v___x_2682_ = lean_box(0);
                        v_isShared_2683_ = v_isSharedCheck_2724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2684_ = lean_array_uget_borrowed(v_as_2671_, v_i_2673_);
                v_keys_2685_ = lean_ctor_get(v_a_2684_, 0);
                v_origin_2686_ = lean_ctor_get(v_a_2684_, 4);
                lean_inc_ref(v_origin_2686_);
                v___x_2687_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_2686_, v___y_2676_);
                if lean_obj_tag(v___x_2687_) == 0 {
                    v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
                    lean_inc(v_a_2688_);
                    lean_dec_ref_known(v___x_2687_, 1);
                    lean_inc_ref(v_keys_2685_);
                    v___x_2689_ =
                        l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_2685_, v___y_2675_, v___y_2676_);
                    if lean_obj_tag(v___x_2689_) == 0 {
                        v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
                        lean_inc(v_a_2690_);
                        lean_dec_ref_known(v___x_2689_, 1);
                        v_data_2691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                        v___x_2692_ = lean_box(0);
                        v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2;
                        v___x_2694_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
                        v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4;
                        v___x_2696_ = lean_alloc_ctor(0, 3, (17) as u32);
                        lean_ctor_set(v___x_2696_, 0, v___x_2693_);
                        lean_ctor_set(v___x_2696_, 1, v___x_2692_);
                        lean_ctor_set(v___x_2696_, 2, v___x_2695_);
                        lean_ctor_set_float(
                            v___x_2696_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_2694_,
                        );
                        lean_ctor_set_float(
                            v___x_2696_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            v___x_2694_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2696_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                            v___x_2678_,
                        );
                        v___x_2697_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
                        v___x_2698_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2698_, 0, v_a_2688_);
                        lean_ctor_set(v___x_2698_, 1, v___x_2697_);
                        v___x_2699_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2699_, 0, v___x_2698_);
                        lean_ctor_set(v___x_2699_, 1, v_a_2690_);
                        v___x_2700_ = lean_alloc_ctor(9, 3, (0) as u32);
                        lean_ctor_set(v___x_2700_, 0, v___x_2696_);
                        lean_ctor_set(v___x_2700_, 1, v___x_2699_);
                        lean_ctor_set(v___x_2700_, 2, v_data_2691_);
                        v___x_2701_ = lean_array_push(v_snd_2680_, v___x_2700_);
                        if v_isShared_2683_ == 0 {
                            lean_ctor_set(v___x_2682_, 1, v___x_2701_);
                            lean_ctor_set(v___x_2682_, 0, v___x_2692_);
                            v___x_2703_ = v___x_2682_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2692_);
                            lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2701_);
                            v___x_2703_ = v_reuseFailAlloc_2707_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2688_);
                        lean_del_object(v___x_2682_);
                        lean_dec(v_snd_2680_);
                        v_a_2708_ = lean_ctor_get(v___x_2689_, 0);
                        v_isSharedCheck_2715_ = (!lean_is_exclusive(v___x_2689_)) as u8;
                        if v_isSharedCheck_2715_ == 0 {
                            v___x_2710_ = v___x_2689_;
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2708_);
                            lean_dec(v___x_2689_);
                            v___x_2710_ = lean_box(0);
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2682_);
                    lean_dec(v_snd_2680_);
                    v_a_2716_ = lean_ctor_get(v___x_2687_, 0);
                    v_isSharedCheck_2723_ = (!lean_is_exclusive(v___x_2687_)) as u8;
                    if v_isSharedCheck_2723_ == 0 {
                        v___x_2718_ = v___x_2687_;
                        v_isShared_2719_ = v_isSharedCheck_2723_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2716_);
                        lean_dec(v___x_2687_);
                        v___x_2718_ = lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2723_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2704_ = 1usize;
                v___x_2705_ = lean_usize_add(v_i_2673_, v___x_2704_);
                v_i_2673_ = v___x_2705_;
                v_b_2674_ = v___x_2703_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2711_ == 0 {
                    v___x_2713_ = v___x_2710_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
                    v___x_2713_ = v_reuseFailAlloc_2714_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2713_;
            }
            5 => {
                if v_isShared_2719_ == 0 {
                    v___x_2721_ = v___x_2718_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
                    v___x_2721_ = v_reuseFailAlloc_2722_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_as_2726_: *mut LeanObject,
    mut v_sz_2727_: *mut LeanObject,
    mut v_i_2728_: *mut LeanObject,
    mut v_b_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
    mut v___y_2732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2733_: usize = 0;
    let mut v_i_boxed_2734_: usize = 0;
    let mut v_res_2735_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2733_ = lean_unbox_usize(v_sz_2727_);
    lean_dec(v_sz_2727_);
    v_i_boxed_2734_ = lean_unbox_usize(v_i_2728_);
    lean_dec(v_i_2728_);
    v_res_2735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_2726_, v_sz_boxed_2733_, v_i_boxed_2734_, v_b_2729_, v___y_2730_, v___y_2731_);
    lean_dec(v___y_2731_);
    lean_dec_ref(v___y_2730_);
    lean_dec_ref(v_as_2726_);
    return v_res_2735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(
    mut v_as_2736_: *mut LeanObject,
    mut v_sz_2737_: usize,
    mut v_i_2738_: usize,
    mut v_b_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v_a_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: f64 = 0.0;
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: usize = 0;
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_a_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2786_: u8 = 0;
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut v_unused_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2745_ = lean_usize_dec_lt(v_i_2738_, v_sz_2737_);
                if v___x_2745_ == 0 {
                    v___x_2746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2746_, 0, v_b_2739_);
                    return v___x_2746_;
                } else {
                    v_snd_2747_ = lean_ctor_get(v_b_2739_, 1);
                    v_isSharedCheck_2791_ = (!lean_is_exclusive(v_b_2739_)) as u8;
                    if v_isSharedCheck_2791_ == 0 {
                        v_unused_2792_ = lean_ctor_get(v_b_2739_, 0);
                        lean_dec(v_unused_2792_);
                        v___x_2749_ = v_b_2739_;
                        v_isShared_2750_ = v_isSharedCheck_2791_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2747_);
                        lean_dec(v_b_2739_);
                        v___x_2749_ = lean_box(0);
                        v_isShared_2750_ = v_isSharedCheck_2791_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2751_ = lean_array_uget_borrowed(v_as_2736_, v_i_2738_);
                v_keys_2752_ = lean_ctor_get(v_a_2751_, 0);
                v_origin_2753_ = lean_ctor_get(v_a_2751_, 4);
                lean_inc_ref(v_origin_2753_);
                v___x_2754_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_2753_, v___y_2743_);
                if lean_obj_tag(v___x_2754_) == 0 {
                    v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
                    lean_inc(v_a_2755_);
                    lean_dec_ref_known(v___x_2754_, 1);
                    lean_inc_ref(v_keys_2752_);
                    v___x_2756_ =
                        l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_2752_, v___y_2742_, v___y_2743_);
                    if lean_obj_tag(v___x_2756_) == 0 {
                        v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
                        lean_inc(v_a_2757_);
                        lean_dec_ref_known(v___x_2756_, 1);
                        v_data_2758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                        v___x_2759_ = lean_box(0);
                        v___x_2760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2;
                        v___x_2761_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
                        v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4;
                        v___x_2763_ = lean_alloc_ctor(0, 3, (17) as u32);
                        lean_ctor_set(v___x_2763_, 0, v___x_2760_);
                        lean_ctor_set(v___x_2763_, 1, v___x_2759_);
                        lean_ctor_set(v___x_2763_, 2, v___x_2762_);
                        lean_ctor_set_float(
                            v___x_2763_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_2761_,
                        );
                        lean_ctor_set_float(
                            v___x_2763_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            v___x_2761_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2763_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                            v___x_2745_,
                        );
                        v___x_2764_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
                        v___x_2765_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2765_, 0, v_a_2755_);
                        lean_ctor_set(v___x_2765_, 1, v___x_2764_);
                        v___x_2766_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2766_, 0, v___x_2765_);
                        lean_ctor_set(v___x_2766_, 1, v_a_2757_);
                        v___x_2767_ = lean_alloc_ctor(9, 3, (0) as u32);
                        lean_ctor_set(v___x_2767_, 0, v___x_2763_);
                        lean_ctor_set(v___x_2767_, 1, v___x_2766_);
                        lean_ctor_set(v___x_2767_, 2, v_data_2758_);
                        v___x_2768_ = lean_array_push(v_snd_2747_, v___x_2767_);
                        if v_isShared_2750_ == 0 {
                            lean_ctor_set(v___x_2749_, 1, v___x_2768_);
                            lean_ctor_set(v___x_2749_, 0, v___x_2759_);
                            v___x_2770_ = v___x_2749_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2759_);
                            lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2768_);
                            v___x_2770_ = v_reuseFailAlloc_2774_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2755_);
                        lean_del_object(v___x_2749_);
                        lean_dec(v_snd_2747_);
                        v_a_2775_ = lean_ctor_get(v___x_2756_, 0);
                        v_isSharedCheck_2782_ = (!lean_is_exclusive(v___x_2756_)) as u8;
                        if v_isSharedCheck_2782_ == 0 {
                            v___x_2777_ = v___x_2756_;
                            v_isShared_2778_ = v_isSharedCheck_2782_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2775_);
                            lean_dec(v___x_2756_);
                            v___x_2777_ = lean_box(0);
                            v_isShared_2778_ = v_isSharedCheck_2782_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2749_);
                    lean_dec(v_snd_2747_);
                    v_a_2783_ = lean_ctor_get(v___x_2754_, 0);
                    v_isSharedCheck_2790_ = (!lean_is_exclusive(v___x_2754_)) as u8;
                    if v_isSharedCheck_2790_ == 0 {
                        v___x_2785_ = v___x_2754_;
                        v_isShared_2786_ = v_isSharedCheck_2790_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2783_);
                        lean_dec(v___x_2754_);
                        v___x_2785_ = lean_box(0);
                        v_isShared_2786_ = v_isSharedCheck_2790_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2771_ = 1usize;
                v___x_2772_ = lean_usize_add(v_i_2738_, v___x_2771_);
                v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_2736_, v_sz_2737_, v___x_2772_, v___x_2770_, v___y_2742_, v___y_2743_);
                return v___x_2773_;
            }
            3 => {
                if v_isShared_2778_ == 0 {
                    v___x_2780_ = v___x_2777_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
                    v___x_2780_ = v_reuseFailAlloc_2781_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2780_;
            }
            5 => {
                if v_isShared_2786_ == 0 {
                    v___x_2788_ = v___x_2785_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
                    v___x_2788_ = v_reuseFailAlloc_2789_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2___boxed(
    mut v_as_2793_: *mut LeanObject,
    mut v_sz_2794_: *mut LeanObject,
    mut v_i_2795_: *mut LeanObject,
    mut v_b_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
    mut v___y_2799_: *mut LeanObject,
    mut v___y_2800_: *mut LeanObject,
    mut v___y_2801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2802_: usize = 0;
    let mut v_i_boxed_2803_: usize = 0;
    let mut v_res_2804_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2802_ = lean_unbox_usize(v_sz_2794_);
    lean_dec(v_sz_2794_);
    v_i_boxed_2803_ = lean_unbox_usize(v_i_2795_);
    lean_dec(v_i_2795_);
    v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_as_2793_, v_sz_boxed_2802_, v_i_boxed_2803_, v_b_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
    lean_dec(v___y_2800_);
    lean_dec_ref(v___y_2799_);
    lean_dec(v___y_2798_);
    lean_dec_ref(v___y_2797_);
    lean_dec_ref(v_as_2793_);
    return v_res_2804_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(
    mut v_init_2805_: *mut LeanObject,
    mut v_n_2806_: *mut LeanObject,
    mut v_b_2807_: *mut LeanObject,
    mut v___y_2808_: *mut LeanObject,
    mut v___y_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
    mut v___y_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2816_: usize = 0;
    let mut v___x_2817_: usize = 0;
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v_fst_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2833_: u8 = 0;
    let mut v_a_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_vs_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2845_: usize = 0;
    let mut v___x_2846_: usize = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v_fst_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2862_: u8 = 0;
    let mut v_a_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_2806_) == 0 {
                    v_cs_2813_ = lean_ctor_get(v_n_2806_, 0);
                    v___x_2814_ = lean_box(0);
                    v___x_2815_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2815_, 0, v___x_2814_);
                    lean_ctor_set(v___x_2815_, 1, v_b_2807_);
                    v_sz_2816_ = lean_array_size(v_cs_2813_);
                    v___x_2817_ = 0usize;
                    v___x_2818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_2805_, v_cs_2813_, v_sz_2816_, v___x_2817_, v___x_2815_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
                    if lean_obj_tag(v___x_2818_) == 0 {
                        v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
                        v_isSharedCheck_2833_ = (!lean_is_exclusive(v___x_2818_)) as u8;
                        if v_isSharedCheck_2833_ == 0 {
                            v___x_2821_ = v___x_2818_;
                            v_isShared_2822_ = v_isSharedCheck_2833_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2819_);
                            lean_dec(v___x_2818_);
                            v___x_2821_ = lean_box(0);
                            v_isShared_2822_ = v_isSharedCheck_2833_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2834_ = lean_ctor_get(v___x_2818_, 0);
                        v_isSharedCheck_2841_ = (!lean_is_exclusive(v___x_2818_)) as u8;
                        if v_isSharedCheck_2841_ == 0 {
                            v___x_2836_ = v___x_2818_;
                            v_isShared_2837_ = v_isSharedCheck_2841_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2834_);
                            lean_dec(v___x_2818_);
                            v___x_2836_ = lean_box(0);
                            v_isShared_2837_ = v_isSharedCheck_2841_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2842_ = lean_ctor_get(v_n_2806_, 0);
                    v___x_2843_ = lean_box(0);
                    v___x_2844_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2844_, 0, v___x_2843_);
                    lean_ctor_set(v___x_2844_, 1, v_b_2807_);
                    v_sz_2845_ = lean_array_size(v_vs_2842_);
                    v___x_2846_ = 0usize;
                    v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_vs_2842_, v_sz_2845_, v___x_2846_, v___x_2844_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
                    if lean_obj_tag(v___x_2847_) == 0 {
                        v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
                        v_isSharedCheck_2862_ = (!lean_is_exclusive(v___x_2847_)) as u8;
                        if v_isSharedCheck_2862_ == 0 {
                            v___x_2850_ = v___x_2847_;
                            v_isShared_2851_ = v_isSharedCheck_2862_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2848_);
                            lean_dec(v___x_2847_);
                            v___x_2850_ = lean_box(0);
                            v_isShared_2851_ = v_isSharedCheck_2862_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2863_ = lean_ctor_get(v___x_2847_, 0);
                        v_isSharedCheck_2870_ = (!lean_is_exclusive(v___x_2847_)) as u8;
                        if v_isSharedCheck_2870_ == 0 {
                            v___x_2865_ = v___x_2847_;
                            v_isShared_2866_ = v_isSharedCheck_2870_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2863_);
                            lean_dec(v___x_2847_);
                            v___x_2865_ = lean_box(0);
                            v_isShared_2866_ = v_isSharedCheck_2870_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2823_ = lean_ctor_get(v_a_2819_, 0);
                if lean_obj_tag(v_fst_2823_) == 0 {
                    v_snd_2824_ = lean_ctor_get(v_a_2819_, 1);
                    lean_inc(v_snd_2824_);
                    lean_dec(v_a_2819_);
                    v___x_2825_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2825_, 0, v_snd_2824_);
                    if v_isShared_2822_ == 0 {
                        lean_ctor_set(v___x_2821_, 0, v___x_2825_);
                        v___x_2827_ = v___x_2821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
                        v___x_2827_ = v_reuseFailAlloc_2828_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2823_);
                    lean_dec(v_a_2819_);
                    v_val_2829_ = lean_ctor_get(v_fst_2823_, 0);
                    lean_inc(v_val_2829_);
                    lean_dec_ref_known(v_fst_2823_, 1);
                    if v_isShared_2822_ == 0 {
                        lean_ctor_set(v___x_2821_, 0, v_val_2829_);
                        v___x_2831_ = v___x_2821_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_val_2829_);
                        v___x_2831_ = v_reuseFailAlloc_2832_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2827_;
            }
            3 => {
                return v___x_2831_;
            }
            4 => {
                if v_isShared_2837_ == 0 {
                    v___x_2839_ = v___x_2836_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
                    v___x_2839_ = v_reuseFailAlloc_2840_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2839_;
            }
            6 => {
                v_fst_2852_ = lean_ctor_get(v_a_2848_, 0);
                if lean_obj_tag(v_fst_2852_) == 0 {
                    v_snd_2853_ = lean_ctor_get(v_a_2848_, 1);
                    lean_inc(v_snd_2853_);
                    lean_dec(v_a_2848_);
                    v___x_2854_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2854_, 0, v_snd_2853_);
                    if v_isShared_2851_ == 0 {
                        lean_ctor_set(v___x_2850_, 0, v___x_2854_);
                        v___x_2856_ = v___x_2850_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
                        v___x_2856_ = v_reuseFailAlloc_2857_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2852_);
                    lean_dec(v_a_2848_);
                    v_val_2858_ = lean_ctor_get(v_fst_2852_, 0);
                    lean_inc(v_val_2858_);
                    lean_dec_ref_known(v_fst_2852_, 1);
                    if v_isShared_2851_ == 0 {
                        lean_ctor_set(v___x_2850_, 0, v_val_2858_);
                        v___x_2860_ = v___x_2850_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_val_2858_);
                        v___x_2860_ = v_reuseFailAlloc_2861_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2856_;
            }
            8 => {
                return v___x_2860_;
            }
            9 => {
                if v_isShared_2866_ == 0 {
                    v___x_2868_ = v___x_2865_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
                    v___x_2868_ = v_reuseFailAlloc_2869_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(
    mut v_init_2871_: *mut LeanObject,
    mut v_as_2872_: *mut LeanObject,
    mut v_sz_2873_: usize,
    mut v_i_2874_: usize,
    mut v_b_2875_: *mut LeanObject,
    mut v___y_2876_: *mut LeanObject,
    mut v___y_2877_: *mut LeanObject,
    mut v___y_2878_: *mut LeanObject,
    mut v___y_2879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2881_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v_a_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2892_: u8 = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: usize = 0;
    let mut v___x_2905_: usize = 0;
    let mut v_reuseFailAlloc_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut v_a_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut v_unused_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2881_ = lean_usize_dec_lt(v_i_2874_, v_sz_2873_);
                if v___x_2881_ == 0 {
                    v___x_2882_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2882_, 0, v_b_2875_);
                    return v___x_2882_;
                } else {
                    v_snd_2883_ = lean_ctor_get(v_b_2875_, 1);
                    v_isSharedCheck_2917_ = (!lean_is_exclusive(v_b_2875_)) as u8;
                    if v_isSharedCheck_2917_ == 0 {
                        v_unused_2918_ = lean_ctor_get(v_b_2875_, 0);
                        lean_dec(v_unused_2918_);
                        v___x_2885_ = v_b_2875_;
                        v_isShared_2886_ = v_isSharedCheck_2917_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2883_);
                        lean_dec(v_b_2875_);
                        v___x_2885_ = lean_box(0);
                        v_isShared_2886_ = v_isSharedCheck_2917_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2887_ = lean_array_uget_borrowed(v_as_2872_, v_i_2874_);
                lean_inc(v_snd_2883_);
                v___x_2888_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_2871_, v_a_2887_, v_snd_2883_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
                if lean_obj_tag(v___x_2888_) == 0 {
                    v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
                    v_isSharedCheck_2908_ = (!lean_is_exclusive(v___x_2888_)) as u8;
                    if v_isSharedCheck_2908_ == 0 {
                        v___x_2891_ = v___x_2888_;
                        v_isShared_2892_ = v_isSharedCheck_2908_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2889_);
                        lean_dec(v___x_2888_);
                        v___x_2891_ = lean_box(0);
                        v_isShared_2892_ = v_isSharedCheck_2908_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2885_);
                    lean_dec(v_snd_2883_);
                    v_a_2909_ = lean_ctor_get(v___x_2888_, 0);
                    v_isSharedCheck_2916_ = (!lean_is_exclusive(v___x_2888_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2911_ = v___x_2888_;
                        v_isShared_2912_ = v_isSharedCheck_2916_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2909_);
                        lean_dec(v___x_2888_);
                        v___x_2911_ = lean_box(0);
                        v_isShared_2912_ = v_isSharedCheck_2916_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2889_) == 0 {
                    v___x_2893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2893_, 0, v_a_2889_);
                    if v_isShared_2886_ == 0 {
                        lean_ctor_set(v___x_2885_, 0, v___x_2893_);
                        v___x_2895_ = v___x_2885_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2893_);
                        lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_snd_2883_);
                        v___x_2895_ = v_reuseFailAlloc_2899_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2891_);
                    lean_dec(v_snd_2883_);
                    v_a_2900_ = lean_ctor_get(v_a_2889_, 0);
                    lean_inc(v_a_2900_);
                    lean_dec_ref_known(v_a_2889_, 1);
                    v___x_2901_ = lean_box(0);
                    if v_isShared_2886_ == 0 {
                        lean_ctor_set(v___x_2885_, 1, v_a_2900_);
                        lean_ctor_set(v___x_2885_, 0, v___x_2901_);
                        v___x_2903_ = v___x_2885_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2901_);
                        lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_a_2900_);
                        v___x_2903_ = v_reuseFailAlloc_2907_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2892_ == 0 {
                    lean_ctor_set(v___x_2891_, 0, v___x_2895_);
                    v___x_2897_ = v___x_2891_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
                    v___x_2897_ = v_reuseFailAlloc_2898_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2897_;
            }
            5 => {
                v___x_2904_ = 1usize;
                v___x_2905_ = lean_usize_add(v_i_2874_, v___x_2904_);
                v_i_2874_ = v___x_2905_;
                v_b_2875_ = v___x_2903_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2912_ == 0 {
                    v___x_2914_ = v___x_2911_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
                    v___x_2914_ = v_reuseFailAlloc_2915_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1___boxed(
    mut v_init_2919_: *mut LeanObject,
    mut v_as_2920_: *mut LeanObject,
    mut v_sz_2921_: *mut LeanObject,
    mut v_i_2922_: *mut LeanObject,
    mut v_b_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
    mut v___y_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2929_: usize = 0;
    let mut v_i_boxed_2930_: usize = 0;
    let mut v_res_2931_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2929_ = lean_unbox_usize(v_sz_2921_);
    lean_dec(v_sz_2921_);
    v_i_boxed_2930_ = lean_unbox_usize(v_i_2922_);
    lean_dec(v_i_2922_);
    v_res_2931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_2919_, v_as_2920_, v_sz_boxed_2929_, v_i_boxed_2930_, v_b_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
    lean_dec(v___y_2927_);
    lean_dec_ref(v___y_2926_);
    lean_dec(v___y_2925_);
    lean_dec_ref(v___y_2924_);
    lean_dec_ref(v_as_2920_);
    lean_dec_ref(v_init_2919_);
    return v_res_2931_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0___boxed(
    mut v_init_2932_: *mut LeanObject,
    mut v_n_2933_: *mut LeanObject,
    mut v_b_2934_: *mut LeanObject,
    mut v___y_2935_: *mut LeanObject,
    mut v___y_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2940_: *mut LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_2932_, v_n_2933_, v_b_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
    lean_dec(v___y_2938_);
    lean_dec_ref(v___y_2937_);
    lean_dec(v___y_2936_);
    lean_dec_ref(v___y_2935_);
    lean_dec_ref(v_n_2933_);
    lean_dec_ref(v_init_2932_);
    return v_res_2940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(
    mut v_as_2941_: *mut LeanObject,
    mut v_sz_2942_: usize,
    mut v_i_2943_: usize,
    mut v_b_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v_a_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: f64 = 0.0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: usize = 0;
    let mut v___x_2975_: usize = 0;
    let mut v_reuseFailAlloc_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2981_: u8 = 0;
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_a_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2989_: u8 = 0;
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2993_: u8 = 0;
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_unused_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2948_ = lean_usize_dec_lt(v_i_2943_, v_sz_2942_);
                if v___x_2948_ == 0 {
                    v___x_2949_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2949_, 0, v_b_2944_);
                    return v___x_2949_;
                } else {
                    v_snd_2950_ = lean_ctor_get(v_b_2944_, 1);
                    v_isSharedCheck_2994_ = (!lean_is_exclusive(v_b_2944_)) as u8;
                    if v_isSharedCheck_2994_ == 0 {
                        v_unused_2995_ = lean_ctor_get(v_b_2944_, 0);
                        lean_dec(v_unused_2995_);
                        v___x_2952_ = v_b_2944_;
                        v_isShared_2953_ = v_isSharedCheck_2994_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2950_);
                        lean_dec(v_b_2944_);
                        v___x_2952_ = lean_box(0);
                        v_isShared_2953_ = v_isSharedCheck_2994_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2954_ = lean_array_uget_borrowed(v_as_2941_, v_i_2943_);
                v_keys_2955_ = lean_ctor_get(v_a_2954_, 0);
                v_origin_2956_ = lean_ctor_get(v_a_2954_, 4);
                lean_inc_ref(v_origin_2956_);
                v___x_2957_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_2956_, v___y_2946_);
                if lean_obj_tag(v___x_2957_) == 0 {
                    v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
                    lean_inc(v_a_2958_);
                    lean_dec_ref_known(v___x_2957_, 1);
                    lean_inc_ref(v_keys_2955_);
                    v___x_2959_ =
                        l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_2955_, v___y_2945_, v___y_2946_);
                    if lean_obj_tag(v___x_2959_) == 0 {
                        v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
                        lean_inc(v_a_2960_);
                        lean_dec_ref_known(v___x_2959_, 1);
                        v_data_2961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                        v___x_2962_ = lean_box(0);
                        v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2;
                        v___x_2964_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
                        v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4;
                        v___x_2966_ = lean_alloc_ctor(0, 3, (17) as u32);
                        lean_ctor_set(v___x_2966_, 0, v___x_2963_);
                        lean_ctor_set(v___x_2966_, 1, v___x_2962_);
                        lean_ctor_set(v___x_2966_, 2, v___x_2965_);
                        lean_ctor_set_float(
                            v___x_2966_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_2964_,
                        );
                        lean_ctor_set_float(
                            v___x_2966_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            v___x_2964_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2966_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                            v___x_2948_,
                        );
                        v___x_2967_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
                        v___x_2968_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2968_, 0, v_a_2958_);
                        lean_ctor_set(v___x_2968_, 1, v___x_2967_);
                        v___x_2969_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2969_, 0, v___x_2968_);
                        lean_ctor_set(v___x_2969_, 1, v_a_2960_);
                        v___x_2970_ = lean_alloc_ctor(9, 3, (0) as u32);
                        lean_ctor_set(v___x_2970_, 0, v___x_2966_);
                        lean_ctor_set(v___x_2970_, 1, v___x_2969_);
                        lean_ctor_set(v___x_2970_, 2, v_data_2961_);
                        v___x_2971_ = lean_array_push(v_snd_2950_, v___x_2970_);
                        if v_isShared_2953_ == 0 {
                            lean_ctor_set(v___x_2952_, 1, v___x_2971_);
                            lean_ctor_set(v___x_2952_, 0, v___x_2962_);
                            v___x_2973_ = v___x_2952_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2962_);
                            lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2971_);
                            v___x_2973_ = v_reuseFailAlloc_2977_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2958_);
                        lean_del_object(v___x_2952_);
                        lean_dec(v_snd_2950_);
                        v_a_2978_ = lean_ctor_get(v___x_2959_, 0);
                        v_isSharedCheck_2985_ = (!lean_is_exclusive(v___x_2959_)) as u8;
                        if v_isSharedCheck_2985_ == 0 {
                            v___x_2980_ = v___x_2959_;
                            v_isShared_2981_ = v_isSharedCheck_2985_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2978_);
                            lean_dec(v___x_2959_);
                            v___x_2980_ = lean_box(0);
                            v_isShared_2981_ = v_isSharedCheck_2985_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2952_);
                    lean_dec(v_snd_2950_);
                    v_a_2986_ = lean_ctor_get(v___x_2957_, 0);
                    v_isSharedCheck_2993_ = (!lean_is_exclusive(v___x_2957_)) as u8;
                    if v_isSharedCheck_2993_ == 0 {
                        v___x_2988_ = v___x_2957_;
                        v_isShared_2989_ = v_isSharedCheck_2993_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2986_);
                        lean_dec(v___x_2957_);
                        v___x_2988_ = lean_box(0);
                        v_isShared_2989_ = v_isSharedCheck_2993_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2974_ = 1usize;
                v___x_2975_ = lean_usize_add(v_i_2943_, v___x_2974_);
                v_i_2943_ = v___x_2975_;
                v_b_2944_ = v___x_2973_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2981_ == 0 {
                    v___x_2983_ = v___x_2980_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
                    v___x_2983_ = v_reuseFailAlloc_2984_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2983_;
            }
            5 => {
                if v_isShared_2989_ == 0 {
                    v___x_2991_ = v___x_2988_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
                    v___x_2991_ = v_reuseFailAlloc_2992_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_as_2996_: *mut LeanObject,
    mut v_sz_2997_: *mut LeanObject,
    mut v_i_2998_: *mut LeanObject,
    mut v_b_2999_: *mut LeanObject,
    mut v___y_3000_: *mut LeanObject,
    mut v___y_3001_: *mut LeanObject,
    mut v___y_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3003_: usize = 0;
    let mut v_i_boxed_3004_: usize = 0;
    let mut v_res_3005_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3003_ = lean_unbox_usize(v_sz_2997_);
    lean_dec(v_sz_2997_);
    v_i_boxed_3004_ = lean_unbox_usize(v_i_2998_);
    lean_dec(v_i_2998_);
    v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_2996_, v_sz_boxed_3003_, v_i_boxed_3004_, v_b_2999_, v___y_3000_, v___y_3001_);
    lean_dec(v___y_3001_);
    lean_dec_ref(v___y_3000_);
    lean_dec_ref(v_as_2996_);
    return v_res_3005_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(
    mut v_as_3006_: *mut LeanObject,
    mut v_sz_3007_: usize,
    mut v_i_3008_: usize,
    mut v_b_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3020_: u8 = 0;
    let mut v_a_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: f64 = 0.0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: usize = 0;
    let mut v___x_3042_: usize = 0;
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3048_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3052_: u8 = 0;
    let mut v_a_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3056_: u8 = 0;
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_isSharedCheck_3061_: u8 = 0;
    let mut v_unused_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3015_ = lean_usize_dec_lt(v_i_3008_, v_sz_3007_);
                if v___x_3015_ == 0 {
                    v___x_3016_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3016_, 0, v_b_3009_);
                    return v___x_3016_;
                } else {
                    v_snd_3017_ = lean_ctor_get(v_b_3009_, 1);
                    v_isSharedCheck_3061_ = (!lean_is_exclusive(v_b_3009_)) as u8;
                    if v_isSharedCheck_3061_ == 0 {
                        v_unused_3062_ = lean_ctor_get(v_b_3009_, 0);
                        lean_dec(v_unused_3062_);
                        v___x_3019_ = v_b_3009_;
                        v_isShared_3020_ = v_isSharedCheck_3061_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3017_);
                        lean_dec(v_b_3009_);
                        v___x_3019_ = lean_box(0);
                        v_isShared_3020_ = v_isSharedCheck_3061_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3021_ = lean_array_uget_borrowed(v_as_3006_, v_i_3008_);
                v_keys_3022_ = lean_ctor_get(v_a_3021_, 0);
                v_origin_3023_ = lean_ctor_get(v_a_3021_, 4);
                lean_inc_ref(v_origin_3023_);
                v___x_3024_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_3023_, v___y_3013_);
                if lean_obj_tag(v___x_3024_) == 0 {
                    v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
                    lean_inc(v_a_3025_);
                    lean_dec_ref_known(v___x_3024_, 1);
                    lean_inc_ref(v_keys_3022_);
                    v___x_3026_ =
                        l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_3022_, v___y_3012_, v___y_3013_);
                    if lean_obj_tag(v___x_3026_) == 0 {
                        v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
                        lean_inc(v_a_3027_);
                        lean_dec_ref_known(v___x_3026_, 1);
                        v_data_3028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                        v___x_3029_ = lean_box(0);
                        v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2;
                        v___x_3031_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
                        v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4;
                        v___x_3033_ = lean_alloc_ctor(0, 3, (17) as u32);
                        lean_ctor_set(v___x_3033_, 0, v___x_3030_);
                        lean_ctor_set(v___x_3033_, 1, v___x_3029_);
                        lean_ctor_set(v___x_3033_, 2, v___x_3032_);
                        lean_ctor_set_float(
                            v___x_3033_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_3031_,
                        );
                        lean_ctor_set_float(
                            v___x_3033_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            v___x_3031_,
                        );
                        lean_ctor_set_uint8(
                            v___x_3033_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                            v___x_3015_,
                        );
                        v___x_3034_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
                        v___x_3035_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3035_, 0, v_a_3025_);
                        lean_ctor_set(v___x_3035_, 1, v___x_3034_);
                        v___x_3036_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3036_, 0, v___x_3035_);
                        lean_ctor_set(v___x_3036_, 1, v_a_3027_);
                        v___x_3037_ = lean_alloc_ctor(9, 3, (0) as u32);
                        lean_ctor_set(v___x_3037_, 0, v___x_3033_);
                        lean_ctor_set(v___x_3037_, 1, v___x_3036_);
                        lean_ctor_set(v___x_3037_, 2, v_data_3028_);
                        v___x_3038_ = lean_array_push(v_snd_3017_, v___x_3037_);
                        if v_isShared_3020_ == 0 {
                            lean_ctor_set(v___x_3019_, 1, v___x_3038_);
                            lean_ctor_set(v___x_3019_, 0, v___x_3029_);
                            v___x_3040_ = v___x_3019_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3029_);
                            lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3038_);
                            v___x_3040_ = v_reuseFailAlloc_3044_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3025_);
                        lean_del_object(v___x_3019_);
                        lean_dec(v_snd_3017_);
                        v_a_3045_ = lean_ctor_get(v___x_3026_, 0);
                        v_isSharedCheck_3052_ = (!lean_is_exclusive(v___x_3026_)) as u8;
                        if v_isSharedCheck_3052_ == 0 {
                            v___x_3047_ = v___x_3026_;
                            v_isShared_3048_ = v_isSharedCheck_3052_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3045_);
                            lean_dec(v___x_3026_);
                            v___x_3047_ = lean_box(0);
                            v_isShared_3048_ = v_isSharedCheck_3052_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3019_);
                    lean_dec(v_snd_3017_);
                    v_a_3053_ = lean_ctor_get(v___x_3024_, 0);
                    v_isSharedCheck_3060_ = (!lean_is_exclusive(v___x_3024_)) as u8;
                    if v_isSharedCheck_3060_ == 0 {
                        v___x_3055_ = v___x_3024_;
                        v_isShared_3056_ = v_isSharedCheck_3060_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3053_);
                        lean_dec(v___x_3024_);
                        v___x_3055_ = lean_box(0);
                        v_isShared_3056_ = v_isSharedCheck_3060_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3041_ = 1usize;
                v___x_3042_ = lean_usize_add(v_i_3008_, v___x_3041_);
                v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_3006_, v_sz_3007_, v___x_3042_, v___x_3040_, v___y_3012_, v___y_3013_);
                return v___x_3043_;
            }
            3 => {
                if v_isShared_3048_ == 0 {
                    v___x_3050_ = v___x_3047_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
                    v___x_3050_ = v_reuseFailAlloc_3051_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3050_;
            }
            5 => {
                if v_isShared_3056_ == 0 {
                    v___x_3058_ = v___x_3055_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
                    v___x_3058_ = v_reuseFailAlloc_3059_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1___boxed(
    mut v_as_3063_: *mut LeanObject,
    mut v_sz_3064_: *mut LeanObject,
    mut v_i_3065_: *mut LeanObject,
    mut v_b_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
    mut v___y_3068_: *mut LeanObject,
    mut v___y_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
    mut v___y_3071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3072_: usize = 0;
    let mut v_i_boxed_3073_: usize = 0;
    let mut v_res_3074_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3072_ = lean_unbox_usize(v_sz_3064_);
    lean_dec(v_sz_3064_);
    v_i_boxed_3073_ = lean_unbox_usize(v_i_3065_);
    lean_dec(v_i_3065_);
    v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_as_3063_, v_sz_boxed_3072_, v_i_boxed_3073_, v_b_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
    lean_dec(v___y_3070_);
    lean_dec_ref(v___y_3069_);
    lean_dec(v___y_3068_);
    lean_dec_ref(v___y_3067_);
    lean_dec_ref(v_as_3063_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(
    mut v_t_3075_: *mut LeanObject,
    mut v_init_3076_: *mut LeanObject,
    mut v___y_3077_: *mut LeanObject,
    mut v___y_3078_: *mut LeanObject,
    mut v___y_3079_: *mut LeanObject,
    mut v___y_3080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v_a_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3096_: usize = 0;
    let mut v___x_3097_: usize = 0;
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v_fst_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v_a_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut v_isSharedCheck_3121_: u8 = 0;
    let mut v_a_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3125_: u8 = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3082_ = lean_ctor_get(v_t_3075_, 0);
                v_tail_3083_ = lean_ctor_get(v_t_3075_, 1);
                lean_inc_ref(v_init_3076_);
                v___x_3084_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_3076_, v_root_3082_, v_init_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
                lean_dec_ref(v_init_3076_);
                if lean_obj_tag(v___x_3084_) == 0 {
                    v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
                    v_isSharedCheck_3121_ = (!lean_is_exclusive(v___x_3084_)) as u8;
                    if v_isSharedCheck_3121_ == 0 {
                        v___x_3087_ = v___x_3084_;
                        v_isShared_3088_ = v_isSharedCheck_3121_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3085_);
                        lean_dec(v___x_3084_);
                        v___x_3087_ = lean_box(0);
                        v_isShared_3088_ = v_isSharedCheck_3121_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3122_ = lean_ctor_get(v___x_3084_, 0);
                    v_isSharedCheck_3129_ = (!lean_is_exclusive(v___x_3084_)) as u8;
                    if v_isSharedCheck_3129_ == 0 {
                        v___x_3124_ = v___x_3084_;
                        v_isShared_3125_ = v_isSharedCheck_3129_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3122_);
                        lean_dec(v___x_3084_);
                        v___x_3124_ = lean_box(0);
                        v_isShared_3125_ = v_isSharedCheck_3129_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3085_) == 0 {
                    v_a_3089_ = lean_ctor_get(v_a_3085_, 0);
                    lean_inc(v_a_3089_);
                    lean_dec_ref_known(v_a_3085_, 1);
                    if v_isShared_3088_ == 0 {
                        lean_ctor_set(v___x_3087_, 0, v_a_3089_);
                        v___x_3091_ = v___x_3087_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3089_);
                        v___x_3091_ = v_reuseFailAlloc_3092_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3087_);
                    v_a_3093_ = lean_ctor_get(v_a_3085_, 0);
                    lean_inc(v_a_3093_);
                    lean_dec_ref_known(v_a_3085_, 1);
                    v___x_3094_ = lean_box(0);
                    v___x_3095_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3095_, 0, v___x_3094_);
                    lean_ctor_set(v___x_3095_, 1, v_a_3093_);
                    v_sz_3096_ = lean_array_size(v_tail_3083_);
                    v___x_3097_ = 0usize;
                    v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_tail_3083_, v_sz_3096_, v___x_3097_, v___x_3095_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
                    if lean_obj_tag(v___x_3098_) == 0 {
                        v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
                        v_isSharedCheck_3112_ = (!lean_is_exclusive(v___x_3098_)) as u8;
                        if v_isSharedCheck_3112_ == 0 {
                            v___x_3101_ = v___x_3098_;
                            v_isShared_3102_ = v_isSharedCheck_3112_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3099_);
                            lean_dec(v___x_3098_);
                            v___x_3101_ = lean_box(0);
                            v_isShared_3102_ = v_isSharedCheck_3112_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3113_ = lean_ctor_get(v___x_3098_, 0);
                        v_isSharedCheck_3120_ = (!lean_is_exclusive(v___x_3098_)) as u8;
                        if v_isSharedCheck_3120_ == 0 {
                            v___x_3115_ = v___x_3098_;
                            v_isShared_3116_ = v_isSharedCheck_3120_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3113_);
                            lean_dec(v___x_3098_);
                            v___x_3115_ = lean_box(0);
                            v_isShared_3116_ = v_isSharedCheck_3120_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3091_;
            }
            3 => {
                v_fst_3103_ = lean_ctor_get(v_a_3099_, 0);
                if lean_obj_tag(v_fst_3103_) == 0 {
                    v_snd_3104_ = lean_ctor_get(v_a_3099_, 1);
                    lean_inc(v_snd_3104_);
                    lean_dec(v_a_3099_);
                    if v_isShared_3102_ == 0 {
                        lean_ctor_set(v___x_3101_, 0, v_snd_3104_);
                        v___x_3106_ = v___x_3101_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_snd_3104_);
                        v___x_3106_ = v_reuseFailAlloc_3107_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3103_);
                    lean_dec(v_a_3099_);
                    v_val_3108_ = lean_ctor_get(v_fst_3103_, 0);
                    lean_inc(v_val_3108_);
                    lean_dec_ref_known(v_fst_3103_, 1);
                    if v_isShared_3102_ == 0 {
                        lean_ctor_set(v___x_3101_, 0, v_val_3108_);
                        v___x_3110_ = v___x_3101_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_val_3108_);
                        v___x_3110_ = v_reuseFailAlloc_3111_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3106_;
            }
            5 => {
                return v___x_3110_;
            }
            6 => {
                if v_isShared_3116_ == 0 {
                    v___x_3118_ = v___x_3115_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
                    v___x_3118_ = v_reuseFailAlloc_3119_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3118_;
            }
            8 => {
                if v_isShared_3125_ == 0 {
                    v___x_3127_ = v___x_3124_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
                    v___x_3127_ = v_reuseFailAlloc_3128_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0___boxed(
    mut v_t_3130_: *mut LeanObject,
    mut v_init_3131_: *mut LeanObject,
    mut v___y_3132_: *mut LeanObject,
    mut v___y_3133_: *mut LeanObject,
    mut v___y_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3137_: *mut LeanObject = core::ptr::null_mut();
    v_res_3137_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_t_3130_, v_init_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
    lean_dec(v___y_3135_);
    lean_dec_ref(v___y_3134_);
    lean_dec(v___y_3133_);
    lean_dec_ref(v___y_3132_);
    lean_dec_ref(v_t_3130_);
    return v_res_3137_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(
    mut v_thms_3138_: *mut LeanObject,
    mut v_a_3139_: *mut LeanObject,
    mut v_a_3140_: *mut LeanObject,
    mut v_a_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_a_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3144_ = l_Lean_PersistentArray_isEmpty___redArg(v_thms_3138_);
                if v___x_3144_ == 0 {
                    v___x_3145_ = lean_unsigned_to_nat(0);
                    v_data_3146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                    v___x_3147_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_thms_3138_, v_data_3146_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
                    if lean_obj_tag(v___x_3147_) == 0 {
                        v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
                        v_isSharedCheck_3156_ = (!lean_is_exclusive(v___x_3147_)) as u8;
                        if v_isSharedCheck_3156_ == 0 {
                            v___x_3150_ = v___x_3147_;
                            v_isShared_3151_ = v_isSharedCheck_3156_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3148_);
                            lean_dec(v___x_3147_);
                            v___x_3150_ = lean_box(0);
                            v_isShared_3151_ = v_isSharedCheck_3156_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3157_ = lean_ctor_get(v___x_3147_, 0);
                        v_isSharedCheck_3164_ = (!lean_is_exclusive(v___x_3147_)) as u8;
                        if v_isSharedCheck_3164_ == 0 {
                            v___x_3159_ = v___x_3147_;
                            v_isShared_3160_ = v_isSharedCheck_3164_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3157_);
                            lean_dec(v___x_3147_);
                            v___x_3159_ = lean_box(0);
                            v_isShared_3160_ = v_isSharedCheck_3164_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_3165_ = l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3;
                    v___x_3166_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3166_, 0, v___x_3165_);
                    return v___x_3166_;
                }
            }
            1 => {
                v___x_3152_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3152_, 0, v_a_3148_);
                lean_ctor_set(v___x_3152_, 1, v___x_3145_);
                if v_isShared_3151_ == 0 {
                    lean_ctor_set(v___x_3150_, 0, v___x_3152_);
                    v___x_3154_ = v___x_3150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3152_);
                    v___x_3154_ = v_reuseFailAlloc_3155_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3154_;
            }
            3 => {
                if v_isShared_3160_ == 0 {
                    v___x_3162_ = v___x_3159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
                    v___x_3162_ = v_reuseFailAlloc_3163_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary___boxed(
    mut v_thms_3167_: *mut LeanObject,
    mut v_a_3168_: *mut LeanObject,
    mut v_a_3169_: *mut LeanObject,
    mut v_a_3170_: *mut LeanObject,
    mut v_a_3171_: *mut LeanObject,
    mut v_a_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3173_: *mut LeanObject = core::ptr::null_mut();
    v_res_3173_ =
        l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(
            v_thms_3167_,
            v_a_3168_,
            v_a_3169_,
            v_a_3170_,
            v_a_3171_,
        );
    lean_dec(v_a_3171_);
    lean_dec_ref(v_a_3170_);
    lean_dec(v_a_3169_);
    lean_dec_ref(v_a_3168_);
    lean_dec_ref(v_thms_3167_);
    return v_res_3173_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(
    mut v_as_3174_: *mut LeanObject,
    mut v_sz_3175_: usize,
    mut v_i_3176_: usize,
    mut v_b_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
    mut v___y_3180_: *mut LeanObject,
    mut v___y_3181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_3174_, v_sz_3175_, v_i_3176_, v_b_3177_, v___y_3180_, v___y_3181_);
    return v___x_3183_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___boxed(
    mut v_as_3184_: *mut LeanObject,
    mut v_sz_3185_: *mut LeanObject,
    mut v_i_3186_: *mut LeanObject,
    mut v_b_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
    mut v___y_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
    mut v___y_3191_: *mut LeanObject,
    mut v___y_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3193_: usize = 0;
    let mut v_i_boxed_3194_: usize = 0;
    let mut v_res_3195_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3193_ = lean_unbox_usize(v_sz_3185_);
    lean_dec(v_sz_3185_);
    v_i_boxed_3194_ = lean_unbox_usize(v_i_3186_);
    lean_dec(v_i_3186_);
    v_res_3195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(v_as_3184_, v_sz_boxed_3193_, v_i_boxed_3194_, v_b_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
    lean_dec(v___y_3191_);
    lean_dec_ref(v___y_3190_);
    lean_dec(v___y_3189_);
    lean_dec_ref(v___y_3188_);
    lean_dec_ref(v_as_3184_);
    return v_res_3195_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(
    mut v_as_3196_: *mut LeanObject,
    mut v_sz_3197_: usize,
    mut v_i_3198_: usize,
    mut v_b_3199_: *mut LeanObject,
    mut v___y_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
    mut v___y_3202_: *mut LeanObject,
    mut v___y_3203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_3196_, v_sz_3197_, v_i_3198_, v_b_3199_, v___y_3202_, v___y_3203_);
    return v___x_3205_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_as_3206_: *mut LeanObject,
    mut v_sz_3207_: *mut LeanObject,
    mut v_i_3208_: *mut LeanObject,
    mut v_b_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
    mut v___y_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3215_: usize = 0;
    let mut v_i_boxed_3216_: usize = 0;
    let mut v_res_3217_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3215_ = lean_unbox_usize(v_sz_3207_);
    lean_dec(v_sz_3207_);
    v_i_boxed_3216_ = lean_unbox_usize(v_i_3208_);
    lean_dec(v_i_3208_);
    v_res_3217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(v_as_3206_, v_sz_boxed_3215_, v_i_boxed_3216_, v_b_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
    lean_dec(v___y_3213_);
    lean_dec_ref(v___y_3212_);
    lean_dec(v___y_3211_);
    lean_dec_ref(v___y_3210_);
    lean_dec_ref(v_as_3206_);
    return v_res_3217_;
}
pub unsafe fn l_Lean_Meta_Simp_mkDiagMessages___lam__0(mut v_x_3218_: *mut LeanObject) -> u8 {
    let mut v___x_3219_: u8 = 0;
    v___x_3219_ = 1;
    return v___x_3219_;
}
pub unsafe fn l_Lean_Meta_Simp_mkDiagMessages___lam__0___boxed(
    mut v_x_3220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3221_: u8 = 0;
    let mut v_r_3222_: *mut LeanObject = core::ptr::null_mut();
    v_res_3221_ = l_Lean_Meta_Simp_mkDiagMessages___lam__0(v_x_3220_);
    lean_dec(v_x_3220_);
    v_r_3222_ = lean_box((v_res_3221_) as usize);
    return v_r_3222_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkDiagMessages___closed__7() -> *mut LeanObject {
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    v___x_3231_ = l_Lean_Meta_Simp_mkDiagMessages___closed__6;
    v___x_3232_ = l_Lean_MessageData_ofFormat(v___x_3231_);
    return v___x_3232_;
}
pub unsafe fn l_Lean_Meta_Simp_mkDiagMessages(
    mut v_diag_3233_: *mut LeanObject,
    mut v_a_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
    mut v_a_3236_: *mut LeanObject,
    mut v_a_3237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedThmCounter_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_triedThmCounter_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrThmCounter_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmsWithBadKeys_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___y_3262_: u8 = 0;
    let mut v___x_3263_: u8 = 0;
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: u8 = 0;
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: u8 = 0;
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: u8 = 0;
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v_a_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_a_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut v_a_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3309_: u8 = 0;
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_a_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_usedThmCounter_3239_ = lean_ctor_get(v_diag_3233_, 0);
                v_triedThmCounter_3240_ = lean_ctor_get(v_diag_3233_, 1);
                v_congrThmCounter_3241_ = lean_ctor_get(v_diag_3233_, 2);
                v_thmsWithBadKeys_3242_ = lean_ctor_get(v_diag_3233_, 3);
                v___x_3243_ = lean_box(0);
                v___x_3244_ = l_Lean_Meta_Simp_mkSimpDiagSummary(
                    v_usedThmCounter_3239_,
                    v___x_3243_,
                    v_a_3234_,
                    v_a_3235_,
                    v_a_3236_,
                    v_a_3237_,
                );
                if lean_obj_tag(v___x_3244_) == 0 {
                    v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
                    lean_inc(v_a_3245_);
                    lean_dec_ref_known(v___x_3244_, 1);
                    lean_inc_ref(v_usedThmCounter_3239_);
                    v___x_3246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3246_, 0, v_usedThmCounter_3239_);
                    v___x_3247_ = l_Lean_Meta_Simp_mkSimpDiagSummary(
                        v_triedThmCounter_3240_,
                        v___x_3246_,
                        v_a_3234_,
                        v_a_3235_,
                        v_a_3236_,
                        v_a_3237_,
                    );
                    lean_dec_ref_known(v___x_3246_, 1);
                    if lean_obj_tag(v___x_3247_) == 0 {
                        v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
                        lean_inc(v_a_3248_);
                        lean_dec_ref_known(v___x_3247_, 1);
                        v___f_3249_ = l_Lean_Meta_Simp_mkDiagMessages___closed__0;
                        v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2;
                        v___x_3251_ = l_Lean_Meta_mkDiagSummary(
                            v___x_3250_,
                            v_congrThmCounter_3241_,
                            v___f_3249_,
                            v_a_3234_,
                            v_a_3235_,
                            v_a_3236_,
                            v_a_3237_,
                        );
                        if lean_obj_tag(v___x_3251_) == 0 {
                            v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
                            v_isSharedCheck_3297_ = (!lean_is_exclusive(v___x_3251_)) as u8;
                            if v_isSharedCheck_3297_ == 0 {
                                v___x_3254_ = v___x_3251_;
                                v_isShared_3255_ = v_isSharedCheck_3297_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3252_);
                                lean_dec(v___x_3251_);
                                v___x_3254_ = lean_box(0);
                                v_isShared_3255_ = v_isSharedCheck_3297_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3248_);
                            lean_dec(v_a_3245_);
                            v_a_3298_ = lean_ctor_get(v___x_3251_, 0);
                            v_isSharedCheck_3305_ = (!lean_is_exclusive(v___x_3251_)) as u8;
                            if v_isSharedCheck_3305_ == 0 {
                                v___x_3300_ = v___x_3251_;
                                v_isShared_3301_ = v_isSharedCheck_3305_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_3298_);
                                lean_dec(v___x_3251_);
                                v___x_3300_ = lean_box(0);
                                v_isShared_3301_ = v_isSharedCheck_3305_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3245_);
                        v_a_3306_ = lean_ctor_get(v___x_3247_, 0);
                        v_isSharedCheck_3313_ = (!lean_is_exclusive(v___x_3247_)) as u8;
                        if v_isSharedCheck_3313_ == 0 {
                            v___x_3308_ = v___x_3247_;
                            v_isShared_3309_ = v_isSharedCheck_3313_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3306_);
                            lean_dec(v___x_3247_);
                            v___x_3308_ = lean_box(0);
                            v_isShared_3309_ = v_isSharedCheck_3313_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v_a_3314_ = lean_ctor_get(v___x_3244_, 0);
                    v_isSharedCheck_3321_ = (!lean_is_exclusive(v___x_3244_)) as u8;
                    if v_isSharedCheck_3321_ == 0 {
                        v___x_3316_ = v___x_3244_;
                        v_isShared_3317_ = v_isSharedCheck_3321_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3314_);
                        lean_dec(v___x_3244_);
                        v___x_3316_ = lean_box(0);
                        v_isShared_3317_ = v_isSharedCheck_3321_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3256_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(v_thmsWithBadKeys_3242_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
                if lean_obj_tag(v___x_3256_) == 0 {
                    v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
                    v_isSharedCheck_3288_ = (!lean_is_exclusive(v___x_3256_)) as u8;
                    if v_isSharedCheck_3288_ == 0 {
                        v___x_3259_ = v___x_3256_;
                        v_isShared_3260_ = v_isSharedCheck_3288_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3257_);
                        lean_dec(v___x_3256_);
                        v___x_3259_ = lean_box(0);
                        v_isShared_3260_ = v_isSharedCheck_3288_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3254_);
                    lean_dec(v_a_3252_);
                    lean_dec(v_a_3248_);
                    lean_dec(v_a_3245_);
                    v_a_3289_ = lean_ctor_get(v___x_3256_, 0);
                    v_isSharedCheck_3296_ = (!lean_is_exclusive(v___x_3256_)) as u8;
                    if v_isSharedCheck_3296_ == 0 {
                        v___x_3291_ = v___x_3256_;
                        v_isShared_3292_ = v_isSharedCheck_3296_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3289_);
                        lean_dec(v___x_3256_);
                        v___x_3291_ = lean_box(0);
                        v_isShared_3292_ = v_isSharedCheck_3296_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3286_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_3245_);
                if v___x_3286_ == 0 {
                    v___y_3279_ = v___x_3286_;
                    state = 5;
                    continue;
                } else {
                    v___x_3287_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_3248_);
                    v___y_3279_ = v___x_3287_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_3263_ = 1;
                v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                v___x_3265_ = l_Lean_Meta_Simp_mkDiagMessages___closed__1;
                v___x_3266_ = l_Lean_Meta_appendSection(
                    v___x_3264_,
                    v___x_3250_,
                    v___x_3265_,
                    v_a_3245_,
                    v___x_3263_,
                );
                v___x_3267_ = l_Lean_Meta_Simp_mkDiagMessages___closed__2;
                v___x_3268_ = l_Lean_Meta_appendSection(
                    v___x_3266_,
                    v___x_3250_,
                    v___x_3267_,
                    v_a_3248_,
                    v___x_3263_,
                );
                v___x_3269_ = l_Lean_Meta_Simp_mkDiagMessages___closed__3;
                v___x_3270_ = l_Lean_Meta_appendSection(
                    v___x_3268_,
                    v___x_3250_,
                    v___x_3269_,
                    v_a_3252_,
                    v___x_3263_,
                );
                v___x_3271_ = l_Lean_Meta_Simp_mkDiagMessages___closed__4;
                v___x_3272_ = l_Lean_Meta_appendSection(
                    v___x_3270_,
                    v___x_3250_,
                    v___x_3271_,
                    v_a_3257_,
                    v___y_3262_,
                );
                v___x_3273_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkDiagMessages___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkDiagMessages___closed__7_once),
                    _init_l_Lean_Meta_Simp_mkDiagMessages___closed__7,
                );
                v___x_3274_ = lean_array_push(v___x_3272_, v___x_3273_);
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 0, v___x_3274_);
                    v___x_3276_ = v___x_3259_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
                    v___x_3276_ = v_reuseFailAlloc_3277_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3276_;
            }
            5 => {
                if v___y_3279_ == 0 {
                    lean_del_object(v___x_3254_);
                    v___y_3262_ = v___y_3279_;
                    state = 3;
                    continue;
                } else {
                    v___x_3280_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_3252_);
                    if v___x_3280_ == 0 {
                        lean_del_object(v___x_3254_);
                        v___y_3262_ = v___x_3280_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3281_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_3257_);
                        if v___x_3281_ == 0 {
                            lean_del_object(v___x_3254_);
                            v___y_3262_ = v___x_3281_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_3259_);
                            lean_dec(v_a_3257_);
                            lean_dec(v_a_3252_);
                            lean_dec(v_a_3248_);
                            lean_dec(v_a_3245_);
                            v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0;
                            if v_isShared_3255_ == 0 {
                                lean_ctor_set(v___x_3254_, 0, v___x_3282_);
                                v___x_3284_ = v___x_3254_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
                                v___x_3284_ = v_reuseFailAlloc_3285_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                return v___x_3284_;
            }
            7 => {
                if v_isShared_3292_ == 0 {
                    v___x_3294_ = v___x_3291_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
                    v___x_3294_ = v_reuseFailAlloc_3295_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3294_;
            }
            9 => {
                if v_isShared_3301_ == 0 {
                    v___x_3303_ = v___x_3300_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
                    v___x_3303_ = v_reuseFailAlloc_3304_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3303_;
            }
            11 => {
                if v_isShared_3309_ == 0 {
                    v___x_3311_ = v___x_3308_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
                    v___x_3311_ = v_reuseFailAlloc_3312_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3311_;
            }
            13 => {
                if v_isShared_3317_ == 0 {
                    v___x_3319_ = v___x_3316_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
                    v___x_3319_ = v_reuseFailAlloc_3320_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_mkDiagMessages___boxed(
    mut v_diag_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
    mut v_a_3324_: *mut LeanObject,
    mut v_a_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
    mut v_a_3327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3328_: *mut LeanObject = core::ptr::null_mut();
    v_res_3328_ =
        l_Lean_Meta_Simp_mkDiagMessages(v_diag_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_);
    lean_dec(v_a_3326_);
    lean_dec_ref(v_a_3325_);
    lean_dec(v_a_3324_);
    lean_dec_ref(v_a_3323_);
    lean_dec_ref(v_diag_3322_);
    return v_res_3328_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(
    mut v___y_3337_: u8,
    mut v_suppressElabErrors_3338_: u8,
    mut v_x_3339_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3339_) == 1 {
        let mut v_pre_3340_: *mut LeanObject = core::ptr::null_mut();
        v_pre_3340_ = lean_ctor_get(v_x_3339_, 0);
        match lean_obj_tag(v_pre_3340_) {
            1 => {
                let mut v_pre_3341_: *mut LeanObject = core::ptr::null_mut();
                v_pre_3341_ = lean_ctor_get(v_pre_3340_, 0);
                match lean_obj_tag(v_pre_3341_) {
                    0 => {
                        let mut v_str_3342_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_3343_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3345_: u8 = 0;
                        v_str_3342_ = lean_ctor_get(v_x_3339_, 1);
                        v_str_3343_ = lean_ctor_get(v_pre_3340_, 1);
                        v___x_3344_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0;
                        v___x_3345_ = lean_string_dec_eq(v_str_3343_, v___x_3344_);
                        if v___x_3345_ == 0 {
                            let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3347_: u8 = 0;
                            v___x_3346_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1;
                            v___x_3347_ = lean_string_dec_eq(v_str_3343_, v___x_3346_);
                            if v___x_3347_ == 0 {
                                return v___y_3337_;
                            } else {
                                let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_3349_: u8 = 0;
                                v___x_3348_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2;
                                v___x_3349_ = lean_string_dec_eq(v_str_3342_, v___x_3348_);
                                if v___x_3349_ == 0 {
                                    return v___y_3337_;
                                } else {
                                    return v_suppressElabErrors_3338_;
                                }
                            }
                        } else {
                            let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3351_: u8 = 0;
                            v___x_3350_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3;
                            v___x_3351_ = lean_string_dec_eq(v_str_3342_, v___x_3350_);
                            if v___x_3351_ == 0 {
                                return v___y_3337_;
                            } else {
                                return v_suppressElabErrors_3338_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_3352_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_3352_ = lean_ctor_get(v_pre_3341_, 0);
                        if lean_obj_tag(v_pre_3352_) == 0 {
                            let mut v_str_3353_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_3354_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_3355_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3357_: u8 = 0;
                            v_str_3353_ = lean_ctor_get(v_x_3339_, 1);
                            v_str_3354_ = lean_ctor_get(v_pre_3340_, 1);
                            v_str_3355_ = lean_ctor_get(v_pre_3341_, 1);
                            v___x_3356_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4;
                            v___x_3357_ = lean_string_dec_eq(v_str_3355_, v___x_3356_);
                            if v___x_3357_ == 0 {
                                return v___y_3337_;
                            } else {
                                let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_3359_: u8 = 0;
                                v___x_3358_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5;
                                v___x_3359_ = lean_string_dec_eq(v_str_3354_, v___x_3358_);
                                if v___x_3359_ == 0 {
                                    return v___y_3337_;
                                } else {
                                    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_3361_: u8 = 0;
                                    v___x_3360_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6;
                                    v___x_3361_ = lean_string_dec_eq(v_str_3353_, v___x_3360_);
                                    if v___x_3361_ == 0 {
                                        return v___y_3337_;
                                    } else {
                                        return v_suppressElabErrors_3338_;
                                    }
                                }
                            }
                        } else {
                            return v___y_3337_;
                        }
                    }
                    _ => {
                        return v___y_3337_;
                    }
                }
            }
            0 => {
                let mut v_str_3362_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3364_: u8 = 0;
                v_str_3362_ = lean_ctor_get(v_x_3339_, 1);
                v___x_3363_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7;
                v___x_3364_ = lean_string_dec_eq(v_str_3362_, v___x_3363_);
                if v___x_3364_ == 0 {
                    return v___y_3337_;
                } else {
                    return v_suppressElabErrors_3338_;
                }
            }
            _ => {
                return v___y_3337_;
            }
        }
    } else {
        return v___y_3337_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed(
    mut v___y_3365_: *mut LeanObject,
    mut v_suppressElabErrors_3366_: *mut LeanObject,
    mut v_x_3367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6413__boxed_3368_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3369_: u8 = 0;
    let mut v_res_3370_: u8 = 0;
    let mut v_r_3371_: *mut LeanObject = core::ptr::null_mut();
    v___y_6413__boxed_3368_ = (lean_unbox(v___y_3365_) as u8);
    v_suppressElabErrors_boxed_3369_ = (lean_unbox(v_suppressElabErrors_3366_) as u8);
    v_res_3370_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(v___y_6413__boxed_3368_, v_suppressElabErrors_boxed_3369_, v_x_3367_);
    lean_dec(v_x_3367_);
    v_r_3371_ = lean_box((v_res_3370_) as usize);
    return v_r_3371_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(
    mut v_opts_3372_: *mut LeanObject,
    mut v_opt_3373_: *mut LeanObject,
) -> u8 {
    let mut v_name_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    v_name_3374_ = lean_ctor_get(v_opt_3373_, 0);
    v_defValue_3375_ = lean_ctor_get(v_opt_3373_, 1);
    v_map_3376_ = lean_ctor_get(v_opts_3372_, 0);
    v___x_3377_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3376_,
            v_name_3374_,
        );
    if lean_obj_tag(v___x_3377_) == 0 {
        let mut v___x_3378_: u8 = 0;
        v___x_3378_ = (lean_unbox(v_defValue_3375_) as u8);
        return v___x_3378_;
    } else {
        let mut v_val_3379_: *mut LeanObject = core::ptr::null_mut();
        v_val_3379_ = lean_ctor_get(v___x_3377_, 0);
        lean_inc(v_val_3379_);
        lean_dec_ref_known(v___x_3377_, 1);
        if lean_obj_tag(v_val_3379_) == 1 {
            let mut v_v_3380_: u8 = 0;
            v_v_3380_ = lean_ctor_get_uint8(v_val_3379_, 0 as u32);
            lean_dec_ref_known(v_val_3379_, 0);
            return v_v_3380_;
        } else {
            let mut v___x_3381_: u8 = 0;
            lean_dec(v_val_3379_);
            v___x_3381_ = (lean_unbox(v_defValue_3375_) as u8);
            return v___x_3381_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_opts_3382_: *mut LeanObject,
    mut v_opt_3383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3384_: u8 = 0;
    let mut v_r_3385_: *mut LeanObject = core::ptr::null_mut();
    v_res_3384_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v_opts_3382_, v_opt_3383_);
    lean_dec_ref(v_opt_3383_);
    lean_dec_ref(v_opts_3382_);
    v_r_3385_ = lean_box((v_res_3384_) as usize);
    return v_r_3385_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(
    mut v_msgData_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    v___x_3392_ = lean_st_ref_get(v___y_3390_);
    v_env_3393_ = lean_ctor_get(v___x_3392_, 0);
    lean_inc_ref(v_env_3393_);
    lean_dec(v___x_3392_);
    v___x_3394_ = lean_st_ref_get(v___y_3388_);
    v_mctx_3395_ = lean_ctor_get(v___x_3394_, 0);
    lean_inc_ref(v_mctx_3395_);
    lean_dec(v___x_3394_);
    v_lctx_3396_ = lean_ctor_get(v___y_3387_, 2);
    v_options_3397_ = lean_ctor_get(v___y_3389_, 2);
    lean_inc_ref(v_options_3397_);
    lean_inc_ref(v_lctx_3396_);
    v___x_3398_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3398_, 0, v_env_3393_);
    lean_ctor_set(v___x_3398_, 1, v_mctx_3395_);
    lean_ctor_set(v___x_3398_, 2, v_lctx_3396_);
    lean_ctor_set(v___x_3398_, 3, v_options_3397_);
    v___x_3399_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3399_, 0, v___x_3398_);
    lean_ctor_set(v___x_3399_, 1, v_msgData_3386_);
    v___x_3400_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3400_, 0, v___x_3399_);
    return v___x_3400_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_msgData_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3407_: *mut LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v_msgData_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
    lean_dec(v___y_3405_);
    lean_dec_ref(v___y_3404_);
    lean_dec(v___y_3403_);
    lean_dec_ref(v___y_3402_);
    return v_res_3407_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(
    mut v_ref_3408_: *mut LeanObject,
    mut v_msgData_3409_: *mut LeanObject,
    mut v_severity_3410_: u8,
    mut v_isSilent_3411_: u8,
    mut v___y_3412_: *mut LeanObject,
    mut v___y_3413_: *mut LeanObject,
    mut v___y_3414_: *mut LeanObject,
    mut v___y_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3418_: u8 = 0;
    let mut v___y_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3420_: u8 = 0;
    let mut v___y_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut v___y_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3455_: u8 = 0;
    let mut v___y_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3457_: u8 = 0;
    let mut v___y_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3460_: u8 = 0;
    let mut v___y_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v___y_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3480_: u8 = 0;
    let mut v___y_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3482_: u8 = 0;
    let mut v___y_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3485_: u8 = 0;
    let mut v___y_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3492_: u8 = 0;
    let mut v___y_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3495_: u8 = 0;
    let mut v___y_3496_: u8 = 0;
    let mut v_ref_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: u8 = 0;
    let mut v___y_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3507_: u8 = 0;
    let mut v___y_3508_: u8 = 0;
    let mut v___y_3509_: u8 = 0;
    let mut v___y_3511_: u8 = 0;
    let mut v_fileName_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3516_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: u8 = 0;
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: u8 = 0;
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: u8 = 0;
    let mut v___x_3527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3501_ = 2;
                v___x_3526_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3410_, v___x_3501_);
                if v___x_3526_ == 0 {
                    v___y_3511_ = v___x_3526_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_3409_);
                    v___x_3527_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3409_);
                    v___y_3511_ = v___x_3527_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3427_ = lean_st_ref_take(v___y_3426_);
                v_currNamespace_3428_ = lean_ctor_get(v___y_3425_, 6);
                v_openDecls_3429_ = lean_ctor_get(v___y_3425_, 7);
                v_env_3430_ = lean_ctor_get(v___x_3427_, 0);
                v_nextMacroScope_3431_ = lean_ctor_get(v___x_3427_, 1);
                v_ngen_3432_ = lean_ctor_get(v___x_3427_, 2);
                v_auxDeclNGen_3433_ = lean_ctor_get(v___x_3427_, 3);
                v_traceState_3434_ = lean_ctor_get(v___x_3427_, 4);
                v_cache_3435_ = lean_ctor_get(v___x_3427_, 5);
                v_messages_3436_ = lean_ctor_get(v___x_3427_, 6);
                v_infoState_3437_ = lean_ctor_get(v___x_3427_, 7);
                v_snapshotTasks_3438_ = lean_ctor_get(v___x_3427_, 8);
                v_isSharedCheck_3452_ = (!lean_is_exclusive(v___x_3427_)) as u8;
                if v_isSharedCheck_3452_ == 0 {
                    v___x_3440_ = v___x_3427_;
                    v_isShared_3441_ = v_isSharedCheck_3452_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3438_);
                    lean_inc(v_infoState_3437_);
                    lean_inc(v_messages_3436_);
                    lean_inc(v_cache_3435_);
                    lean_inc(v_traceState_3434_);
                    lean_inc(v_auxDeclNGen_3433_);
                    lean_inc(v_ngen_3432_);
                    lean_inc(v_nextMacroScope_3431_);
                    lean_inc(v_env_3430_);
                    lean_dec(v___x_3427_);
                    v___x_3440_ = lean_box(0);
                    v_isShared_3441_ = v_isSharedCheck_3452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_3429_);
                lean_inc(v_currNamespace_3428_);
                v___x_3442_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3442_, 0, v_currNamespace_3428_);
                lean_ctor_set(v___x_3442_, 1, v_openDecls_3429_);
                v___x_3443_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3443_, 0, v___x_3442_);
                lean_ctor_set(v___x_3443_, 1, v___y_3424_);
                lean_inc_ref(v___y_3422_);
                lean_inc_ref(v___y_3419_);
                v___x_3444_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_3444_, 0, v___y_3419_);
                lean_ctor_set(v___x_3444_, 1, v___y_3421_);
                lean_ctor_set(v___x_3444_, 2, v___y_3423_);
                lean_ctor_set(v___x_3444_, 3, v___y_3422_);
                lean_ctor_set(v___x_3444_, 4, v___x_3443_);
                lean_ctor_set_uint8(
                    v___x_3444_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_3420_,
                );
                lean_ctor_set_uint8(
                    v___x_3444_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_3418_,
                );
                lean_ctor_set_uint8(
                    v___x_3444_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3411_,
                );
                v___x_3445_ = l_Lean_MessageLog_add(v___x_3444_, v_messages_3436_);
                if v_isShared_3441_ == 0 {
                    lean_ctor_set(v___x_3440_, 6, v___x_3445_);
                    v___x_3447_ = v___x_3440_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_env_3430_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_nextMacroScope_3431_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_ngen_3432_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_auxDeclNGen_3433_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_traceState_3434_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 5, v_cache_3435_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 6, v___x_3445_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 7, v_infoState_3437_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 8, v_snapshotTasks_3438_);
                    v___x_3447_ = v_reuseFailAlloc_3451_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3448_ = lean_st_ref_set(v___y_3426_, v___x_3447_);
                v___x_3449_ = lean_box(0);
                v___x_3450_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3450_, 0, v___x_3449_);
                return v___x_3450_;
            }
            4 => {
                v___x_3462_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3409_,
                    );
                v___x_3463_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v___x_3462_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
                v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
                v_isSharedCheck_3477_ = (!lean_is_exclusive(v___x_3463_)) as u8;
                if v_isSharedCheck_3477_ == 0 {
                    v___x_3466_ = v___x_3463_;
                    v_isShared_3467_ = v_isSharedCheck_3477_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_3464_);
                    lean_dec(v___x_3463_);
                    v___x_3466_ = lean_box(0);
                    v_isShared_3467_ = v_isSharedCheck_3477_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_3459_, 2);
                v___x_3468_ = l_Lean_FileMap_toPosition(v___y_3459_, v___y_3458_);
                lean_dec(v___y_3458_);
                v___x_3469_ = l_Lean_FileMap_toPosition(v___y_3459_, v___y_3461_);
                lean_dec(v___y_3461_);
                v___x_3470_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3470_, 0, v___x_3469_);
                v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4;
                if v___y_3460_ == 0 {
                    lean_del_object(v___x_3466_);
                    lean_dec_ref(v___y_3454_);
                    v___y_3418_ = v___y_3455_;
                    v___y_3419_ = v___y_3456_;
                    v___y_3420_ = v___y_3457_;
                    v___y_3421_ = v___x_3468_;
                    v___y_3422_ = v___x_3471_;
                    v___y_3423_ = v___x_3470_;
                    v___y_3424_ = v_a_3464_;
                    v___y_3425_ = v___y_3414_;
                    v___y_3426_ = v___y_3415_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3464_);
                    v___x_3472_ = l_Lean_MessageData_hasTag(v___y_3454_, v_a_3464_);
                    if v___x_3472_ == 0 {
                        lean_dec_ref_known(v___x_3470_, 1);
                        lean_dec_ref(v___x_3468_);
                        lean_dec(v_a_3464_);
                        v___x_3473_ = lean_box(0);
                        if v_isShared_3467_ == 0 {
                            lean_ctor_set(v___x_3466_, 0, v___x_3473_);
                            v___x_3475_ = v___x_3466_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
                            v___x_3475_ = v_reuseFailAlloc_3476_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3466_);
                        v___y_3418_ = v___y_3455_;
                        v___y_3419_ = v___y_3456_;
                        v___y_3420_ = v___y_3457_;
                        v___y_3421_ = v___x_3468_;
                        v___y_3422_ = v___x_3471_;
                        v___y_3423_ = v___x_3470_;
                        v___y_3424_ = v_a_3464_;
                        v___y_3425_ = v___y_3414_;
                        v___y_3426_ = v___y_3415_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3475_;
            }
            7 => {
                v___x_3487_ = l_Lean_Syntax_getTailPos_x3f(v___y_3483_, v___y_3482_);
                lean_dec(v___y_3483_);
                if lean_obj_tag(v___x_3487_) == 0 {
                    lean_inc(v___y_3486_);
                    v___y_3454_ = v___y_3479_;
                    v___y_3455_ = v___y_3480_;
                    v___y_3456_ = v___y_3481_;
                    v___y_3457_ = v___y_3482_;
                    v___y_3458_ = v___y_3486_;
                    v___y_3459_ = v___y_3484_;
                    v___y_3460_ = v___y_3485_;
                    v___y_3461_ = v___y_3486_;
                    state = 4;
                    continue;
                } else {
                    v_val_3488_ = lean_ctor_get(v___x_3487_, 0);
                    lean_inc(v_val_3488_);
                    lean_dec_ref_known(v___x_3487_, 1);
                    v___y_3454_ = v___y_3479_;
                    v___y_3455_ = v___y_3480_;
                    v___y_3456_ = v___y_3481_;
                    v___y_3457_ = v___y_3482_;
                    v___y_3458_ = v___y_3486_;
                    v___y_3459_ = v___y_3484_;
                    v___y_3460_ = v___y_3485_;
                    v___y_3461_ = v_val_3488_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3497_ = l_Lean_replaceRef(v_ref_3408_, v___y_3494_);
                v___x_3498_ = l_Lean_Syntax_getPos_x3f(v_ref_3497_, v___y_3492_);
                if lean_obj_tag(v___x_3498_) == 0 {
                    v___x_3499_ = lean_unsigned_to_nat(0);
                    v___y_3479_ = v___y_3490_;
                    v___y_3480_ = v___y_3496_;
                    v___y_3481_ = v___y_3491_;
                    v___y_3482_ = v___y_3492_;
                    v___y_3483_ = v_ref_3497_;
                    v___y_3484_ = v___y_3493_;
                    v___y_3485_ = v___y_3495_;
                    v___y_3486_ = v___x_3499_;
                    state = 7;
                    continue;
                } else {
                    v_val_3500_ = lean_ctor_get(v___x_3498_, 0);
                    lean_inc(v_val_3500_);
                    lean_dec_ref_known(v___x_3498_, 1);
                    v___y_3479_ = v___y_3490_;
                    v___y_3480_ = v___y_3496_;
                    v___y_3481_ = v___y_3491_;
                    v___y_3482_ = v___y_3492_;
                    v___y_3483_ = v_ref_3497_;
                    v___y_3484_ = v___y_3493_;
                    v___y_3485_ = v___y_3495_;
                    v___y_3486_ = v_val_3500_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3509_ == 0 {
                    v___y_3490_ = v___y_3504_;
                    v___y_3491_ = v___y_3503_;
                    v___y_3492_ = v___y_3508_;
                    v___y_3493_ = v___y_3505_;
                    v___y_3494_ = v___y_3506_;
                    v___y_3495_ = v___y_3507_;
                    v___y_3496_ = v_severity_3410_;
                    state = 8;
                    continue;
                } else {
                    v___y_3490_ = v___y_3504_;
                    v___y_3491_ = v___y_3503_;
                    v___y_3492_ = v___y_3508_;
                    v___y_3493_ = v___y_3505_;
                    v___y_3494_ = v___y_3506_;
                    v___y_3495_ = v___y_3507_;
                    v___y_3496_ = v___x_3501_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3511_ == 0 {
                    v_fileName_3512_ = lean_ctor_get(v___y_3414_, 0);
                    v_fileMap_3513_ = lean_ctor_get(v___y_3414_, 1);
                    v_options_3514_ = lean_ctor_get(v___y_3414_, 2);
                    v_ref_3515_ = lean_ctor_get(v___y_3414_, 5);
                    v_suppressElabErrors_3516_ = lean_ctor_get_uint8(
                        v___y_3414_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3517_ = lean_box((v___y_3511_) as usize);
                    v___x_3518_ = lean_box((v_suppressElabErrors_3516_) as usize);
                    v___f_3519_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_3519_, 0, v___x_3517_);
                    lean_closure_set(v___f_3519_, 1, v___x_3518_);
                    v___x_3520_ = 1;
                    v___x_3521_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3410_, v___x_3520_);
                    if v___x_3521_ == 0 {
                        v___y_3503_ = v_fileName_3512_;
                        v___y_3504_ = v___f_3519_;
                        v___y_3505_ = v_fileMap_3513_;
                        v___y_3506_ = v_ref_3515_;
                        v___y_3507_ = v_suppressElabErrors_3516_;
                        v___y_3508_ = v___y_3511_;
                        v___y_3509_ = v___x_3521_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3522_ = l_Lean_warningAsError;
                        v___x_3523_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v_options_3514_, v___x_3522_);
                        v___y_3503_ = v_fileName_3512_;
                        v___y_3504_ = v___f_3519_;
                        v___y_3505_ = v_fileMap_3513_;
                        v___y_3506_ = v_ref_3515_;
                        v___y_3507_ = v_suppressElabErrors_3516_;
                        v___y_3508_ = v___y_3511_;
                        v___y_3509_ = v___x_3523_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_3409_);
                    v___x_3524_ = lean_box(0);
                    v___x_3525_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3525_, 0, v___x_3524_);
                    return v___x_3525_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___boxed(
    mut v_ref_3528_: *mut LeanObject,
    mut v_msgData_3529_: *mut LeanObject,
    mut v_severity_3530_: *mut LeanObject,
    mut v_isSilent_3531_: *mut LeanObject,
    mut v___y_3532_: *mut LeanObject,
    mut v___y_3533_: *mut LeanObject,
    mut v___y_3534_: *mut LeanObject,
    mut v___y_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3537_: u8 = 0;
    let mut v_isSilent_boxed_3538_: u8 = 0;
    let mut v_res_3539_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3537_ = (lean_unbox(v_severity_3530_) as u8);
    v_isSilent_boxed_3538_ = (lean_unbox(v_isSilent_3531_) as u8);
    v_res_3539_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_3528_, v_msgData_3529_, v_severity_boxed_3537_, v_isSilent_boxed_3538_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
    lean_dec(v___y_3535_);
    lean_dec_ref(v___y_3534_);
    lean_dec(v___y_3533_);
    lean_dec_ref(v___y_3532_);
    lean_dec(v_ref_3528_);
    return v_res_3539_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(
    mut v_msgData_3540_: *mut LeanObject,
    mut v_severity_3541_: u8,
    mut v_isSilent_3542_: u8,
    mut v___y_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3548_ = lean_ctor_get(v___y_3545_, 5);
    v___x_3549_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_3548_, v_msgData_3540_, v_severity_3541_, v_isSilent_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
    return v___x_3549_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0___boxed(
    mut v_msgData_3550_: *mut LeanObject,
    mut v_severity_3551_: *mut LeanObject,
    mut v_isSilent_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3558_: u8 = 0;
    let mut v_isSilent_boxed_3559_: u8 = 0;
    let mut v_res_3560_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3558_ = (lean_unbox(v_severity_3551_) as u8);
    v_isSilent_boxed_3559_ = (lean_unbox(v_isSilent_3552_) as u8);
    v_res_3560_ =
        l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(
            v_msgData_3550_,
            v_severity_boxed_3558_,
            v_isSilent_boxed_3559_,
            v___y_3553_,
            v___y_3554_,
            v___y_3555_,
            v___y_3556_,
        );
    lean_dec(v___y_3556_);
    lean_dec_ref(v___y_3555_);
    lean_dec(v___y_3554_);
    lean_dec_ref(v___y_3553_);
    return v_res_3560_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(
    mut v_msgData_3561_: *mut LeanObject,
    mut v___y_3562_: *mut LeanObject,
    mut v___y_3563_: *mut LeanObject,
    mut v___y_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3567_: u8 = 0;
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    v___x_3567_ = 0;
    v___x_3568_ = 0;
    v___x_3569_ =
        l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(
            v_msgData_3561_,
            v___x_3567_,
            v___x_3568_,
            v___y_3562_,
            v___y_3563_,
            v___y_3564_,
            v___y_3565_,
        );
    return v___x_3569_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0___boxed(
    mut v_msgData_3570_: *mut LeanObject,
    mut v___y_3571_: *mut LeanObject,
    mut v___y_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
    mut v___y_3574_: *mut LeanObject,
    mut v___y_3575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3576_: *mut LeanObject = core::ptr::null_mut();
    v_res_3576_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(
        v_msgData_3570_,
        v___y_3571_,
        v___y_3572_,
        v___y_3573_,
        v___y_3574_,
    );
    lean_dec(v___y_3574_);
    lean_dec_ref(v___y_3573_);
    lean_dec(v___y_3572_);
    lean_dec_ref(v___y_3571_);
    return v_res_3576_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_reportDiag___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    v___x_3580_ = l_Lean_Meta_Simp_reportDiag___lam__0___closed__1;
    v___x_3581_ = l_Lean_MessageData_ofFormat(v___x_3580_);
    return v___x_3581_;
}
pub unsafe fn l_Lean_Meta_Simp_reportDiag___lam__0(
    mut v_diag_3582_: *mut LeanObject,
    mut v___y_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: f64 = 0.0;
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v_a_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3612_: u8 = 0;
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3588_ = l_Lean_Meta_Simp_mkDiagMessages(
                    v_diag_3582_,
                    v___y_3583_,
                    v___y_3584_,
                    v___y_3585_,
                    v___y_3586_,
                );
                if lean_obj_tag(v___x_3588_) == 0 {
                    v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
                    v_isSharedCheck_3608_ = (!lean_is_exclusive(v___x_3588_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v___x_3591_ = v___x_3588_;
                        v_isShared_3592_ = v_isSharedCheck_3608_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3589_);
                        lean_dec(v___x_3588_);
                        v___x_3591_ = lean_box(0);
                        v_isShared_3592_ = v_isSharedCheck_3608_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3609_ = lean_ctor_get(v___x_3588_, 0);
                    v_isSharedCheck_3616_ = (!lean_is_exclusive(v___x_3588_)) as u8;
                    if v_isSharedCheck_3616_ == 0 {
                        v___x_3611_ = v___x_3588_;
                        v_isShared_3612_ = v_isSharedCheck_3616_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3609_);
                        lean_dec(v___x_3588_);
                        v___x_3611_ = lean_box(0);
                        v_isShared_3612_ = v_isSharedCheck_3616_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3593_ = lean_array_get_size(v_a_3589_);
                v___x_3594_ = lean_unsigned_to_nat(0);
                v___x_3595_ = lean_nat_dec_eq(v___x_3593_, v___x_3594_);
                if v___x_3595_ == 0 {
                    lean_del_object(v___x_3591_);
                    v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2;
                    v___x_3597_ = lean_box(0);
                    v___x_3598_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
                    v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4;
                    v___x_3600_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v___x_3600_, 0, v___x_3596_);
                    lean_ctor_set(v___x_3600_, 1, v___x_3597_);
                    lean_ctor_set(v___x_3600_, 2, v___x_3599_);
                    lean_ctor_set_float(
                        v___x_3600_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_3598_,
                    );
                    lean_ctor_set_float(
                        v___x_3600_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_3598_,
                    );
                    lean_ctor_set_uint8(
                        v___x_3600_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v___x_3595_,
                    );
                    v___x_3601_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_reportDiag___lam__0___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_reportDiag___lam__0___closed__2_once
                        ),
                        _init_l_Lean_Meta_Simp_reportDiag___lam__0___closed__2,
                    );
                    v___x_3602_ = lean_alloc_ctor(9, 3, (0) as u32);
                    lean_ctor_set(v___x_3602_, 0, v___x_3600_);
                    lean_ctor_set(v___x_3602_, 1, v___x_3601_);
                    lean_ctor_set(v___x_3602_, 2, v_a_3589_);
                    v___x_3603_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(
                        v___x_3602_,
                        v___y_3583_,
                        v___y_3584_,
                        v___y_3585_,
                        v___y_3586_,
                    );
                    return v___x_3603_;
                } else {
                    lean_dec(v_a_3589_);
                    v___x_3604_ = lean_box(0);
                    if v_isShared_3592_ == 0 {
                        lean_ctor_set(v___x_3591_, 0, v___x_3604_);
                        v___x_3606_ = v___x_3591_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
                        v___x_3606_ = v_reuseFailAlloc_3607_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3606_;
            }
            3 => {
                if v_isShared_3612_ == 0 {
                    v___x_3614_ = v___x_3611_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
                    v___x_3614_ = v_reuseFailAlloc_3615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_reportDiag___lam__0___boxed(
    mut v_diag_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
    mut v___y_3619_: *mut LeanObject,
    mut v___y_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3623_: *mut LeanObject = core::ptr::null_mut();
    v_res_3623_ = l_Lean_Meta_Simp_reportDiag___lam__0(
        v_diag_3617_,
        v___y_3618_,
        v___y_3619_,
        v___y_3620_,
        v___y_3621_,
    );
    lean_dec(v___y_3621_);
    lean_dec_ref(v___y_3620_);
    lean_dec(v___y_3619_);
    lean_dec_ref(v___y_3618_);
    lean_dec_ref(v_diag_3617_);
    return v_res_3623_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(
    mut v___y_3624_: *mut LeanObject,
    mut v_isExporting_3625_: u8,
    mut v___x_3626_: *mut LeanObject,
    mut v___y_3627_: *mut LeanObject,
    mut v___x_3628_: *mut LeanObject,
    mut v_a_x3f_3629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v_unused_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut v_unused_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3631_ = lean_st_ref_take(v___y_3624_);
                v_env_3632_ = lean_ctor_get(v___x_3631_, 0);
                v_nextMacroScope_3633_ = lean_ctor_get(v___x_3631_, 1);
                v_ngen_3634_ = lean_ctor_get(v___x_3631_, 2);
                v_auxDeclNGen_3635_ = lean_ctor_get(v___x_3631_, 3);
                v_traceState_3636_ = lean_ctor_get(v___x_3631_, 4);
                v_messages_3637_ = lean_ctor_get(v___x_3631_, 6);
                v_infoState_3638_ = lean_ctor_get(v___x_3631_, 7);
                v_snapshotTasks_3639_ = lean_ctor_get(v___x_3631_, 8);
                v_isSharedCheck_3664_ = (!lean_is_exclusive(v___x_3631_)) as u8;
                if v_isSharedCheck_3664_ == 0 {
                    v_unused_3665_ = lean_ctor_get(v___x_3631_, 5);
                    lean_dec(v_unused_3665_);
                    v___x_3641_ = v___x_3631_;
                    v_isShared_3642_ = v_isSharedCheck_3664_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3639_);
                    lean_inc(v_infoState_3638_);
                    lean_inc(v_messages_3637_);
                    lean_inc(v_traceState_3636_);
                    lean_inc(v_auxDeclNGen_3635_);
                    lean_inc(v_ngen_3634_);
                    lean_inc(v_nextMacroScope_3633_);
                    lean_inc(v_env_3632_);
                    lean_dec(v___x_3631_);
                    v___x_3641_ = lean_box(0);
                    v_isShared_3642_ = v_isSharedCheck_3664_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3643_ = l_Lean_Environment_setExporting(v_env_3632_, v_isExporting_3625_);
                if v_isShared_3642_ == 0 {
                    lean_ctor_set(v___x_3641_, 5, v___x_3626_);
                    lean_ctor_set(v___x_3641_, 0, v___x_3643_);
                    v___x_3645_ = v___x_3641_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3643_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_nextMacroScope_3633_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_ngen_3634_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 3, v_auxDeclNGen_3635_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 4, v_traceState_3636_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 5, v___x_3626_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 6, v_messages_3637_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 7, v_infoState_3638_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 8, v_snapshotTasks_3639_);
                    v___x_3645_ = v_reuseFailAlloc_3663_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3646_ = lean_st_ref_set(v___y_3624_, v___x_3645_);
                v___x_3647_ = lean_st_ref_take(v___y_3627_);
                v_mctx_3648_ = lean_ctor_get(v___x_3647_, 0);
                v_zetaDeltaFVarIds_3649_ = lean_ctor_get(v___x_3647_, 2);
                v_postponed_3650_ = lean_ctor_get(v___x_3647_, 3);
                v_diag_3651_ = lean_ctor_get(v___x_3647_, 4);
                v_isSharedCheck_3661_ = (!lean_is_exclusive(v___x_3647_)) as u8;
                if v_isSharedCheck_3661_ == 0 {
                    v_unused_3662_ = lean_ctor_get(v___x_3647_, 1);
                    lean_dec(v_unused_3662_);
                    v___x_3653_ = v___x_3647_;
                    v_isShared_3654_ = v_isSharedCheck_3661_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_3651_);
                    lean_inc(v_postponed_3650_);
                    lean_inc(v_zetaDeltaFVarIds_3649_);
                    lean_inc(v_mctx_3648_);
                    lean_dec(v___x_3647_);
                    v___x_3653_ = lean_box(0);
                    v_isShared_3654_ = v_isSharedCheck_3661_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3654_ == 0 {
                    lean_ctor_set(v___x_3653_, 1, v___x_3628_);
                    v___x_3656_ = v___x_3653_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_mctx_3648_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 1, v___x_3628_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_zetaDeltaFVarIds_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_postponed_3650_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_diag_3651_);
                    v___x_3656_ = v_reuseFailAlloc_3660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3657_ = lean_st_ref_set(v___y_3627_, v___x_3656_);
                v___x_3658_ = lean_box(0);
                v___x_3659_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3659_, 0, v___x_3658_);
                return v___x_3659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0___boxed(
    mut v___y_3666_: *mut LeanObject,
    mut v_isExporting_3667_: *mut LeanObject,
    mut v___x_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
    mut v___x_3670_: *mut LeanObject,
    mut v_a_x3f_3671_: *mut LeanObject,
    mut v___y_3672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_3673_: u8 = 0;
    let mut v_res_3674_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3673_ = (lean_unbox(v_isExporting_3667_) as u8);
    v_res_3674_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_3666_, v_isExporting_boxed_3673_, v___x_3668_, v___y_3669_, v___x_3670_, v_a_x3f_3671_);
    lean_dec(v_a_x3f_3671_);
    lean_dec(v___y_3669_);
    lean_dec(v___y_3666_);
    return v_res_3674_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    v___x_3675_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3675_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3676_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0);
    v___x_3677_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3677_, 0, v___x_3676_);
    return v___x_3677_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    v___x_3678_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1);
    v___x_3679_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3679_, 0, v___x_3678_);
    lean_ctor_set(v___x_3679_, 1, v___x_3678_);
    return v___x_3679_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    v___x_3680_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1);
    v___x_3681_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3681_, 0, v___x_3680_);
    lean_ctor_set(v___x_3681_, 1, v___x_3680_);
    lean_ctor_set(v___x_3681_, 2, v___x_3680_);
    lean_ctor_set(v___x_3681_, 3, v___x_3680_);
    lean_ctor_set(v___x_3681_, 4, v___x_3680_);
    lean_ctor_set(v___x_3681_, 5, v___x_3680_);
    return v___x_3681_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(
    mut v_x_3682_: *mut LeanObject,
    mut v_isExporting_3683_: u8,
    mut v___y_3684_: *mut LeanObject,
    mut v___y_3685_: *mut LeanObject,
    mut v___y_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3691_: u8 = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3716_: u8 = 0;
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3731_: u8 = 0;
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_unused_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3738_: u8 = 0;
    let mut v_a_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3744_: u8 = 0;
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3748_: u8 = 0;
    let mut v_unused_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut v_unused_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v_unused_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3689_ = lean_st_ref_get(v___y_3687_);
                v_env_3690_ = lean_ctor_get(v___x_3689_, 0);
                lean_inc_ref(v_env_3690_);
                lean_dec(v___x_3689_);
                v_isExporting_3691_ = lean_ctor_get_uint8(
                    v_env_3690_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_3690_);
                v___x_3692_ = lean_st_ref_take(v___y_3687_);
                v_env_3693_ = lean_ctor_get(v___x_3692_, 0);
                v_nextMacroScope_3694_ = lean_ctor_get(v___x_3692_, 1);
                v_ngen_3695_ = lean_ctor_get(v___x_3692_, 2);
                v_auxDeclNGen_3696_ = lean_ctor_get(v___x_3692_, 3);
                v_traceState_3697_ = lean_ctor_get(v___x_3692_, 4);
                v_messages_3698_ = lean_ctor_get(v___x_3692_, 6);
                v_infoState_3699_ = lean_ctor_get(v___x_3692_, 7);
                v_snapshotTasks_3700_ = lean_ctor_get(v___x_3692_, 8);
                v_isSharedCheck_3754_ = (!lean_is_exclusive(v___x_3692_)) as u8;
                if v_isSharedCheck_3754_ == 0 {
                    v_unused_3755_ = lean_ctor_get(v___x_3692_, 5);
                    lean_dec(v_unused_3755_);
                    v___x_3702_ = v___x_3692_;
                    v_isShared_3703_ = v_isSharedCheck_3754_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3700_);
                    lean_inc(v_infoState_3699_);
                    lean_inc(v_messages_3698_);
                    lean_inc(v_traceState_3697_);
                    lean_inc(v_auxDeclNGen_3696_);
                    lean_inc(v_ngen_3695_);
                    lean_inc(v_nextMacroScope_3694_);
                    lean_inc(v_env_3693_);
                    lean_dec(v___x_3692_);
                    v___x_3702_ = lean_box(0);
                    v_isShared_3703_ = v_isSharedCheck_3754_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3704_ = l_Lean_Environment_setExporting(v_env_3693_, v_isExporting_3683_);
                v___x_3705_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2);
                if v_isShared_3703_ == 0 {
                    lean_ctor_set(v___x_3702_, 5, v___x_3705_);
                    lean_ctor_set(v___x_3702_, 0, v___x_3704_);
                    v___x_3707_ = v___x_3702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3704_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_nextMacroScope_3694_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 2, v_ngen_3695_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 3, v_auxDeclNGen_3696_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 4, v_traceState_3697_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 5, v___x_3705_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 6, v_messages_3698_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 7, v_infoState_3699_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 8, v_snapshotTasks_3700_);
                    v___x_3707_ = v_reuseFailAlloc_3753_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3708_ = lean_st_ref_set(v___y_3687_, v___x_3707_);
                v___x_3709_ = lean_st_ref_take(v___y_3685_);
                v_mctx_3710_ = lean_ctor_get(v___x_3709_, 0);
                v_zetaDeltaFVarIds_3711_ = lean_ctor_get(v___x_3709_, 2);
                v_postponed_3712_ = lean_ctor_get(v___x_3709_, 3);
                v_diag_3713_ = lean_ctor_get(v___x_3709_, 4);
                v_isSharedCheck_3751_ = (!lean_is_exclusive(v___x_3709_)) as u8;
                if v_isSharedCheck_3751_ == 0 {
                    v_unused_3752_ = lean_ctor_get(v___x_3709_, 1);
                    lean_dec(v_unused_3752_);
                    v___x_3715_ = v___x_3709_;
                    v_isShared_3716_ = v_isSharedCheck_3751_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_3713_);
                    lean_inc(v_postponed_3712_);
                    lean_inc(v_zetaDeltaFVarIds_3711_);
                    lean_inc(v_mctx_3710_);
                    lean_dec(v___x_3709_);
                    v___x_3715_ = lean_box(0);
                    v_isShared_3716_ = v_isSharedCheck_3751_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3717_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3);
                if v_isShared_3716_ == 0 {
                    lean_ctor_set(v___x_3715_, 1, v___x_3717_);
                    v___x_3719_ = v___x_3715_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_mctx_3710_);
                    lean_ctor_set(v_reuseFailAlloc_3750_, 1, v___x_3717_);
                    lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_zetaDeltaFVarIds_3711_);
                    lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_postponed_3712_);
                    lean_ctor_set(v_reuseFailAlloc_3750_, 4, v_diag_3713_);
                    v___x_3719_ = v_reuseFailAlloc_3750_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3720_ = lean_st_ref_set(v___y_3685_, v___x_3719_);
                lean_inc(v___y_3687_);
                lean_inc_ref(v___y_3686_);
                lean_inc(v___y_3685_);
                lean_inc_ref(v___y_3684_);
                v_r_3721_ = lean_apply_5(
                    v_x_3682_,
                    v___y_3684_,
                    v___y_3685_,
                    v___y_3686_,
                    v___y_3687_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_3721_) == 0 {
                    v_a_3722_ = lean_ctor_get(v_r_3721_, 0);
                    v_isSharedCheck_3738_ = (!lean_is_exclusive(v_r_3721_)) as u8;
                    if v_isSharedCheck_3738_ == 0 {
                        v___x_3724_ = v_r_3721_;
                        v_isShared_3725_ = v_isSharedCheck_3738_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3722_);
                        lean_dec(v_r_3721_);
                        v___x_3724_ = lean_box(0);
                        v_isShared_3725_ = v_isSharedCheck_3738_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3739_ = lean_ctor_get(v_r_3721_, 0);
                    lean_inc(v_a_3739_);
                    lean_dec_ref_known(v_r_3721_, 1);
                    v___x_3740_ = lean_box(0);
                    v___x_3741_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_3687_, v_isExporting_3691_, v___x_3705_, v___y_3685_, v___x_3717_, v___x_3740_);
                    v_isSharedCheck_3748_ = (!lean_is_exclusive(v___x_3741_)) as u8;
                    if v_isSharedCheck_3748_ == 0 {
                        v_unused_3749_ = lean_ctor_get(v___x_3741_, 0);
                        lean_dec(v_unused_3749_);
                        v___x_3743_ = v___x_3741_;
                        v_isShared_3744_ = v_isSharedCheck_3748_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_3741_);
                        v___x_3743_ = lean_box(0);
                        v_isShared_3744_ = v_isSharedCheck_3748_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_3722_);
                if v_isShared_3725_ == 0 {
                    lean_ctor_set_tag(v___x_3724_, 1);
                    v___x_3727_ = v___x_3724_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3722_);
                    v___x_3727_ = v_reuseFailAlloc_3737_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3728_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_3687_, v_isExporting_3691_, v___x_3705_, v___y_3685_, v___x_3717_, v___x_3727_);
                lean_dec_ref(v___x_3727_);
                v_isSharedCheck_3735_ = (!lean_is_exclusive(v___x_3728_)) as u8;
                if v_isSharedCheck_3735_ == 0 {
                    v_unused_3736_ = lean_ctor_get(v___x_3728_, 0);
                    lean_dec(v_unused_3736_);
                    v___x_3730_ = v___x_3728_;
                    v_isShared_3731_ = v_isSharedCheck_3735_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v___x_3728_);
                    v___x_3730_ = lean_box(0);
                    v_isShared_3731_ = v_isSharedCheck_3735_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3731_ == 0 {
                    lean_ctor_set(v___x_3730_, 0, v_a_3722_);
                    v___x_3733_ = v___x_3730_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3722_);
                    v___x_3733_ = v_reuseFailAlloc_3734_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3733_;
            }
            9 => {
                if v_isShared_3744_ == 0 {
                    lean_ctor_set_tag(v___x_3743_, 1);
                    lean_ctor_set(v___x_3743_, 0, v_a_3739_);
                    v___x_3746_ = v___x_3743_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3739_);
                    v___x_3746_ = v_reuseFailAlloc_3747_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___boxed(
    mut v_x_3756_: *mut LeanObject,
    mut v_isExporting_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
    mut v___y_3760_: *mut LeanObject,
    mut v___y_3761_: *mut LeanObject,
    mut v___y_3762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_3763_: u8 = 0;
    let mut v_res_3764_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3763_ = (lean_unbox(v_isExporting_3757_) as u8);
    v_res_3764_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_3756_, v_isExporting_boxed_3763_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
    lean_dec(v___y_3761_);
    lean_dec_ref(v___y_3760_);
    lean_dec(v___y_3759_);
    lean_dec_ref(v___y_3758_);
    return v_res_3764_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(
    mut v_x_3765_: *mut LeanObject,
    mut v_when_3766_: u8,
    mut v___y_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
    mut v___y_3769_: *mut LeanObject,
    mut v___y_3770_: *mut LeanObject,
) -> *mut LeanObject {
    if v_when_3766_ == 0 {
        let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_3770_);
        lean_inc_ref(v___y_3769_);
        lean_inc(v___y_3768_);
        lean_inc_ref(v___y_3767_);
        v___x_3772_ = lean_apply_5(
            v_x_3765_,
            v___y_3767_,
            v___y_3768_,
            v___y_3769_,
            v___y_3770_,
            lean_box(0),
        );
        return v___x_3772_;
    } else {
        let mut v___x_3773_: u8 = 0;
        let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
        v___x_3773_ = 0;
        v___x_3774_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_3765_, v___x_3773_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
        return v___x_3774_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg___boxed(
    mut v_x_3775_: *mut LeanObject,
    mut v_when_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
    mut v___y_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_3782_: u8 = 0;
    let mut v_res_3783_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_3782_ = (lean_unbox(v_when_3776_) as u8);
    v_res_3783_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(
        v_x_3775_,
        v_when_boxed_3782_,
        v___y_3777_,
        v___y_3778_,
        v___y_3779_,
        v___y_3780_,
    );
    lean_dec(v___y_3780_);
    lean_dec_ref(v___y_3779_);
    lean_dec(v___y_3778_);
    lean_dec_ref(v___y_3777_);
    return v_res_3783_;
}
pub unsafe fn l_Lean_Meta_Simp_reportDiag(
    mut v_diag_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
    mut v_a_3786_: *mut LeanObject,
    mut v_a_3787_: *mut LeanObject,
    mut v_a_3788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_a_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3807_: u8 = 0;
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3811_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3790_ = l_Lean_isDiagnosticsEnabled___redArg(v_a_3787_);
                if lean_obj_tag(v___x_3790_) == 0 {
                    v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
                    v_isSharedCheck_3803_ = (!lean_is_exclusive(v___x_3790_)) as u8;
                    if v_isSharedCheck_3803_ == 0 {
                        v___x_3793_ = v___x_3790_;
                        v_isShared_3794_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3791_);
                        lean_dec(v___x_3790_);
                        v___x_3793_ = lean_box(0);
                        v_isShared_3794_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_diag_3784_);
                    v_a_3804_ = lean_ctor_get(v___x_3790_, 0);
                    v_isSharedCheck_3811_ = (!lean_is_exclusive(v___x_3790_)) as u8;
                    if v_isSharedCheck_3811_ == 0 {
                        v___x_3806_ = v___x_3790_;
                        v_isShared_3807_ = v_isSharedCheck_3811_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3804_);
                        lean_dec(v___x_3790_);
                        v___x_3806_ = lean_box(0);
                        v_isShared_3807_ = v_isSharedCheck_3811_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3795_ = (lean_unbox(v_a_3791_) as u8);
                if v___x_3795_ == 0 {
                    lean_dec(v_a_3791_);
                    lean_dec_ref(v_diag_3784_);
                    v___x_3796_ = lean_box(0);
                    if v_isShared_3794_ == 0 {
                        lean_ctor_set(v___x_3793_, 0, v___x_3796_);
                        v___x_3798_ = v___x_3793_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
                        v___x_3798_ = v_reuseFailAlloc_3799_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3793_);
                    v___f_3800_ = lean_alloc_closure(
                        l_Lean_Meta_Simp_reportDiag___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    lean_closure_set(v___f_3800_, 0, v_diag_3784_);
                    v___x_3801_ = (lean_unbox(v_a_3791_) as u8);
                    lean_dec(v_a_3791_);
                    v___x_3802_ =
                        l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(
                            v___f_3800_,
                            v___x_3801_,
                            v_a_3785_,
                            v_a_3786_,
                            v_a_3787_,
                            v_a_3788_,
                        );
                    return v___x_3802_;
                }
            }
            2 => {
                return v___x_3798_;
            }
            3 => {
                if v_isShared_3807_ == 0 {
                    v___x_3809_ = v___x_3806_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
                    v___x_3809_ = v_reuseFailAlloc_3810_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_reportDiag___boxed(
    mut v_diag_3812_: *mut LeanObject,
    mut v_a_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3818_: *mut LeanObject = core::ptr::null_mut();
    v_res_3818_ =
        l_Lean_Meta_Simp_reportDiag(v_diag_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
    lean_dec(v_a_3816_);
    lean_dec_ref(v_a_3815_);
    lean_dec(v_a_3814_);
    lean_dec_ref(v_a_3813_);
    return v_res_3818_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(
    mut v_00_u03b1_3819_: *mut LeanObject,
    mut v_x_3820_: *mut LeanObject,
    mut v_isExporting_3821_: u8,
    mut v___y_3822_: *mut LeanObject,
    mut v___y_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_3820_, v_isExporting_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
    return v___x_3827_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___boxed(
    mut v_00_u03b1_3828_: *mut LeanObject,
    mut v_x_3829_: *mut LeanObject,
    mut v_isExporting_3830_: *mut LeanObject,
    mut v___y_3831_: *mut LeanObject,
    mut v___y_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
    mut v___y_3834_: *mut LeanObject,
    mut v___y_3835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_3836_: u8 = 0;
    let mut v_res_3837_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3836_ = (lean_unbox(v_isExporting_3830_) as u8);
    v_res_3837_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(v_00_u03b1_3828_, v_x_3829_, v_isExporting_boxed_3836_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
    lean_dec(v___y_3834_);
    lean_dec_ref(v___y_3833_);
    lean_dec(v___y_3832_);
    lean_dec_ref(v___y_3831_);
    return v_res_3837_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(
    mut v_00_u03b1_3838_: *mut LeanObject,
    mut v_x_3839_: *mut LeanObject,
    mut v_when_3840_: u8,
    mut v___y_3841_: *mut LeanObject,
    mut v___y_3842_: *mut LeanObject,
    mut v___y_3843_: *mut LeanObject,
    mut v___y_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    v___x_3846_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(
        v_x_3839_,
        v_when_3840_,
        v___y_3841_,
        v___y_3842_,
        v___y_3843_,
        v___y_3844_,
    );
    return v___x_3846_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___boxed(
    mut v_00_u03b1_3847_: *mut LeanObject,
    mut v_x_3848_: *mut LeanObject,
    mut v_when_3849_: *mut LeanObject,
    mut v___y_3850_: *mut LeanObject,
    mut v___y_3851_: *mut LeanObject,
    mut v___y_3852_: *mut LeanObject,
    mut v___y_3853_: *mut LeanObject,
    mut v___y_3854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_3855_: u8 = 0;
    let mut v_res_3856_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_3855_ = (lean_unbox(v_when_3849_) as u8);
    v_res_3856_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(
        v_00_u03b1_3847_,
        v_x_3848_,
        v_when_boxed_3855_,
        v___y_3850_,
        v___y_3851_,
        v___y_3852_,
        v___y_3853_,
    );
    lean_dec(v___y_3853_);
    lean_dec_ref(v___y_3852_);
    lean_dec(v___y_3851_);
    lean_dec_ref(v___y_3850_);
    return v_res_3856_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Diagnostics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Diagnostics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
}
