// Lean compiler output
// Module: Lean.Compiler.LCNF.SplitSCC
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Util.SCC
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_instInhabitedDecl_default;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_getPurity___redArg,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::SCC::{initialize_Lean_Util_SCC, runtime_initialize_Lean_Util_SCC};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__3: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__4_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__4_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__5_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__5_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__0_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__1_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__2_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31_spec__34___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31_spec__34___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31_spec__34___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31_spec__34___closed__0_value) as *mut LeanObject;
static mut l_Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_splitScc___closed__0_value: LeanStringObject<9> =
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
        m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0],
    };
static mut l_Lean_Compiler_LCNF_splitScc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_splitScc___closed__1_value: LeanStringObject<9> =
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
        m_data: [115, 112, 108, 105, 116, 83, 67, 67, 0],
    };
static mut l_Lean_Compiler_LCNF_splitScc___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__1_value) as *mut LeanObject;
static l_Lean_Compiler_LCNF_splitScc___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__0_value) as *mut LeanObject,
        2042452093243897853 as *mut LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_splitScc___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__1_value) as *mut LeanObject,
        4937407396035962416 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_splitScc___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_splitScc___closed__3_value: LeanStringObject<6> =
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
static mut l_Lean_Compiler_LCNF_splitScc___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__3_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_splitScc___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__3_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_splitScc___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__4_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_splitScc___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_splitScc___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_splitScc___closed__6_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            83, 112, 108, 105, 116, 32, 83, 67, 67, 32, 105, 110, 116, 111, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_splitScc___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__6_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_splitScc___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_splitScc___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__0_value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 112, 108, 105, 116, 83, 67, 67, 0]};
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,7753942883574265752 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,14029221697601573521 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,6771966091838483156 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__0_value) as *mut LeanObject,4388185407386834078 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,5139750592187044391 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,7300555764246177622 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,14024027738857321639 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,7270833796633177498 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_splitScc___closed__0_value) as *mut LeanObject,1742140420951729160 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,6018253244088337441 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,10052823274279689816 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,((( 1807176231 as usize) << 1) | 1) as *mut LeanObject,5604627553429280338 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,14509882014254543005 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,17800082423809239805 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,2018301098310392592 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0___redArg(
    mut v_a_1375_: *mut LeanObject,
    mut v_x_1376_: *mut LeanObject,
) -> u8 {
    let mut v___x_1377_: u8 = 0;
    let mut v_key_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1376_) == 0 {
                    v___x_1377_ = 0;
                    return v___x_1377_;
                } else {
                    v_key_1378_ = lean_ctor_get(v_x_1376_, 0);
                    v_tail_1379_ = lean_ctor_get(v_x_1376_, 2);
                    v___x_1380_ = lean_name_eq(v_key_1378_, v_a_1375_);
                    if v___x_1380_ == 0 {
                        v_x_1376_ = v_tail_1379_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1380_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0___redArg___boxed(
    mut v_a_1382_: *mut LeanObject,
    mut v_x_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1384_: u8 = 0;
    let mut v_r_1385_: *mut LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0___redArg(v_a_1382_, v_x_1383_);
    lean_dec(v_x_1383_);
    lean_dec(v_a_1382_);
    v_r_1385_ = lean_box((v_res_1384_) as usize);
    return v_r_1385_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: u64 = 0;
    v___x_1386_ = lean_unsigned_to_nat(1723);
    v___x_1387_ = lean_uint64_of_nat(v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg(
    mut v_m_1388_: *mut LeanObject,
    mut v_a_1389_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1393_: u64 = 0;
    let mut v___x_1394_: u64 = 0;
    let mut v___x_1395_: u64 = 0;
    let mut v_fold_1396_: u64 = 0;
    let mut v___x_1397_: u64 = 0;
    let mut v___x_1398_: u64 = 0;
    let mut v___x_1399_: u64 = 0;
    let mut v___x_1400_: usize = 0;
    let mut v___x_1401_: usize = 0;
    let mut v___x_1402_: usize = 0;
    let mut v___x_1403_: usize = 0;
    let mut v___x_1404_: usize = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: u64 = 0;
    let mut v_hash_1408_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1390_ = lean_ctor_get(v_m_1388_, 1);
                v___x_1391_ = lean_array_get_size(v_buckets_1390_);
                if lean_obj_tag(v_a_1389_) == 0 {
                    v___x_1407_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0);
                    v___y_1393_ = v___x_1407_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1408_ = lean_ctor_get_uint64(
                        v_a_1389_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1393_ = v_hash_1408_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1394_ = 32u64;
                v___x_1395_ = lean_uint64_shift_right(v___y_1393_, v___x_1394_);
                v_fold_1396_ = lean_uint64_xor(v___y_1393_, v___x_1395_);
                v___x_1397_ = 16u64;
                v___x_1398_ = lean_uint64_shift_right(v_fold_1396_, v___x_1397_);
                v___x_1399_ = lean_uint64_xor(v_fold_1396_, v___x_1398_);
                v___x_1400_ = lean_uint64_to_usize(v___x_1399_);
                v___x_1401_ = lean_usize_of_nat(v___x_1391_);
                v___x_1402_ = 1usize;
                v___x_1403_ = lean_usize_sub(v___x_1401_, v___x_1402_);
                v___x_1404_ = lean_usize_land(v___x_1400_, v___x_1403_);
                v___x_1405_ = lean_array_uget_borrowed(v_buckets_1390_, v___x_1404_);
                v___x_1406_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0___redArg(v_a_1389_, v___x_1405_);
                return v___x_1406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___boxed(
    mut v_m_1409_: *mut LeanObject,
    mut v_a_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1411_: u8 = 0;
    let mut v_r_1412_: *mut LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg(v_m_1409_, v_a_1410_);
    lean_dec(v_a_1410_);
    lean_dec_ref(v_m_1409_);
    v_r_1412_ = lean_box((v_res_1411_) as usize);
    return v_r_1412_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_x_1413_: *mut LeanObject,
    mut v_x_1414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: u64 = 0;
    let mut v___x_1424_: u64 = 0;
    let mut v___x_1425_: u64 = 0;
    let mut v_fold_1426_: u64 = 0;
    let mut v___x_1427_: u64 = 0;
    let mut v___x_1428_: u64 = 0;
    let mut v___x_1429_: u64 = 0;
    let mut v___x_1430_: usize = 0;
    let mut v___x_1431_: usize = 0;
    let mut v___x_1432_: usize = 0;
    let mut v___x_1433_: usize = 0;
    let mut v___x_1434_: usize = 0;
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u64 = 0;
    let mut v_hash_1442_: u64 = 0;
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1414_) == 0 {
                    return v_x_1413_;
                } else {
                    v_key_1415_ = lean_ctor_get(v_x_1414_, 0);
                    v_value_1416_ = lean_ctor_get(v_x_1414_, 1);
                    v_tail_1417_ = lean_ctor_get(v_x_1414_, 2);
                    v_isSharedCheck_1443_ = (!lean_is_exclusive(v_x_1414_)) as u8;
                    if v_isSharedCheck_1443_ == 0 {
                        v___x_1419_ = v_x_1414_;
                        v_isShared_1420_ = v_isSharedCheck_1443_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1417_);
                        lean_inc(v_value_1416_);
                        lean_inc(v_key_1415_);
                        lean_dec(v_x_1414_);
                        v___x_1419_ = lean_box(0);
                        v_isShared_1420_ = v_isSharedCheck_1443_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1421_ = lean_array_get_size(v_x_1413_);
                if lean_obj_tag(v_key_1415_) == 0 {
                    v___x_1441_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0);
                    v___y_1423_ = v___x_1441_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1442_ = lean_ctor_get_uint64(
                        v_key_1415_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1423_ = v_hash_1442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1424_ = 32u64;
                v___x_1425_ = lean_uint64_shift_right(v___y_1423_, v___x_1424_);
                v_fold_1426_ = lean_uint64_xor(v___y_1423_, v___x_1425_);
                v___x_1427_ = 16u64;
                v___x_1428_ = lean_uint64_shift_right(v_fold_1426_, v___x_1427_);
                v___x_1429_ = lean_uint64_xor(v_fold_1426_, v___x_1428_);
                v___x_1430_ = lean_uint64_to_usize(v___x_1429_);
                v___x_1431_ = lean_usize_of_nat(v___x_1421_);
                v___x_1432_ = 1usize;
                v___x_1433_ = lean_usize_sub(v___x_1431_, v___x_1432_);
                v___x_1434_ = lean_usize_land(v___x_1430_, v___x_1433_);
                v___x_1435_ = lean_array_uget_borrowed(v_x_1413_, v___x_1434_);
                lean_inc(v___x_1435_);
                if v_isShared_1420_ == 0 {
                    lean_ctor_set(v___x_1419_, 2, v___x_1435_);
                    v___x_1437_ = v___x_1419_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_key_1415_);
                    lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_value_1416_);
                    lean_ctor_set(v_reuseFailAlloc_1440_, 2, v___x_1435_);
                    v___x_1437_ = v_reuseFailAlloc_1440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1438_ = lean_array_uset(v_x_1413_, v___x_1434_, v___x_1437_);
                v_x_1413_ = v___x_1438_;
                v_x_1414_ = v_tail_1417_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2_spec__3___redArg(
    mut v_i_1444_: *mut LeanObject,
    mut v_source_1445_: *mut LeanObject,
    mut v_target_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v_es_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1447_ = lean_array_get_size(v_source_1445_);
                v___x_1448_ = lean_nat_dec_lt(v_i_1444_, v___x_1447_);
                if v___x_1448_ == 0 {
                    lean_dec_ref(v_source_1445_);
                    lean_dec(v_i_1444_);
                    return v_target_1446_;
                } else {
                    v_es_1449_ = lean_array_fget(v_source_1445_, v_i_1444_);
                    v___x_1450_ = lean_box(0);
                    v_source_1451_ = lean_array_fset(v_source_1445_, v_i_1444_, v___x_1450_);
                    v_target_1452_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2_spec__3_spec__5___redArg(v_target_1446_, v_es_1449_);
                    v___x_1453_ = lean_unsigned_to_nat(1);
                    v___x_1454_ = lean_nat_add(v_i_1444_, v___x_1453_);
                    lean_dec(v_i_1444_);
                    v_i_1444_ = v___x_1454_;
                    v_source_1445_ = v_source_1451_;
                    v_target_1446_ = v_target_1452_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2___redArg(
    mut v_data_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = lean_array_get_size(v_data_1456_);
    v___x_1458_ = lean_unsigned_to_nat(2);
    v_nbuckets_1459_ = lean_nat_mul(v___x_1457_, v___x_1458_);
    v___x_1460_ = lean_unsigned_to_nat(0);
    v___x_1461_ = lean_box(0);
    v___x_1462_ = lean_mk_array(v_nbuckets_1459_, v___x_1461_);
    v___x_1463_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2_spec__3___redArg(v___x_1460_, v_data_1456_, v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1___redArg(
    mut v_m_1464_: *mut LeanObject,
    mut v_a_1465_: *mut LeanObject,
    mut v_b_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: u64 = 0;
    let mut v___x_1472_: u64 = 0;
    let mut v___x_1473_: u64 = 0;
    let mut v_fold_1474_: u64 = 0;
    let mut v___x_1475_: u64 = 0;
    let mut v___x_1476_: u64 = 0;
    let mut v___x_1477_: u64 = 0;
    let mut v___x_1478_: usize = 0;
    let mut v___x_1479_: usize = 0;
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: usize = 0;
    let mut v___x_1482_: usize = 0;
    let mut v_bkt_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: u8 = 0;
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v_val_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1505_: u8 = 0;
    let mut v_unused_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u64 = 0;
    let mut v_hash_1509_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1467_ = lean_ctor_get(v_m_1464_, 0);
                v_buckets_1468_ = lean_ctor_get(v_m_1464_, 1);
                v___x_1469_ = lean_array_get_size(v_buckets_1468_);
                if lean_obj_tag(v_a_1465_) == 0 {
                    v___x_1508_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0);
                    v___y_1471_ = v___x_1508_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1509_ = lean_ctor_get_uint64(
                        v_a_1465_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1471_ = v_hash_1509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1472_ = 32u64;
                v___x_1473_ = lean_uint64_shift_right(v___y_1471_, v___x_1472_);
                v_fold_1474_ = lean_uint64_xor(v___y_1471_, v___x_1473_);
                v___x_1475_ = 16u64;
                v___x_1476_ = lean_uint64_shift_right(v_fold_1474_, v___x_1475_);
                v___x_1477_ = lean_uint64_xor(v_fold_1474_, v___x_1476_);
                v___x_1478_ = lean_uint64_to_usize(v___x_1477_);
                v___x_1479_ = lean_usize_of_nat(v___x_1469_);
                v___x_1480_ = 1usize;
                v___x_1481_ = lean_usize_sub(v___x_1479_, v___x_1480_);
                v___x_1482_ = lean_usize_land(v___x_1478_, v___x_1481_);
                v_bkt_1483_ = lean_array_uget_borrowed(v_buckets_1468_, v___x_1482_);
                v___x_1484_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0___redArg(v_a_1465_, v_bkt_1483_);
                if v___x_1484_ == 0 {
                    lean_inc_ref(v_buckets_1468_);
                    lean_inc(v_size_1467_);
                    v_isSharedCheck_1505_ = (!lean_is_exclusive(v_m_1464_)) as u8;
                    if v_isSharedCheck_1505_ == 0 {
                        v_unused_1506_ = lean_ctor_get(v_m_1464_, 1);
                        lean_dec(v_unused_1506_);
                        v_unused_1507_ = lean_ctor_get(v_m_1464_, 0);
                        lean_dec(v_unused_1507_);
                        v___x_1486_ = v_m_1464_;
                        v_isShared_1487_ = v_isSharedCheck_1505_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_1464_);
                        v___x_1486_ = lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1505_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1466_);
                    lean_dec(v_a_1465_);
                    return v_m_1464_;
                }
            }
            2 => {
                v___x_1488_ = lean_unsigned_to_nat(1);
                v_size_x27_1489_ = lean_nat_add(v_size_1467_, v___x_1488_);
                lean_dec(v_size_1467_);
                lean_inc(v_bkt_1483_);
                v___x_1490_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1490_, 0, v_a_1465_);
                lean_ctor_set(v___x_1490_, 1, v_b_1466_);
                lean_ctor_set(v___x_1490_, 2, v_bkt_1483_);
                v_buckets_x27_1491_ = lean_array_uset(v_buckets_1468_, v___x_1482_, v___x_1490_);
                v___x_1492_ = lean_unsigned_to_nat(4);
                v___x_1493_ = lean_nat_mul(v_size_x27_1489_, v___x_1492_);
                v___x_1494_ = lean_unsigned_to_nat(3);
                v___x_1495_ = lean_nat_div(v___x_1493_, v___x_1494_);
                lean_dec(v___x_1493_);
                v___x_1496_ = lean_array_get_size(v_buckets_x27_1491_);
                v___x_1497_ = lean_nat_dec_le(v___x_1495_, v___x_1496_);
                lean_dec(v___x_1495_);
                if v___x_1497_ == 0 {
                    v_val_1498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2___redArg(v_buckets_x27_1491_);
                    if v_isShared_1487_ == 0 {
                        lean_ctor_set(v___x_1486_, 1, v_val_1498_);
                        lean_ctor_set(v___x_1486_, 0, v_size_x27_1489_);
                        v___x_1500_ = v___x_1486_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_size_x27_1489_);
                        lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_val_1498_);
                        v___x_1500_ = v_reuseFailAlloc_1501_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1487_ == 0 {
                        lean_ctor_set(v___x_1486_, 1, v_buckets_x27_1491_);
                        lean_ctor_set(v___x_1486_, 0, v_size_x27_1489_);
                        v___x_1503_ = v___x_1486_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_size_x27_1489_);
                        lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_buckets_x27_1491_);
                        v___x_1503_ = v_reuseFailAlloc_1504_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1500_;
            }
            4 => {
                return v___x_1503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(
    mut v_scc_1510_: *mut LeanObject,
    mut v_pu_1511_: u8,
    mut v_c_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: u8 = 0;
    let mut v___x_1535_: usize = 0;
    let mut v___x_1536_: usize = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: usize = 0;
    let mut v___x_1539_: usize = 0;
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_c_1512_) == 0 {
                    v_decl_1564_ = lean_ctor_get(v_c_1512_, 0);
                    v_value_1565_ = lean_ctor_get(v_decl_1564_, 3);
                    match lean_obj_tag(v_value_1565_) {
                        3 => {
                            v_declName_1566_ = lean_ctor_get(v_value_1565_, 0);
                            v___x_1567_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg(v_scc_1510_, v_declName_1566_);
                            if v___x_1567_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1568_ = lean_st_ref_take(v___y_1513_);
                                v___x_1569_ = lean_box(0);
                                lean_inc(v_declName_1566_);
                                v___x_1570_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1___redArg(v___x_1568_, v_declName_1566_, v___x_1569_);
                                v___x_1571_ = lean_st_ref_set(v___y_1513_, v___x_1570_);
                                state = 1;
                                continue;
                            }
                        }
                        9 => {
                            v_fn_1572_ = lean_ctor_get(v_value_1565_, 0);
                            lean_inc(v_fn_1572_);
                            v_name_1557_ = v_fn_1572_;
                            v___y_1558_ = v___y_1513_;
                            state = 2;
                            continue;
                        }
                        10 => {
                            v_fn_1573_ = lean_ctor_get(v_value_1565_, 0);
                            lean_inc(v_fn_1573_);
                            v_name_1557_ = v_fn_1573_;
                            v___y_1558_ = v___y_1513_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => match lean_obj_tag(v_c_1512_) {
                0 => {
                    v_k_1516_ = lean_ctor_get(v_c_1512_, 1);
                    lean_inc_ref(v_k_1516_);
                    lean_dec_ref_known(v_c_1512_, 2);
                    v_c_1512_ = v_k_1516_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_1518_ = lean_ctor_get(v_c_1512_, 0);
                    lean_inc_ref(v_decl_1518_);
                    v_k_1519_ = lean_ctor_get(v_c_1512_, 1);
                    lean_inc_ref(v_k_1519_);
                    lean_dec_ref_known(v_c_1512_, 2);
                    v_value_1520_ = lean_ctor_get(v_decl_1518_, 4);
                    lean_inc_ref(v_value_1520_);
                    lean_dec_ref(v_decl_1518_);
                    v___x_1521_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(v_scc_1510_, v_pu_1511_, v_value_1520_, v___y_1513_);
                    v_c_1512_ = v_k_1519_;
                    state = 0;
                    continue;
                }
                2 => {
                    v_decl_1523_ = lean_ctor_get(v_c_1512_, 0);
                    lean_inc_ref(v_decl_1523_);
                    v_k_1524_ = lean_ctor_get(v_c_1512_, 1);
                    lean_inc_ref(v_k_1524_);
                    lean_dec_ref_known(v_c_1512_, 2);
                    v_value_1525_ = lean_ctor_get(v_decl_1523_, 4);
                    lean_inc_ref(v_value_1525_);
                    lean_dec_ref(v_decl_1523_);
                    v___x_1526_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(v_scc_1510_, v_pu_1511_, v_value_1525_, v___y_1513_);
                    v_c_1512_ = v_k_1524_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_cases_1528_ = lean_ctor_get(v_c_1512_, 0);
                    lean_inc_ref(v_cases_1528_);
                    lean_dec_ref_known(v_c_1512_, 1);
                    v_alts_1529_ = lean_ctor_get(v_cases_1528_, 3);
                    lean_inc_ref(v_alts_1529_);
                    lean_dec_ref(v_cases_1528_);
                    v___x_1530_ = lean_unsigned_to_nat(0);
                    v___x_1531_ = lean_array_get_size(v_alts_1529_);
                    v___x_1532_ = lean_box(0);
                    v___x_1533_ = lean_nat_dec_lt(v___x_1530_, v___x_1531_);
                    if v___x_1533_ == 0 {
                        lean_dec_ref(v_alts_1529_);
                        return v___x_1532_;
                    } else {
                        v___x_1534_ = lean_nat_dec_le(v___x_1531_, v___x_1531_);
                        if v___x_1534_ == 0 {
                            if v___x_1533_ == 0 {
                                lean_dec_ref(v_alts_1529_);
                                return v___x_1532_;
                            } else {
                                v___x_1535_ = 0usize;
                                v___x_1536_ = lean_usize_of_nat(v___x_1531_);
                                v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2_spec__4(v_scc_1510_, v_pu_1511_, v_alts_1529_, v___x_1535_, v___x_1536_, v___x_1532_, v___y_1513_);
                                lean_dec_ref(v_alts_1529_);
                                return v___x_1537_;
                            }
                        } else {
                            v___x_1538_ = 0usize;
                            v___x_1539_ = lean_usize_of_nat(v___x_1531_);
                            v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2_spec__4(v_scc_1510_, v_pu_1511_, v_alts_1529_, v___x_1538_, v___x_1539_, v___x_1532_, v___y_1513_);
                            lean_dec_ref(v_alts_1529_);
                            return v___x_1540_;
                        }
                    }
                }
                7 => {
                    v_k_1541_ = lean_ctor_get(v_c_1512_, 3);
                    lean_inc_ref(v_k_1541_);
                    lean_dec_ref_known(v_c_1512_, 4);
                    v_c_1512_ = v_k_1541_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_1543_ = lean_ctor_get(v_c_1512_, 3);
                    lean_inc_ref(v_k_1543_);
                    lean_dec_ref_known(v_c_1512_, 4);
                    v_c_1512_ = v_k_1543_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_1545_ = lean_ctor_get(v_c_1512_, 5);
                    lean_inc_ref(v_k_1545_);
                    lean_dec_ref_known(v_c_1512_, 6);
                    v_c_1512_ = v_k_1545_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_1547_ = lean_ctor_get(v_c_1512_, 2);
                    lean_inc_ref(v_k_1547_);
                    lean_dec_ref_known(v_c_1512_, 3);
                    v_c_1512_ = v_k_1547_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_1549_ = lean_ctor_get(v_c_1512_, 2);
                    lean_inc_ref(v_k_1549_);
                    lean_dec_ref_known(v_c_1512_, 3);
                    v_c_1512_ = v_k_1549_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_1551_ = lean_ctor_get(v_c_1512_, 3);
                    lean_inc_ref(v_k_1551_);
                    lean_dec_ref_known(v_c_1512_, 4);
                    v_c_1512_ = v_k_1551_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_1553_ = lean_ctor_get(v_c_1512_, 1);
                    lean_inc_ref(v_k_1553_);
                    lean_dec_ref_known(v_c_1512_, 2);
                    v_c_1512_ = v_k_1553_;
                    state = 0;
                    continue;
                }
                _ => {
                    lean_dec_ref(v_c_1512_);
                    v___x_1555_ = lean_box(0);
                    return v___x_1555_;
                }
            },
            2 => {
                v___x_1559_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg(v_scc_1510_, v_name_1557_);
                if v___x_1559_ == 0 {
                    lean_dec(v_name_1557_);
                    state = 1;
                    continue;
                } else {
                    v___x_1560_ = lean_st_ref_take(v___y_1558_);
                    v___x_1561_ = lean_box(0);
                    v___x_1562_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1___redArg(v___x_1560_, v_name_1557_, v___x_1561_);
                    v___x_1563_ = lean_st_ref_set(v___y_1558_, v___x_1562_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2_spec__4(
    mut v_scc_1574_: *mut LeanObject,
    mut v_pu_1575_: u8,
    mut v_as_1576_: *mut LeanObject,
    mut v_i_1577_: usize,
    mut v_stop_1578_: usize,
    mut v_b_1579_: *mut LeanObject,
    mut v___y_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: usize = 0;
    let mut v___x_1585_: usize = 0;
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1587_ = lean_usize_dec_eq(v_i_1577_, v_stop_1578_);
                if v___x_1587_ == 0 {
                    v___x_1588_ = lean_array_uget_borrowed(v_as_1576_, v_i_1577_);
                    match lean_obj_tag(v___x_1588_) {
                        0 => {
                            v_code_1589_ = lean_ctor_get(v___x_1588_, 2);
                            lean_inc_ref(v_code_1589_);
                            v___x_1590_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(v_scc_1574_, v_pu_1575_, v_code_1589_, v___y_1580_);
                            v___y_1583_ = v___x_1590_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1591_ = lean_ctor_get(v___x_1588_, 1);
                            lean_inc_ref(v_code_1591_);
                            v___x_1592_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(v_scc_1574_, v_pu_1575_, v_code_1591_, v___y_1580_);
                            v___y_1583_ = v___x_1592_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1593_ = lean_ctor_get(v___x_1588_, 0);
                            lean_inc_ref(v_code_1593_);
                            v___x_1594_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(v_scc_1574_, v_pu_1575_, v_code_1593_, v___y_1580_);
                            v___y_1583_ = v___x_1594_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_1579_;
                }
            }
            1 => {
                v___x_1584_ = 1usize;
                v___x_1585_ = lean_usize_add(v_i_1577_, v___x_1584_);
                v_i_1577_ = v___x_1585_;
                v_b_1579_ = v___y_1583_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2_spec__4___boxed(
    mut v_scc_1595_: *mut LeanObject,
    mut v_pu_1596_: *mut LeanObject,
    mut v_as_1597_: *mut LeanObject,
    mut v_i_1598_: *mut LeanObject,
    mut v_stop_1599_: *mut LeanObject,
    mut v_b_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1603_: u8 = 0;
    let mut v_i_boxed_1604_: usize = 0;
    let mut v_stop_boxed_1605_: usize = 0;
    let mut v_res_1606_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1603_ = (lean_unbox(v_pu_1596_) as u8);
    v_i_boxed_1604_ = lean_unbox_usize(v_i_1598_);
    lean_dec(v_i_1598_);
    v_stop_boxed_1605_ = lean_unbox_usize(v_stop_1599_);
    lean_dec(v_stop_1599_);
    v_res_1606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2_spec__4(v_scc_1595_, v_pu_boxed_1603_, v_as_1597_, v_i_boxed_1604_, v_stop_boxed_1605_, v_b_1600_, v___y_1601_);
    lean_dec(v___y_1601_);
    lean_dec_ref(v_as_1597_);
    lean_dec_ref(v_scc_1595_);
    return v_res_1606_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2___boxed(
    mut v_scc_1607_: *mut LeanObject,
    mut v_pu_1608_: *mut LeanObject,
    mut v_c_1609_: *mut LeanObject,
    mut v___y_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1612_: u8 = 0;
    let mut v_res_1613_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1612_ = (lean_unbox(v_pu_1608_) as u8);
    v_res_1613_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(v_scc_1607_, v_pu_boxed_1612_, v_c_1609_, v___y_1610_);
    lean_dec(v___y_1610_);
    lean_dec_ref(v_scc_1607_);
    return v_res_1613_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode(
    mut v_pu_1614_: u8,
    mut v_scc_1615_: *mut LeanObject,
    mut v_c_1616_: *mut LeanObject,
    mut v_a_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    v___x_1619_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(v_scc_1615_, v_pu_1614_, v_c_1616_, v_a_1617_);
    return v___x_1619_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode___boxed(
    mut v_pu_1620_: *mut LeanObject,
    mut v_scc_1621_: *mut LeanObject,
    mut v_c_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1625_: u8 = 0;
    let mut v_res_1626_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1625_ = (lean_unbox(v_pu_1620_) as u8);
    v_res_1626_ =
        l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode(
            v_pu_boxed_1625_,
            v_scc_1621_,
            v_c_1622_,
            v_a_1623_,
        );
    lean_dec(v_a_1623_);
    lean_dec_ref(v_scc_1621_);
    return v_res_1626_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0(
    mut v_00_u03b2_1627_: *mut LeanObject,
    mut v_m_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
) -> u8 {
    let mut v___x_1630_: u8 = 0;
    v___x_1630_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg(v_m_1628_, v_a_1629_);
    return v___x_1630_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___boxed(
    mut v_00_u03b2_1631_: *mut LeanObject,
    mut v_m_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1634_: u8 = 0;
    let mut v_r_1635_: *mut LeanObject = core::ptr::null_mut();
    v_res_1634_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0(v_00_u03b2_1631_, v_m_1632_, v_a_1633_);
    lean_dec(v_a_1633_);
    lean_dec_ref(v_m_1632_);
    v_r_1635_ = lean_box((v_res_1634_) as usize);
    return v_r_1635_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1(
    mut v_00_u03b2_1636_: *mut LeanObject,
    mut v_m_1637_: *mut LeanObject,
    mut v_a_1638_: *mut LeanObject,
    mut v_b_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1___redArg(v_m_1637_, v_a_1638_, v_b_1639_);
    return v___x_1640_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0(
    mut v_00_u03b2_1641_: *mut LeanObject,
    mut v_a_1642_: *mut LeanObject,
    mut v_x_1643_: *mut LeanObject,
) -> u8 {
    let mut v___x_1644_: u8 = 0;
    v___x_1644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0___redArg(v_a_1642_, v_x_1643_);
    return v___x_1644_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0___boxed(
    mut v_00_u03b2_1645_: *mut LeanObject,
    mut v_a_1646_: *mut LeanObject,
    mut v_x_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1648_: u8 = 0;
    let mut v_r_1649_: *mut LeanObject = core::ptr::null_mut();
    v_res_1648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0(v_00_u03b2_1645_, v_a_1646_, v_x_1647_);
    lean_dec(v_x_1647_);
    lean_dec(v_a_1646_);
    v_r_1649_ = lean_box((v_res_1648_) as usize);
    return v_r_1649_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2(
    mut v_00_u03b2_1650_: *mut LeanObject,
    mut v_data_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2___redArg(v_data_1651_);
    return v___x_1652_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1653_: *mut LeanObject,
    mut v_i_1654_: *mut LeanObject,
    mut v_source_1655_: *mut LeanObject,
    mut v_target_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    v___x_1657_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2_spec__3___redArg(v_i_1654_, v_source_1655_, v_target_1656_);
    return v___x_1657_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1658_: *mut LeanObject,
    mut v_x_1659_: *mut LeanObject,
    mut v_x_1660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    v___x_1661_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2_spec__3_spec__5___redArg(v_x_1659_, v_x_1660_);
    return v___x_1661_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__0()
-> *mut LeanObject {
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    v___x_1662_ = lean_box(0);
    v___x_1663_ = lean_unsigned_to_nat(16);
    v___x_1664_ = lean_mk_array(v___x_1663_, v___x_1662_);
    return v___x_1664_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1()
-> *mut LeanObject {
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v___x_1665_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__0);
    v___x_1666_ = lean_unsigned_to_nat(0);
    v___x_1667_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1667_, 0, v___x_1666_);
    lean_ctor_set(v___x_1667_, 1, v___x_1665_);
    return v___x_1667_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls(
    mut v_pu_1668_: u8,
    mut v_scc_1669_: *mut LeanObject,
    mut v_decl_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_1672_: *mut LeanObject = core::ptr::null_mut();
    v_value_1672_ = lean_ctor_get(v_decl_1670_, 1);
    lean_inc_ref(v_value_1672_);
    lean_dec_ref(v_decl_1670_);
    if lean_obj_tag(v_value_1672_) == 0 {
        let mut v_code_1673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
        v_code_1673_ = lean_ctor_get(v_value_1672_, 0);
        lean_inc_ref(v_code_1673_);
        lean_dec_ref_known(v_value_1672_, 1);
        v___x_1674_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1_once), _init_l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1);
        v___x_1675_ = lean_st_mk_ref(v___x_1674_);
        v___x_1676_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__2(v_scc_1669_, v_pu_1668_, v_code_1673_, v___x_1675_);
        v___x_1677_ = lean_st_ref_get(v___x_1675_);
        lean_dec(v___x_1675_);
        return v___x_1677_;
    } else {
        let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_value_1672_, 1);
        v___x_1678_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1_once), _init_l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1);
        return v___x_1678_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___boxed(
    mut v_pu_1679_: *mut LeanObject,
    mut v_scc_1680_: *mut LeanObject,
    mut v_decl_1681_: *mut LeanObject,
    mut v_a_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1683_: u8 = 0;
    let mut v_res_1684_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1683_ = (lean_unbox(v_pu_1679_) as u8);
    v_res_1684_ =
        l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls(
            v_pu_boxed_1683_,
            v_scc_1680_,
            v_decl_1681_,
        );
    lean_dec_ref(v_scc_1680_);
    return v_res_1684_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__0()
-> *mut LeanObject {
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    v___x_1685_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1685_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__1()
-> *mut LeanObject {
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    v___x_1686_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__0,
    );
    v___x_1687_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1687_, 0, v___x_1686_);
    return v___x_1687_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__2()
-> *mut LeanObject {
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    v___x_1688_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__1_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__1,
    );
    v___x_1689_ = lean_unsigned_to_nat(0);
    v___x_1690_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1690_, 0, v___x_1689_);
    lean_ctor_set(v___x_1690_, 1, v___x_1689_);
    lean_ctor_set(v___x_1690_, 2, v___x_1689_);
    lean_ctor_set(v___x_1690_, 3, v___x_1689_);
    lean_ctor_set(v___x_1690_, 4, v___x_1688_);
    lean_ctor_set(v___x_1690_, 5, v___x_1688_);
    lean_ctor_set(v___x_1690_, 6, v___x_1688_);
    lean_ctor_set(v___x_1690_, 7, v___x_1688_);
    lean_ctor_set(v___x_1690_, 8, v___x_1688_);
    lean_ctor_set(v___x_1690_, 9, v___x_1688_);
    return v___x_1690_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__3()
-> f64 {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: f64 = 0.0;
    v___x_1691_ = lean_unsigned_to_nat(0);
    v___x_1692_ = lean_float_of_nat(v___x_1691_);
    return v___x_1692_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14(
    mut v_cls_1696_: *mut LeanObject,
    mut v_msg_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1711_: u8 = 0;
    let mut v_env_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v_tid_1731_: u64 = 0;
    let mut v_traces_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1735_: u8 = 0;
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: f64 = 0.0;
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1762_: u8 = 0;
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v_unused_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut v_a_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1770_: u8 = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1703_ = lean_ctor_get(v___y_1700_, 2);
                v_ref_1704_ = lean_ctor_get(v___y_1700_, 5);
                v___x_1705_ = lean_st_ref_get(v___y_1701_);
                v___x_1706_ = lean_st_ref_get(v___y_1699_);
                v___x_1707_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1698_);
                if lean_obj_tag(v___x_1707_) == 0 {
                    v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
                    v_isSharedCheck_1766_ = (!lean_is_exclusive(v___x_1707_)) as u8;
                    if v_isSharedCheck_1766_ == 0 {
                        v___x_1710_ = v___x_1707_;
                        v_isShared_1711_ = v_isSharedCheck_1766_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1708_);
                        lean_dec(v___x_1707_);
                        v___x_1710_ = lean_box(0);
                        v_isShared_1711_ = v_isSharedCheck_1766_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1706_);
                    lean_dec(v___x_1705_);
                    lean_dec_ref(v_msg_1697_);
                    lean_dec(v_cls_1696_);
                    v_a_1767_ = lean_ctor_get(v___x_1707_, 0);
                    v_isSharedCheck_1774_ = (!lean_is_exclusive(v___x_1707_)) as u8;
                    if v_isSharedCheck_1774_ == 0 {
                        v___x_1769_ = v___x_1707_;
                        v_isShared_1770_ = v_isSharedCheck_1774_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1767_);
                        lean_dec(v___x_1707_);
                        v___x_1769_ = lean_box(0);
                        v_isShared_1770_ = v_isSharedCheck_1774_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_1712_ = lean_ctor_get(v___x_1705_, 0);
                lean_inc_ref(v_env_1712_);
                lean_dec(v___x_1705_);
                v_lctx_1713_ = lean_ctor_get(v___x_1706_, 0);
                v_isSharedCheck_1764_ = (!lean_is_exclusive(v___x_1706_)) as u8;
                if v_isSharedCheck_1764_ == 0 {
                    v_unused_1765_ = lean_ctor_get(v___x_1706_, 1);
                    lean_dec(v_unused_1765_);
                    v___x_1715_ = v___x_1706_;
                    v_isShared_1716_ = v_isSharedCheck_1764_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_1713_);
                    lean_dec(v___x_1706_);
                    v___x_1715_ = lean_box(0);
                    v_isShared_1716_ = v_isSharedCheck_1764_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1717_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__2);
                v___x_1718_ = lean_st_ref_take(v___y_1701_);
                v_traceState_1719_ = lean_ctor_get(v___x_1718_, 4);
                v_env_1720_ = lean_ctor_get(v___x_1718_, 0);
                v_nextMacroScope_1721_ = lean_ctor_get(v___x_1718_, 1);
                v_ngen_1722_ = lean_ctor_get(v___x_1718_, 2);
                v_auxDeclNGen_1723_ = lean_ctor_get(v___x_1718_, 3);
                v_cache_1724_ = lean_ctor_get(v___x_1718_, 5);
                v_messages_1725_ = lean_ctor_get(v___x_1718_, 6);
                v_infoState_1726_ = lean_ctor_get(v___x_1718_, 7);
                v_snapshotTasks_1727_ = lean_ctor_get(v___x_1718_, 8);
                v_isSharedCheck_1763_ = (!lean_is_exclusive(v___x_1718_)) as u8;
                if v_isSharedCheck_1763_ == 0 {
                    v___x_1729_ = v___x_1718_;
                    v_isShared_1730_ = v_isSharedCheck_1763_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1727_);
                    lean_inc(v_infoState_1726_);
                    lean_inc(v_messages_1725_);
                    lean_inc(v_cache_1724_);
                    lean_inc(v_traceState_1719_);
                    lean_inc(v_auxDeclNGen_1723_);
                    lean_inc(v_ngen_1722_);
                    lean_inc(v_nextMacroScope_1721_);
                    lean_inc(v_env_1720_);
                    lean_dec(v___x_1718_);
                    v___x_1729_ = lean_box(0);
                    v_isShared_1730_ = v_isSharedCheck_1763_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_1731_ = lean_ctor_get_uint64(
                    v_traceState_1719_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_1732_ = lean_ctor_get(v_traceState_1719_, 0);
                v_isSharedCheck_1762_ = (!lean_is_exclusive(v_traceState_1719_)) as u8;
                if v_isSharedCheck_1762_ == 0 {
                    v___x_1734_ = v_traceState_1719_;
                    v_isShared_1735_ = v_isSharedCheck_1762_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_traces_1732_);
                    lean_dec(v_traceState_1719_);
                    v___x_1734_ = lean_box(0);
                    v_isShared_1735_ = v_isSharedCheck_1762_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1736_ = (lean_unbox(v_a_1708_) as u8);
                lean_dec(v_a_1708_);
                v___x_1737_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1713_, v___x_1736_);
                lean_dec_ref(v_lctx_1713_);
                lean_inc_ref(v_options_1703_);
                v___x_1738_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1738_, 0, v_env_1712_);
                lean_ctor_set(v___x_1738_, 1, v___x_1717_);
                lean_ctor_set(v___x_1738_, 2, v___x_1737_);
                lean_ctor_set(v___x_1738_, 3, v_options_1703_);
                if v_isShared_1716_ == 0 {
                    lean_ctor_set_tag(v___x_1715_, 3);
                    lean_ctor_set(v___x_1715_, 1, v_msg_1697_);
                    lean_ctor_set(v___x_1715_, 0, v___x_1738_);
                    v___x_1740_ = v___x_1715_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1761_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1738_);
                    lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_msg_1697_);
                    v___x_1740_ = v_reuseFailAlloc_1761_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1741_ = lean_box(0);
                v___x_1742_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__3);
                v___x_1743_ = 0;
                v___x_1744_ =
                    l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__4;
                v___x_1745_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_1745_, 0, v_cls_1696_);
                lean_ctor_set(v___x_1745_, 1, v___x_1741_);
                lean_ctor_set(v___x_1745_, 2, v___x_1744_);
                lean_ctor_set_float(
                    v___x_1745_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1742_,
                );
                lean_ctor_set_float(
                    v___x_1745_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_1742_,
                );
                lean_ctor_set_uint8(
                    v___x_1745_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_1743_,
                );
                v___x_1746_ =
                    l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___closed__5;
                v___x_1747_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_1747_, 0, v___x_1745_);
                lean_ctor_set(v___x_1747_, 1, v___x_1740_);
                lean_ctor_set(v___x_1747_, 2, v___x_1746_);
                lean_inc(v_ref_1704_);
                v___x_1748_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1748_, 0, v_ref_1704_);
                lean_ctor_set(v___x_1748_, 1, v___x_1747_);
                v___x_1749_ = l_Lean_PersistentArray_push___redArg(v_traces_1732_, v___x_1748_);
                if v_isShared_1735_ == 0 {
                    lean_ctor_set(v___x_1734_, 0, v___x_1749_);
                    v___x_1751_ = v___x_1734_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1749_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_1760_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_1731_,
                    );
                    v___x_1751_ = v_reuseFailAlloc_1760_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1730_ == 0 {
                    lean_ctor_set(v___x_1729_, 4, v___x_1751_);
                    v___x_1753_ = v___x_1729_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_env_1720_);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_nextMacroScope_1721_);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_ngen_1722_);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_auxDeclNGen_1723_);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 4, v___x_1751_);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 5, v_cache_1724_);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 6, v_messages_1725_);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 7, v_infoState_1726_);
                    lean_ctor_set(v_reuseFailAlloc_1759_, 8, v_snapshotTasks_1727_);
                    v___x_1753_ = v_reuseFailAlloc_1759_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1754_ = lean_st_ref_set(v___y_1701_, v___x_1753_);
                v___x_1755_ = lean_box(0);
                if v_isShared_1711_ == 0 {
                    lean_ctor_set(v___x_1710_, 0, v___x_1755_);
                    v___x_1757_ = v___x_1710_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
                    v___x_1757_ = v_reuseFailAlloc_1758_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1757_;
            }
            9 => {
                if v_isShared_1770_ == 0 {
                    v___x_1772_ = v___x_1769_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
                    v___x_1772_ = v_reuseFailAlloc_1773_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14___boxed(
    mut v_cls_1775_: *mut LeanObject,
    mut v_msg_1776_: *mut LeanObject,
    mut v___y_1777_: *mut LeanObject,
    mut v___y_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1782_: *mut LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14(
        v_cls_1775_,
        v_msg_1776_,
        v___y_1777_,
        v___y_1778_,
        v___y_1779_,
        v___y_1780_,
    );
    lean_dec(v___y_1780_);
    lean_dec_ref(v___y_1779_);
    lean_dec(v___y_1778_);
    lean_dec_ref(v___y_1777_);
    return v_res_1782_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9_spec__13___redArg(
    mut v_a_1783_: *mut LeanObject,
    mut v_fallback_1784_: *mut LeanObject,
    mut v_x_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1785_) == 0 {
                    lean_inc(v_fallback_1784_);
                    return v_fallback_1784_;
                } else {
                    v_key_1786_ = lean_ctor_get(v_x_1785_, 0);
                    v_value_1787_ = lean_ctor_get(v_x_1785_, 1);
                    v_tail_1788_ = lean_ctor_get(v_x_1785_, 2);
                    v___x_1789_ = lean_name_eq(v_key_1786_, v_a_1783_);
                    if v___x_1789_ == 0 {
                        v_x_1785_ = v_tail_1788_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1787_);
                        return v_value_1787_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9_spec__13___redArg___boxed(
    mut v_a_1791_: *mut LeanObject,
    mut v_fallback_1792_: *mut LeanObject,
    mut v_x_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1794_: *mut LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9_spec__13___redArg(v_a_1791_, v_fallback_1792_, v_x_1793_);
    lean_dec(v_x_1793_);
    lean_dec(v_fallback_1792_);
    lean_dec(v_a_1791_);
    return v_res_1794_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9___redArg(
    mut v_m_1795_: *mut LeanObject,
    mut v_a_1796_: *mut LeanObject,
    mut v_fallback_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1801_: u64 = 0;
    let mut v___x_1802_: u64 = 0;
    let mut v___x_1803_: u64 = 0;
    let mut v_fold_1804_: u64 = 0;
    let mut v___x_1805_: u64 = 0;
    let mut v___x_1806_: u64 = 0;
    let mut v___x_1807_: u64 = 0;
    let mut v___x_1808_: usize = 0;
    let mut v___x_1809_: usize = 0;
    let mut v___x_1810_: usize = 0;
    let mut v___x_1811_: usize = 0;
    let mut v___x_1812_: usize = 0;
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u64 = 0;
    let mut v_hash_1816_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1798_ = lean_ctor_get(v_m_1795_, 1);
                v___x_1799_ = lean_array_get_size(v_buckets_1798_);
                if lean_obj_tag(v_a_1796_) == 0 {
                    v___x_1815_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0);
                    v___y_1801_ = v___x_1815_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1816_ = lean_ctor_get_uint64(
                        v_a_1796_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1801_ = v_hash_1816_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1802_ = 32u64;
                v___x_1803_ = lean_uint64_shift_right(v___y_1801_, v___x_1802_);
                v_fold_1804_ = lean_uint64_xor(v___y_1801_, v___x_1803_);
                v___x_1805_ = 16u64;
                v___x_1806_ = lean_uint64_shift_right(v_fold_1804_, v___x_1805_);
                v___x_1807_ = lean_uint64_xor(v_fold_1804_, v___x_1806_);
                v___x_1808_ = lean_uint64_to_usize(v___x_1807_);
                v___x_1809_ = lean_usize_of_nat(v___x_1799_);
                v___x_1810_ = 1usize;
                v___x_1811_ = lean_usize_sub(v___x_1809_, v___x_1810_);
                v___x_1812_ = lean_usize_land(v___x_1808_, v___x_1811_);
                v___x_1813_ = lean_array_uget_borrowed(v_buckets_1798_, v___x_1812_);
                v___x_1814_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9_spec__13___redArg(v_a_1796_, v_fallback_1797_, v___x_1813_);
                return v___x_1814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9___redArg___boxed(
    mut v_m_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_fallback_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1820_: *mut LeanObject = core::ptr::null_mut();
    v_res_1820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9___redArg(v_m_1817_, v_a_1818_, v_fallback_1819_);
    lean_dec(v_fallback_1819_);
    lean_dec(v_a_1818_);
    lean_dec_ref(v_m_1817_);
    return v_res_1820_;
}
pub unsafe fn l_Lean_Compiler_LCNF_splitScc___lam__0(
    mut v___x_1821_: *mut LeanObject,
    mut v_x_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    v___x_1823_ = lean_box(0);
    v___x_1824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9___redArg(v___x_1821_, v_x_1822_, v___x_1823_);
    return v___x_1824_;
}
pub unsafe fn l_Lean_Compiler_LCNF_splitScc___lam__0___boxed(
    mut v___x_1825_: *mut LeanObject,
    mut v_x_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1827_: *mut LeanObject = core::ptr::null_mut();
    v_res_1827_ = l_Lean_Compiler_LCNF_splitScc___lam__0(v___x_1825_, v_x_1826_);
    lean_dec(v_x_1826_);
    lean_dec_ref(v___x_1825_);
    return v_res_1827_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2_spec__4___redArg(
    mut v_a_1828_: *mut LeanObject,
    mut v_b_1829_: *mut LeanObject,
    mut v_x_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1836_: u8 = 0;
    let mut v___x_1837_: u8 = 0;
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1830_) == 0 {
                    lean_dec(v_b_1829_);
                    lean_dec(v_a_1828_);
                    return v_x_1830_;
                } else {
                    v_key_1831_ = lean_ctor_get(v_x_1830_, 0);
                    v_value_1832_ = lean_ctor_get(v_x_1830_, 1);
                    v_tail_1833_ = lean_ctor_get(v_x_1830_, 2);
                    v_isSharedCheck_1845_ = (!lean_is_exclusive(v_x_1830_)) as u8;
                    if v_isSharedCheck_1845_ == 0 {
                        v___x_1835_ = v_x_1830_;
                        v_isShared_1836_ = v_isSharedCheck_1845_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1833_);
                        lean_inc(v_value_1832_);
                        lean_inc(v_key_1831_);
                        lean_dec(v_x_1830_);
                        v___x_1835_ = lean_box(0);
                        v_isShared_1836_ = v_isSharedCheck_1845_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1837_ = lean_name_eq(v_key_1831_, v_a_1828_);
                if v___x_1837_ == 0 {
                    v___x_1838_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2_spec__4___redArg(v_a_1828_, v_b_1829_, v_tail_1833_);
                    if v_isShared_1836_ == 0 {
                        lean_ctor_set(v___x_1835_, 2, v___x_1838_);
                        v___x_1840_ = v___x_1835_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_key_1831_);
                        lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_value_1832_);
                        lean_ctor_set(v_reuseFailAlloc_1841_, 2, v___x_1838_);
                        v___x_1840_ = v_reuseFailAlloc_1841_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1832_);
                    lean_dec(v_key_1831_);
                    if v_isShared_1836_ == 0 {
                        lean_ctor_set(v___x_1835_, 1, v_b_1829_);
                        lean_ctor_set(v___x_1835_, 0, v_a_1828_);
                        v___x_1843_ = v___x_1835_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1828_);
                        lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_b_1829_);
                        lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_tail_1833_);
                        v___x_1843_ = v_reuseFailAlloc_1844_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1840_;
            }
            3 => {
                return v___x_1843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2___redArg(
    mut v_m_1846_: *mut LeanObject,
    mut v_a_1847_: *mut LeanObject,
    mut v_b_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1856_: u64 = 0;
    let mut v___x_1857_: u64 = 0;
    let mut v___x_1858_: u64 = 0;
    let mut v_fold_1859_: u64 = 0;
    let mut v___x_1860_: u64 = 0;
    let mut v___x_1861_: u64 = 0;
    let mut v___x_1862_: u64 = 0;
    let mut v___x_1863_: usize = 0;
    let mut v___x_1864_: usize = 0;
    let mut v___x_1865_: usize = 0;
    let mut v___x_1866_: usize = 0;
    let mut v___x_1867_: usize = 0;
    let mut v_bkt_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v_val_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: u64 = 0;
    let mut v_hash_1895_: u64 = 0;
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1849_ = lean_ctor_get(v_m_1846_, 0);
                v_buckets_1850_ = lean_ctor_get(v_m_1846_, 1);
                v_isSharedCheck_1896_ = (!lean_is_exclusive(v_m_1846_)) as u8;
                if v_isSharedCheck_1896_ == 0 {
                    v___x_1852_ = v_m_1846_;
                    v_isShared_1853_ = v_isSharedCheck_1896_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1850_);
                    lean_inc(v_size_1849_);
                    lean_dec(v_m_1846_);
                    v___x_1852_ = lean_box(0);
                    v_isShared_1853_ = v_isSharedCheck_1896_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1854_ = lean_array_get_size(v_buckets_1850_);
                if lean_obj_tag(v_a_1847_) == 0 {
                    v___x_1894_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0);
                    v___y_1856_ = v___x_1894_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1895_ = lean_ctor_get_uint64(
                        v_a_1847_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1856_ = v_hash_1895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1857_ = 32u64;
                v___x_1858_ = lean_uint64_shift_right(v___y_1856_, v___x_1857_);
                v_fold_1859_ = lean_uint64_xor(v___y_1856_, v___x_1858_);
                v___x_1860_ = 16u64;
                v___x_1861_ = lean_uint64_shift_right(v_fold_1859_, v___x_1860_);
                v___x_1862_ = lean_uint64_xor(v_fold_1859_, v___x_1861_);
                v___x_1863_ = lean_uint64_to_usize(v___x_1862_);
                v___x_1864_ = lean_usize_of_nat(v___x_1854_);
                v___x_1865_ = 1usize;
                v___x_1866_ = lean_usize_sub(v___x_1864_, v___x_1865_);
                v___x_1867_ = lean_usize_land(v___x_1863_, v___x_1866_);
                v_bkt_1868_ = lean_array_uget_borrowed(v_buckets_1850_, v___x_1867_);
                v___x_1869_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0_spec__0___redArg(v_a_1847_, v_bkt_1868_);
                if v___x_1869_ == 0 {
                    v___x_1870_ = lean_unsigned_to_nat(1);
                    v_size_x27_1871_ = lean_nat_add(v_size_1849_, v___x_1870_);
                    lean_dec(v_size_1849_);
                    lean_inc(v_bkt_1868_);
                    v___x_1872_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1872_, 0, v_a_1847_);
                    lean_ctor_set(v___x_1872_, 1, v_b_1848_);
                    lean_ctor_set(v___x_1872_, 2, v_bkt_1868_);
                    v_buckets_x27_1873_ =
                        lean_array_uset(v_buckets_1850_, v___x_1867_, v___x_1872_);
                    v___x_1874_ = lean_unsigned_to_nat(4);
                    v___x_1875_ = lean_nat_mul(v_size_x27_1871_, v___x_1874_);
                    v___x_1876_ = lean_unsigned_to_nat(3);
                    v___x_1877_ = lean_nat_div(v___x_1875_, v___x_1876_);
                    lean_dec(v___x_1875_);
                    v___x_1878_ = lean_array_get_size(v_buckets_x27_1873_);
                    v___x_1879_ = lean_nat_dec_le(v___x_1877_, v___x_1878_);
                    lean_dec(v___x_1877_);
                    if v___x_1879_ == 0 {
                        v_val_1880_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__1_spec__2___redArg(v_buckets_x27_1873_);
                        if v_isShared_1853_ == 0 {
                            lean_ctor_set(v___x_1852_, 1, v_val_1880_);
                            lean_ctor_set(v___x_1852_, 0, v_size_x27_1871_);
                            v___x_1882_ = v___x_1852_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_size_x27_1871_);
                            lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_val_1880_);
                            v___x_1882_ = v_reuseFailAlloc_1883_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_1853_ == 0 {
                            lean_ctor_set(v___x_1852_, 1, v_buckets_x27_1873_);
                            lean_ctor_set(v___x_1852_, 0, v_size_x27_1871_);
                            v___x_1885_ = v___x_1852_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_size_x27_1871_);
                            lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_buckets_x27_1873_);
                            v___x_1885_ = v_reuseFailAlloc_1886_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1868_);
                    v___x_1887_ = lean_box(0);
                    v_buckets_x27_1888_ =
                        lean_array_uset(v_buckets_1850_, v___x_1867_, v___x_1887_);
                    v___x_1889_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2_spec__4___redArg(v_a_1847_, v_b_1848_, v_bkt_1868_);
                    v___x_1890_ = lean_array_uset(v_buckets_x27_1888_, v___x_1867_, v___x_1889_);
                    if v_isShared_1853_ == 0 {
                        lean_ctor_set(v___x_1852_, 1, v___x_1890_);
                        v___x_1892_ = v___x_1852_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_size_1849_);
                        lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1890_);
                        v___x_1892_ = v_reuseFailAlloc_1893_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1882_;
            }
            4 => {
                return v___x_1885_;
            }
            5 => {
                return v___x_1892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__3(
    mut v_as_1897_: *mut LeanObject,
    mut v_sz_1898_: usize,
    mut v_i_1899_: usize,
    mut v_b_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1901_: u8 = 0;
    let mut v_a_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: usize = 0;
    let mut v___x_1907_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1901_ = lean_usize_dec_lt(v_i_1899_, v_sz_1898_);
                if v___x_1901_ == 0 {
                    return v_b_1900_;
                } else {
                    v_a_1902_ = lean_array_uget_borrowed(v_as_1897_, v_i_1899_);
                    v_fst_1903_ = lean_ctor_get(v_a_1902_, 0);
                    v_snd_1904_ = lean_ctor_get(v_a_1902_, 1);
                    lean_inc(v_snd_1904_);
                    lean_inc(v_fst_1903_);
                    v_r_1905_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2___redArg(v_b_1900_, v_fst_1903_, v_snd_1904_);
                    v___x_1906_ = 1usize;
                    v___x_1907_ = lean_usize_add(v_i_1899_, v___x_1906_);
                    v_i_1899_ = v___x_1907_;
                    v_b_1900_ = v_r_1905_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__3___boxed(
    mut v_as_1909_: *mut LeanObject,
    mut v_sz_1910_: *mut LeanObject,
    mut v_i_1911_: *mut LeanObject,
    mut v_b_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1913_: usize = 0;
    let mut v_i_boxed_1914_: usize = 0;
    let mut v_res_1915_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1913_ = lean_unbox_usize(v_sz_1910_);
    lean_dec(v_sz_1910_);
    v_i_boxed_1914_ = lean_unbox_usize(v_i_1911_);
    lean_dec(v_i_1911_);
    v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__3(v_as_1909_, v_sz_boxed_1913_, v_i_boxed_1914_, v_b_1912_);
    lean_dec_ref(v_as_1909_);
    return v_res_1915_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2(
    mut v_m_1916_: *mut LeanObject,
    mut v_l_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1918_: usize = 0;
    let mut v___x_1919_: usize = 0;
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1918_ = lean_array_size(v_l_1917_);
    v___x_1919_ = 0usize;
    v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__3(v_l_1917_, v_sz_1918_, v___x_1919_, v_m_1916_);
    return v___x_1920_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2___boxed(
    mut v_m_1921_: *mut LeanObject,
    mut v_l_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2(v_m_1921_, v_l_1922_);
    lean_dec_ref(v_l_1922_);
    return v_res_1923_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5_spec__8(
    mut v_pu_1924_: u8,
    mut v_msg_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    v___x_1926_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_1924_);
    v___x_1927_ = lean_panic_fn_borrowed(v___x_1926_, v_msg_1925_);
    lean_dec_ref(v___x_1926_);
    return v___x_1927_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5_spec__8___boxed(
    mut v_pu_1928_: *mut LeanObject,
    mut v_msg_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1930_: u8 = 0;
    let mut v_res_1931_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1930_ = (lean_unbox(v_pu_1928_) as u8);
    v_res_1931_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5_spec__8(v_pu_boxed_1930_, v_msg_1929_);
    return v_res_1931_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    v___x_1935_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__2;
    v___x_1936_ = lean_unsigned_to_nat(11);
    v___x_1937_ = lean_unsigned_to_nat(163);
    v___x_1938_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__1;
    v___x_1939_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__0;
    v___x_1940_ = l_mkPanicMessageWithDecl(
        v___x_1939_,
        v___x_1938_,
        v___x_1937_,
        v___x_1936_,
        v___x_1935_,
    );
    return v___x_1940_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5(
    mut v_pu_1941_: u8,
    mut v_a_1942_: *mut LeanObject,
    mut v_x_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1943_) == 0 {
                    v___x_1944_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___closed__3);
                    v___x_1945_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5_spec__8(v_pu_1941_, v___x_1944_);
                    return v___x_1945_;
                } else {
                    v_key_1946_ = lean_ctor_get(v_x_1943_, 0);
                    v_value_1947_ = lean_ctor_get(v_x_1943_, 1);
                    v_tail_1948_ = lean_ctor_get(v_x_1943_, 2);
                    v___x_1949_ = lean_name_eq(v_key_1946_, v_a_1942_);
                    if v___x_1949_ == 0 {
                        v_x_1943_ = v_tail_1948_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1947_);
                        return v_value_1947_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5___boxed(
    mut v_pu_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
    mut v_x_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1954_: u8 = 0;
    let mut v_res_1955_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1954_ = (lean_unbox(v_pu_1951_) as u8);
    v_res_1955_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5(v_pu_boxed_1954_, v_a_1952_, v_x_1953_);
    lean_dec(v_x_1953_);
    lean_dec(v_a_1952_);
    return v_res_1955_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3(
    mut v_pu_1956_: u8,
    mut v_m_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1962_: u64 = 0;
    let mut v___x_1963_: u64 = 0;
    let mut v___x_1964_: u64 = 0;
    let mut v_fold_1965_: u64 = 0;
    let mut v___x_1966_: u64 = 0;
    let mut v___x_1967_: u64 = 0;
    let mut v___x_1968_: u64 = 0;
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: usize = 0;
    let mut v___x_1973_: usize = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: u64 = 0;
    let mut v_hash_1977_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1959_ = lean_ctor_get(v_m_1957_, 1);
                v___x_1960_ = lean_array_get_size(v_buckets_1959_);
                if lean_obj_tag(v_a_1958_) == 0 {
                    v___x_1976_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0);
                    v___y_1962_ = v___x_1976_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1977_ = lean_ctor_get_uint64(
                        v_a_1958_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1962_ = v_hash_1977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1963_ = 32u64;
                v___x_1964_ = lean_uint64_shift_right(v___y_1962_, v___x_1963_);
                v_fold_1965_ = lean_uint64_xor(v___y_1962_, v___x_1964_);
                v___x_1966_ = 16u64;
                v___x_1967_ = lean_uint64_shift_right(v_fold_1965_, v___x_1966_);
                v___x_1968_ = lean_uint64_xor(v_fold_1965_, v___x_1967_);
                v___x_1969_ = lean_uint64_to_usize(v___x_1968_);
                v___x_1970_ = lean_usize_of_nat(v___x_1960_);
                v___x_1971_ = 1usize;
                v___x_1972_ = lean_usize_sub(v___x_1970_, v___x_1971_);
                v___x_1973_ = lean_usize_land(v___x_1969_, v___x_1972_);
                v___x_1974_ = lean_array_uget_borrowed(v_buckets_1959_, v___x_1973_);
                v___x_1975_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3_spec__5(v_pu_1956_, v_a_1958_, v___x_1974_);
                return v___x_1975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3___boxed(
    mut v_pu_1978_: *mut LeanObject,
    mut v_m_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1981_: u8 = 0;
    let mut v_res_1982_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1981_ = (lean_unbox(v_pu_1978_) as u8);
    v_res_1982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3(v_pu_boxed_1981_, v_m_1979_, v_a_1980_);
    lean_dec(v_a_1980_);
    lean_dec_ref(v_m_1979_);
    return v_res_1982_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__4(
    mut v___x_1983_: *mut LeanObject,
    mut v_pu_1984_: u8,
    mut v_sz_1985_: usize,
    mut v_i_1986_: usize,
    mut v_bs_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1988_: u8 = 0;
    let mut v_v_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1988_ = lean_usize_dec_lt(v_i_1986_, v_sz_1985_);
                if v___x_1988_ == 0 {
                    return v_bs_1987_;
                } else {
                    v_v_1989_ = lean_array_uget(v_bs_1987_, v_i_1986_);
                    v___x_1990_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1991_ = lean_array_uset(v_bs_1987_, v_i_1986_, v___x_1990_);
                    v___x_1992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_splitScc_spec__3(v_pu_1984_, v___x_1983_, v_v_1989_);
                    lean_dec(v_v_1989_);
                    v___x_1993_ = 1usize;
                    v___x_1994_ = lean_usize_add(v_i_1986_, v___x_1993_);
                    v___x_1995_ = lean_array_uset(v_bs_x27_1991_, v_i_1986_, v___x_1992_);
                    v_i_1986_ = v___x_1994_;
                    v_bs_1987_ = v___x_1995_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__4___boxed(
    mut v___x_1997_: *mut LeanObject,
    mut v_pu_1998_: *mut LeanObject,
    mut v_sz_1999_: *mut LeanObject,
    mut v_i_2000_: *mut LeanObject,
    mut v_bs_2001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2002_: u8 = 0;
    let mut v_sz_boxed_2003_: usize = 0;
    let mut v_i_boxed_2004_: usize = 0;
    let mut v_res_2005_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2002_ = (lean_unbox(v_pu_1998_) as u8);
    v_sz_boxed_2003_ = lean_unbox_usize(v_sz_1999_);
    lean_dec(v_sz_1999_);
    v_i_boxed_2004_ = lean_unbox_usize(v_i_2000_);
    lean_dec(v_i_2000_);
    v_res_2005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__4(v___x_1997_, v_pu_boxed_2002_, v_sz_boxed_2003_, v_i_boxed_2004_, v_bs_2001_);
    lean_dec_ref(v___x_1997_);
    return v_res_2005_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__12_spec__20(
    mut v___x_2006_: *mut LeanObject,
    mut v_pu_2007_: u8,
    mut v_sz_2008_: usize,
    mut v_i_2009_: usize,
    mut v_bs_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2011_: u8 = 0;
    let mut v_v_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2016_: usize = 0;
    let mut v___x_2017_: usize = 0;
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: usize = 0;
    let mut v___x_2020_: usize = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2011_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
                if v___x_2011_ == 0 {
                    return v_bs_2010_;
                } else {
                    v_v_2012_ = lean_array_uget(v_bs_2010_, v_i_2009_);
                    v___x_2013_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2014_ = lean_array_uset(v_bs_2010_, v_i_2009_, v___x_2013_);
                    v___x_2015_ = lean_array_mk(v_v_2012_);
                    v_sz_2016_ = lean_array_size(v___x_2015_);
                    v___x_2017_ = 0usize;
                    v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__4(v___x_2006_, v_pu_2007_, v_sz_2016_, v___x_2017_, v___x_2015_);
                    v___x_2019_ = 1usize;
                    v___x_2020_ = lean_usize_add(v_i_2009_, v___x_2019_);
                    v___x_2021_ = lean_array_uset(v_bs_x27_2014_, v_i_2009_, v___x_2018_);
                    v_i_2009_ = v___x_2020_;
                    v_bs_2010_ = v___x_2021_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__12_spec__20___boxed(
    mut v___x_2023_: *mut LeanObject,
    mut v_pu_2024_: *mut LeanObject,
    mut v_sz_2025_: *mut LeanObject,
    mut v_i_2026_: *mut LeanObject,
    mut v_bs_2027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2028_: u8 = 0;
    let mut v_sz_boxed_2029_: usize = 0;
    let mut v_i_boxed_2030_: usize = 0;
    let mut v_res_2031_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2028_ = (lean_unbox(v_pu_2024_) as u8);
    v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2025_);
    lean_dec(v_sz_2025_);
    v_i_boxed_2030_ = lean_unbox_usize(v_i_2026_);
    lean_dec(v_i_2026_);
    v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__12_spec__20(v___x_2023_, v_pu_boxed_2028_, v_sz_boxed_2029_, v_i_boxed_2030_, v_bs_2027_);
    lean_dec_ref(v___x_2023_);
    return v_res_2031_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__12(
    mut v_pu_2032_: u8,
    mut v___x_2033_: *mut LeanObject,
    mut v_sz_2034_: usize,
    mut v_i_2035_: usize,
    mut v_bs_2036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2037_: u8 = 0;
    v___x_2037_ = lean_usize_dec_lt(v_i_2035_, v_sz_2034_);
    if v___x_2037_ == 0 {
        return v_bs_2036_;
    } else {
        let mut v_v_2038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
        let mut v_bs_x27_2040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_2042_: usize = 0;
        let mut v___x_2043_: usize = 0;
        let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: usize = 0;
        let mut v___x_2046_: usize = 0;
        let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
        v_v_2038_ = lean_array_uget(v_bs_2036_, v_i_2035_);
        v___x_2039_ = lean_unsigned_to_nat(0);
        v_bs_x27_2040_ = lean_array_uset(v_bs_2036_, v_i_2035_, v___x_2039_);
        v___x_2041_ = lean_array_mk(v_v_2038_);
        v_sz_2042_ = lean_array_size(v___x_2041_);
        v___x_2043_ = 0usize;
        v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__4(v___x_2033_, v_pu_2032_, v_sz_2042_, v___x_2043_, v___x_2041_);
        v___x_2045_ = 1usize;
        v___x_2046_ = lean_usize_add(v_i_2035_, v___x_2045_);
        v___x_2047_ = lean_array_uset(v_bs_x27_2040_, v_i_2035_, v___x_2044_);
        v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__12_spec__20(v___x_2033_, v_pu_2032_, v_sz_2034_, v___x_2046_, v___x_2047_);
        return v___x_2048_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__12___boxed(
    mut v_pu_2049_: *mut LeanObject,
    mut v___x_2050_: *mut LeanObject,
    mut v_sz_2051_: *mut LeanObject,
    mut v_i_2052_: *mut LeanObject,
    mut v_bs_2053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2054_: u8 = 0;
    let mut v_sz_boxed_2055_: usize = 0;
    let mut v_i_boxed_2056_: usize = 0;
    let mut v_res_2057_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2054_ = (lean_unbox(v_pu_2049_) as u8);
    v_sz_boxed_2055_ = lean_unbox_usize(v_sz_2051_);
    lean_dec(v_sz_2051_);
    v_i_boxed_2056_ = lean_unbox_usize(v_i_2052_);
    lean_dec(v_i_2052_);
    v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__12(v_pu_boxed_2054_, v___x_2050_, v_sz_boxed_2055_, v_i_boxed_2056_, v_bs_2053_);
    lean_dec_ref(v___x_2050_);
    return v_res_2057_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20_spec__23___redArg(
    mut v_a_2058_: *mut LeanObject,
    mut v_x_2059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2059_) == 0 {
                    v___x_2060_ = lean_box(0);
                    return v___x_2060_;
                } else {
                    v_key_2061_ = lean_ctor_get(v_x_2059_, 0);
                    v_value_2062_ = lean_ctor_get(v_x_2059_, 1);
                    v_tail_2063_ = lean_ctor_get(v_x_2059_, 2);
                    v___x_2064_ = lean_name_eq(v_key_2061_, v_a_2058_);
                    if v___x_2064_ == 0 {
                        v_x_2059_ = v_tail_2063_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2062_);
                        v___x_2066_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2066_, 0, v_value_2062_);
                        return v___x_2066_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20_spec__23___redArg___boxed(
    mut v_a_2067_: *mut LeanObject,
    mut v_x_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2069_: *mut LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20_spec__23___redArg(v_a_2067_, v_x_2068_);
    lean_dec(v_x_2068_);
    lean_dec(v_a_2067_);
    return v_res_2069_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20___redArg(
    mut v_m_2070_: *mut LeanObject,
    mut v_a_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2075_: u64 = 0;
    let mut v___x_2076_: u64 = 0;
    let mut v___x_2077_: u64 = 0;
    let mut v_fold_2078_: u64 = 0;
    let mut v___x_2079_: u64 = 0;
    let mut v___x_2080_: u64 = 0;
    let mut v___x_2081_: u64 = 0;
    let mut v___x_2082_: usize = 0;
    let mut v___x_2083_: usize = 0;
    let mut v___x_2084_: usize = 0;
    let mut v___x_2085_: usize = 0;
    let mut v___x_2086_: usize = 0;
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: u64 = 0;
    let mut v_hash_2090_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2072_ = lean_ctor_get(v_m_2070_, 1);
                v___x_2073_ = lean_array_get_size(v_buckets_2072_);
                if lean_obj_tag(v_a_2071_) == 0 {
                    v___x_2089_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls_goCode_spec__0___redArg___closed__0);
                    v___y_2075_ = v___x_2089_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2090_ = lean_ctor_get_uint64(
                        v_a_2071_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2075_ = v_hash_2090_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2076_ = 32u64;
                v___x_2077_ = lean_uint64_shift_right(v___y_2075_, v___x_2076_);
                v_fold_2078_ = lean_uint64_xor(v___y_2075_, v___x_2077_);
                v___x_2079_ = 16u64;
                v___x_2080_ = lean_uint64_shift_right(v_fold_2078_, v___x_2079_);
                v___x_2081_ = lean_uint64_xor(v_fold_2078_, v___x_2080_);
                v___x_2082_ = lean_uint64_to_usize(v___x_2081_);
                v___x_2083_ = lean_usize_of_nat(v___x_2073_);
                v___x_2084_ = 1usize;
                v___x_2085_ = lean_usize_sub(v___x_2083_, v___x_2084_);
                v___x_2086_ = lean_usize_land(v___x_2082_, v___x_2085_);
                v___x_2087_ = lean_array_uget_borrowed(v_buckets_2072_, v___x_2086_);
                v___x_2088_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20_spec__23___redArg(v_a_2071_, v___x_2087_);
                return v___x_2088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20___redArg___boxed(
    mut v_m_2091_: *mut LeanObject,
    mut v_a_2092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2093_: *mut LeanObject = core::ptr::null_mut();
    v_res_2093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20___redArg(v_m_2091_, v_a_2092_);
    lean_dec(v_a_2092_);
    lean_dec_ref(v_m_2091_);
    return v_res_2093_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16(
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    v_data_2099_ = lean_ctor_get(v_a_2098_, 2);
    v___x_2100_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20___redArg(v_data_2099_, v_a_2097_);
    if lean_obj_tag(v___x_2100_) == 0 {
        let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
        v___x_2101_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16___closed__0;
        v___x_2102_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2102_, 0, v___x_2101_);
        lean_ctor_set(v___x_2102_, 1, v_a_2098_);
        return v___x_2102_;
    } else {
        let mut v_val_2103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
        v_val_2103_ = lean_ctor_get(v___x_2100_, 0);
        lean_inc(v_val_2103_);
        lean_dec_ref_known(v___x_2100_, 1);
        v___x_2104_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2104_, 0, v_val_2103_);
        lean_ctor_set(v___x_2104_, 1, v_a_2098_);
        return v___x_2104_;
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16___boxed(
    mut v_a_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2107_: *mut LeanObject = core::ptr::null_mut();
    v_res_2107_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16(v_a_2105_, v_a_2106_);
    lean_dec(v_a_2105_);
    return v_res_2107_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31_spec__34___lam__0(
    mut v_d_2108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_index_x3f_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowlink_x3f_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_index_x3f_2109_ = lean_ctor_get(v_d_2108_, 0);
                v_lowlink_x3f_2110_ = lean_ctor_get(v_d_2108_, 1);
                v_isSharedCheck_2118_ = (!lean_is_exclusive(v_d_2108_)) as u8;
                if v_isSharedCheck_2118_ == 0 {
                    v___x_2112_ = v_d_2108_;
                    v_isShared_2113_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_lowlink_x3f_2110_);
                    lean_inc(v_index_x3f_2109_);
                    lean_dec(v_d_2108_);
                    v___x_2112_ = lean_box(0);
                    v_isShared_2113_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2114_ = 0;
                if v_isShared_2113_ == 0 {
                    v___x_2116_ = v___x_2112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_index_x3f_2109_);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_lowlink_x3f_2110_);
                    v___x_2116_ = v_reuseFailAlloc_2117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2116_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2114_,
                );
                return v___x_2116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__22_spec__26(
    mut v_a_2119_: *mut LeanObject,
    mut v_f_2120_: *mut LeanObject,
    mut v_a_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stack_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIndex_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sccs_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stack_2122_ = lean_ctor_get(v_a_2121_, 0);
                v_nextIndex_2123_ = lean_ctor_get(v_a_2121_, 1);
                v_data_2124_ = lean_ctor_get(v_a_2121_, 2);
                v_sccs_2125_ = lean_ctor_get(v_a_2121_, 3);
                v_isSharedCheck_2140_ = (!lean_is_exclusive(v_a_2121_)) as u8;
                if v_isSharedCheck_2140_ == 0 {
                    v___x_2127_ = v_a_2121_;
                    v_isShared_2128_ = v_isSharedCheck_2140_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_sccs_2125_);
                    lean_inc(v_data_2124_);
                    lean_inc(v_nextIndex_2123_);
                    lean_inc(v_stack_2122_);
                    lean_dec(v_a_2121_);
                    v___x_2127_ = lean_box(0);
                    v_isShared_2128_ = v_isSharedCheck_2140_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2129_ = lean_box(0);
                v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20___redArg(v_data_2124_, v_a_2119_);
                if lean_obj_tag(v___x_2136_) == 0 {
                    lean_dec_ref(v_f_2120_);
                    lean_dec(v_a_2119_);
                    v___y_2131_ = v_data_2124_;
                    state = 2;
                    continue;
                } else {
                    v_val_2137_ = lean_ctor_get(v___x_2136_, 0);
                    lean_inc(v_val_2137_);
                    lean_dec_ref_known(v___x_2136_, 1);
                    v___x_2138_ = lean_apply_1(v_f_2120_, v_val_2137_);
                    v___x_2139_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2___redArg(v_data_2124_, v_a_2119_, v___x_2138_);
                    v___y_2131_ = v___x_2139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2128_ == 0 {
                    lean_ctor_set(v___x_2127_, 2, v___y_2131_);
                    v___x_2133_ = v___x_2127_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_stack_2122_);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_nextIndex_2123_);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 2, v___y_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_sccs_2125_);
                    v___x_2133_ = v_reuseFailAlloc_2135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2134_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2134_, 0, v___x_2129_);
                lean_ctor_set(v___x_2134_, 1, v___x_2133_);
                return v___x_2134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31_spec__34(
    mut v_a_2142_: *mut LeanObject,
    mut v_a_2143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    v___f_2144_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31_spec__34___closed__0;
    v___x_2145_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__22_spec__26(v_a_2142_, v___f_2144_, v_a_2143_);
    return v___x_2145_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31(
    mut v_a_2146_: *mut LeanObject,
    mut v_x_2147_: *mut LeanObject,
    mut v_x_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nextIndex_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sccs_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut v_unused_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2173_: u8 = 0;
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: u8 = 0;
    let mut v_nextIndex_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sccs_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v_unused_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2195_: u8 = 0;
    let mut v_unused_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2147_) == 0 {
                    v_nextIndex_2150_ = lean_ctor_get(v_a_2149_, 1);
                    v_data_2151_ = lean_ctor_get(v_a_2149_, 2);
                    v_sccs_2152_ = lean_ctor_get(v_a_2149_, 3);
                    v_isSharedCheck_2162_ = (!lean_is_exclusive(v_a_2149_)) as u8;
                    if v_isSharedCheck_2162_ == 0 {
                        v_unused_2163_ = lean_ctor_get(v_a_2149_, 0);
                        lean_dec(v_unused_2163_);
                        v___x_2154_ = v_a_2149_;
                        v_isShared_2155_ = v_isSharedCheck_2162_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_sccs_2152_);
                        lean_inc(v_data_2151_);
                        lean_inc(v_nextIndex_2150_);
                        lean_dec(v_a_2149_);
                        v___x_2154_ = lean_box(0);
                        v_isShared_2155_ = v_isSharedCheck_2162_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_head_2164_ = lean_ctor_get(v_x_2147_, 0);
                    v_tail_2165_ = lean_ctor_get(v_x_2147_, 1);
                    v_isSharedCheck_2197_ = (!lean_is_exclusive(v_x_2147_)) as u8;
                    if v_isSharedCheck_2197_ == 0 {
                        v___x_2167_ = v_x_2147_;
                        v_isShared_2168_ = v_isSharedCheck_2197_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_tail_2165_);
                        lean_inc(v_head_2164_);
                        lean_dec(v_x_2147_);
                        v___x_2167_ = lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2197_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2156_ = lean_box(0);
                v___x_2157_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2157_, 0, v_x_2148_);
                lean_ctor_set(v___x_2157_, 1, v_sccs_2152_);
                if v_isShared_2155_ == 0 {
                    lean_ctor_set(v___x_2154_, 3, v___x_2157_);
                    lean_ctor_set(v___x_2154_, 0, v_x_2147_);
                    v___x_2159_ = v___x_2154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_x_2147_);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_nextIndex_2150_);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_data_2151_);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 3, v___x_2157_);
                    v___x_2159_ = v_reuseFailAlloc_2161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2160_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2160_, 0, v___x_2156_);
                lean_ctor_set(v___x_2160_, 1, v___x_2159_);
                return v___x_2160_;
            }
            3 => {
                lean_inc(v_head_2164_);
                v___x_2169_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31_spec__34(v_head_2164_, v_a_2149_);
                v_snd_2170_ = lean_ctor_get(v___x_2169_, 1);
                v_isSharedCheck_2195_ = (!lean_is_exclusive(v___x_2169_)) as u8;
                if v_isSharedCheck_2195_ == 0 {
                    v_unused_2196_ = lean_ctor_get(v___x_2169_, 0);
                    lean_dec(v_unused_2196_);
                    v___x_2172_ = v___x_2169_;
                    v_isShared_2173_ = v_isSharedCheck_2195_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_2170_);
                    lean_dec(v___x_2169_);
                    v___x_2172_ = lean_box(0);
                    v_isShared_2173_ = v_isSharedCheck_2195_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_head_2164_);
                if v_isShared_2168_ == 0 {
                    lean_ctor_set(v___x_2167_, 1, v_x_2148_);
                    v___x_2175_ = v___x_2167_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_head_2164_);
                    lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_x_2148_);
                    v___x_2175_ = v_reuseFailAlloc_2194_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2176_ = lean_name_eq(v_a_2146_, v_head_2164_);
                lean_dec(v_head_2164_);
                if v___x_2176_ == 0 {
                    lean_del_object(v___x_2172_);
                    v_x_2147_ = v_tail_2165_;
                    v_x_2148_ = v___x_2175_;
                    v_a_2149_ = v_snd_2170_;
                    state = 0;
                    continue;
                } else {
                    v_nextIndex_2178_ = lean_ctor_get(v_snd_2170_, 1);
                    v_data_2179_ = lean_ctor_get(v_snd_2170_, 2);
                    v_sccs_2180_ = lean_ctor_get(v_snd_2170_, 3);
                    v_isSharedCheck_2192_ = (!lean_is_exclusive(v_snd_2170_)) as u8;
                    if v_isSharedCheck_2192_ == 0 {
                        v_unused_2193_ = lean_ctor_get(v_snd_2170_, 0);
                        lean_dec(v_unused_2193_);
                        v___x_2182_ = v_snd_2170_;
                        v_isShared_2183_ = v_isSharedCheck_2192_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_sccs_2180_);
                        lean_inc(v_data_2179_);
                        lean_inc(v_nextIndex_2178_);
                        lean_dec(v_snd_2170_);
                        v___x_2182_ = lean_box(0);
                        v_isShared_2183_ = v_isSharedCheck_2192_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2184_ = lean_box(0);
                v___x_2185_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2185_, 0, v___x_2175_);
                lean_ctor_set(v___x_2185_, 1, v_sccs_2180_);
                if v_isShared_2183_ == 0 {
                    lean_ctor_set(v___x_2182_, 3, v___x_2185_);
                    lean_ctor_set(v___x_2182_, 0, v_tail_2165_);
                    v___x_2187_ = v___x_2182_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_tail_2165_);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_nextIndex_2178_);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_data_2179_);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 3, v___x_2185_);
                    v___x_2187_ = v_reuseFailAlloc_2191_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2173_ == 0 {
                    lean_ctor_set(v___x_2172_, 1, v___x_2187_);
                    lean_ctor_set(v___x_2172_, 0, v___x_2184_);
                    v___x_2189_ = v___x_2172_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2184_);
                    lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2187_);
                    v___x_2189_ = v_reuseFailAlloc_2190_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31___boxed(
    mut v_a_2198_: *mut LeanObject,
    mut v_x_2199_: *mut LeanObject,
    mut v_x_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2202_: *mut LeanObject = core::ptr::null_mut();
    v_res_2202_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31(v_a_2198_, v_x_2199_, v_x_2200_, v_a_2201_);
    lean_dec(v_a_2198_);
    return v_res_2202_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26(
    mut v_a_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stack_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    v_stack_2205_ = lean_ctor_get(v_a_2204_, 0);
    lean_inc(v_stack_2205_);
    v___x_2206_ = lean_box(0);
    v___x_2207_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___00__private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26_spec__31(v_a_2203_, v_stack_2205_, v___x_2206_, v_a_2204_);
    return v___x_2207_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26___boxed(
    mut v_a_2208_: *mut LeanObject,
    mut v_a_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26(v_a_2208_, v_a_2209_);
    lean_dec(v_a_2208_);
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__22___lam__0(
    mut v_v_2211_: *mut LeanObject,
    mut v_d_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lowlink_x3f_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_x3f_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onStack_2215_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v_unused_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_x3f_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onStack_2225_: u8 = 0;
    let mut v_val_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v_unused_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2211_) == 0 {
                    return v_d_2212_;
                } else {
                    v_lowlink_x3f_2213_ = lean_ctor_get(v_d_2212_, 1);
                    if lean_obj_tag(v_lowlink_x3f_2213_) == 0 {
                        v_index_x3f_2214_ = lean_ctor_get(v_d_2212_, 0);
                        v_onStack_2215_ = lean_ctor_get_uint8(
                            v_d_2212_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_isSharedCheck_2222_ = (!lean_is_exclusive(v_d_2212_)) as u8;
                        if v_isSharedCheck_2222_ == 0 {
                            v_unused_2223_ = lean_ctor_get(v_d_2212_, 1);
                            lean_dec(v_unused_2223_);
                            v___x_2217_ = v_d_2212_;
                            v_isShared_2218_ = v_isSharedCheck_2222_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_index_x3f_2214_);
                            lean_dec(v_d_2212_);
                            v___x_2217_ = lean_box(0);
                            v_isShared_2218_ = v_isSharedCheck_2222_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_index_x3f_2224_ = lean_ctor_get(v_d_2212_, 0);
                        v_onStack_2225_ = lean_ctor_get_uint8(
                            v_d_2212_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_val_2226_ = lean_ctor_get(v_v_2211_, 0);
                        v_val_2227_ = lean_ctor_get(v_lowlink_x3f_2213_, 0);
                        v___x_2228_ = lean_nat_dec_lt(v_val_2227_, v_val_2226_);
                        if v___x_2228_ == 0 {
                            lean_inc(v_index_x3f_2224_);
                            v_isSharedCheck_2235_ = (!lean_is_exclusive(v_d_2212_)) as u8;
                            if v_isSharedCheck_2235_ == 0 {
                                v_unused_2236_ = lean_ctor_get(v_d_2212_, 1);
                                lean_dec(v_unused_2236_);
                                v_unused_2237_ = lean_ctor_get(v_d_2212_, 0);
                                lean_dec(v_unused_2237_);
                                v___x_2230_ = v_d_2212_;
                                v_isShared_2231_ = v_isSharedCheck_2235_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_d_2212_);
                                v___x_2230_ = lean_box(0);
                                v_isShared_2231_ = v_isSharedCheck_2235_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_v_2211_, 1);
                            return v_d_2212_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2218_ == 0 {
                    lean_ctor_set(v___x_2217_, 1, v_v_2211_);
                    v___x_2220_ = v___x_2217_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_index_x3f_2214_);
                    lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_v_2211_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2221_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_onStack_2215_,
                    );
                    v___x_2220_ = v_reuseFailAlloc_2221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2220_;
            }
            3 => {
                if v_isShared_2231_ == 0 {
                    lean_ctor_set(v___x_2230_, 1, v_v_2211_);
                    v___x_2233_ = v___x_2230_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_index_x3f_2224_);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_v_2211_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2234_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_onStack_2225_,
                    );
                    v___x_2233_ = v_reuseFailAlloc_2234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__22(
    mut v_a_2238_: *mut LeanObject,
    mut v_v_2239_: *mut LeanObject,
    mut v_a_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    v___f_2241_ = lean_alloc_closure(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__22___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_2241_, 0, v_v_2239_);
    v___x_2242_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__22_spec__26(v_a_2238_, v___f_2241_, v_a_2240_);
    return v___x_2242_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__25(
    mut v_x_2243_: *mut LeanObject,
    mut v_x_2244_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2243_) == 0 {
        if lean_obj_tag(v_x_2244_) == 0 {
            let mut v___x_2245_: u8 = 0;
            v___x_2245_ = 1;
            return v___x_2245_;
        } else {
            let mut v___x_2246_: u8 = 0;
            v___x_2246_ = 0;
            return v___x_2246_;
        }
    } else {
        if lean_obj_tag(v_x_2244_) == 0 {
            let mut v___x_2247_: u8 = 0;
            v___x_2247_ = 0;
            return v___x_2247_;
        } else {
            let mut v_val_2248_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_2249_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2250_: u8 = 0;
            v_val_2248_ = lean_ctor_get(v_x_2243_, 0);
            v_val_2249_ = lean_ctor_get(v_x_2244_, 0);
            v___x_2250_ = lean_nat_dec_eq(v_val_2248_, v_val_2249_);
            return v___x_2250_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__25___boxed(
    mut v_x_2251_: *mut LeanObject,
    mut v_x_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2253_: u8 = 0;
    let mut v_r_2254_: *mut LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Option_instBEq_beq___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__25(v_x_2251_, v_x_2252_);
    lean_dec(v_x_2252_);
    lean_dec(v_x_2251_);
    v_r_2254_ = lean_box((v_res_2253_) as usize);
    return v_r_2254_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_push___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__23(
    mut v_a_2255_: *mut LeanObject,
    mut v_a_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stack_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIndex_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sccs_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2263_: u8 = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stack_2257_ = lean_ctor_get(v_a_2256_, 0);
                v_nextIndex_2258_ = lean_ctor_get(v_a_2256_, 1);
                v_data_2259_ = lean_ctor_get(v_a_2256_, 2);
                v_sccs_2260_ = lean_ctor_get(v_a_2256_, 3);
                v_isSharedCheck_2276_ = (!lean_is_exclusive(v_a_2256_)) as u8;
                if v_isSharedCheck_2276_ == 0 {
                    v___x_2262_ = v_a_2256_;
                    v_isShared_2263_ = v_isSharedCheck_2276_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_sccs_2260_);
                    lean_inc(v_data_2259_);
                    lean_inc(v_nextIndex_2258_);
                    lean_inc(v_stack_2257_);
                    lean_dec(v_a_2256_);
                    v___x_2262_ = lean_box(0);
                    v_isShared_2263_ = v_isSharedCheck_2276_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2264_ = lean_box(0);
                lean_inc(v_a_2255_);
                v___x_2265_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2265_, 0, v_a_2255_);
                lean_ctor_set(v___x_2265_, 1, v_stack_2257_);
                v___x_2266_ = lean_unsigned_to_nat(1);
                v___x_2267_ = lean_nat_add(v_nextIndex_2258_, v___x_2266_);
                v___x_2268_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2268_, 0, v_nextIndex_2258_);
                v___x_2269_ = 1;
                lean_inc_ref(v___x_2268_);
                v___x_2270_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2270_, 0, v___x_2268_);
                lean_ctor_set(v___x_2270_, 1, v___x_2268_);
                lean_ctor_set_uint8(
                    v___x_2270_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2269_,
                );
                v___x_2271_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2___redArg(v_data_2259_, v_a_2255_, v___x_2270_);
                if v_isShared_2263_ == 0 {
                    lean_ctor_set(v___x_2262_, 2, v___x_2271_);
                    lean_ctor_set(v___x_2262_, 1, v___x_2267_);
                    lean_ctor_set(v___x_2262_, 0, v___x_2265_);
                    v___x_2273_ = v___x_2262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2265_);
                    lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2267_);
                    lean_ctor_set(v_reuseFailAlloc_2275_, 2, v___x_2271_);
                    lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_sccs_2260_);
                    v___x_2273_ = v_reuseFailAlloc_2275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2274_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2274_, 0, v___x_2264_);
                lean_ctor_set(v___x_2274_, 1, v___x_2273_);
                return v___x_2274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__24(
    mut v_successorsOf_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
    mut v_as_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_x3f_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowlink_x3f_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onStack_2300_: u8 = 0;
    let mut v_snd_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_2279_) == 0 {
                    lean_dec(v_a_2278_);
                    lean_dec_ref(v_successorsOf_2277_);
                    v___x_2281_ = lean_box(0);
                    v___x_2282_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2282_, 0, v___x_2281_);
                    lean_ctor_set(v___x_2282_, 1, v___y_2280_);
                    return v___x_2282_;
                } else {
                    v_head_2283_ = lean_ctor_get(v_as_2279_, 0);
                    lean_inc(v_head_2283_);
                    v_tail_2284_ = lean_ctor_get(v_as_2279_, 1);
                    lean_inc(v_tail_2284_);
                    lean_dec_ref_known(v_as_2279_, 2);
                    v___x_2289_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16(v_head_2283_, v___y_2280_);
                    v_fst_2290_ = lean_ctor_get(v___x_2289_, 0);
                    lean_inc(v_fst_2290_);
                    v_index_x3f_2291_ = lean_ctor_get(v_fst_2290_, 0);
                    lean_inc(v_index_x3f_2291_);
                    if lean_obj_tag(v_index_x3f_2291_) == 0 {
                        lean_dec(v_fst_2290_);
                        v_snd_2292_ = lean_ctor_get(v___x_2289_, 1);
                        lean_inc(v_snd_2292_);
                        lean_dec_ref(v___x_2289_);
                        lean_inc(v_head_2283_);
                        lean_inc_ref(v_successorsOf_2277_);
                        v___x_2293_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17(v_successorsOf_2277_, v_head_2283_, v_snd_2292_);
                        v_snd_2294_ = lean_ctor_get(v___x_2293_, 1);
                        lean_inc(v_snd_2294_);
                        lean_dec_ref(v___x_2293_);
                        v___x_2295_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16(v_head_2283_, v_snd_2294_);
                        lean_dec(v_head_2283_);
                        v_fst_2296_ = lean_ctor_get(v___x_2295_, 0);
                        lean_inc(v_fst_2296_);
                        v_snd_2297_ = lean_ctor_get(v___x_2295_, 1);
                        lean_inc(v_snd_2297_);
                        lean_dec_ref(v___x_2295_);
                        v_lowlink_x3f_2298_ = lean_ctor_get(v_fst_2296_, 1);
                        lean_inc(v_lowlink_x3f_2298_);
                        lean_dec(v_fst_2296_);
                        lean_inc(v_a_2278_);
                        v___x_2299_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__22(v_a_2278_, v_lowlink_x3f_2298_, v_snd_2297_);
                        v___y_2286_ = v___x_2299_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_head_2283_);
                        v_onStack_2300_ = lean_ctor_get_uint8(
                            v_fst_2290_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        lean_dec(v_fst_2290_);
                        if v_onStack_2300_ == 0 {
                            lean_dec_ref_known(v_index_x3f_2291_, 1);
                            v_snd_2301_ = lean_ctor_get(v___x_2289_, 1);
                            lean_inc(v_snd_2301_);
                            lean_dec_ref(v___x_2289_);
                            v_as_2279_ = v_tail_2284_;
                            v___y_2280_ = v_snd_2301_;
                            state = 0;
                            continue;
                        } else {
                            v_snd_2303_ = lean_ctor_get(v___x_2289_, 1);
                            lean_inc(v_snd_2303_);
                            lean_dec_ref(v___x_2289_);
                            lean_inc(v_a_2278_);
                            v___x_2304_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__22(v_a_2278_, v_index_x3f_2291_, v_snd_2303_);
                            v___y_2286_ = v___x_2304_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_snd_2287_ = lean_ctor_get(v___y_2286_, 1);
                lean_inc(v_snd_2287_);
                lean_dec_ref(v___y_2286_);
                v_as_2279_ = v_tail_2284_;
                v___y_2280_ = v_snd_2287_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17(
    mut v_successorsOf_2305_: *mut LeanObject,
    mut v_a_2306_: *mut LeanObject,
    mut v_a_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v_index_x3f_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowlink_x3f_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_n(v_a_2306_, 3);
                v___x_2308_ = l___private_Lean_Util_SCC_0__Lean_SCC_push___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__23(v_a_2306_, v_a_2307_);
                v_snd_2309_ = lean_ctor_get(v___x_2308_, 1);
                lean_inc(v_snd_2309_);
                lean_dec_ref(v___x_2308_);
                lean_inc_ref(v_successorsOf_2305_);
                v___x_2310_ = lean_apply_1(v_successorsOf_2305_, v_a_2306_);
                v___x_2311_ = l_List_forM___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__24(v_successorsOf_2305_, v_a_2306_, v___x_2310_, v_snd_2309_);
                v_snd_2312_ = lean_ctor_get(v___x_2311_, 1);
                lean_inc(v_snd_2312_);
                lean_dec_ref(v___x_2311_);
                v___x_2313_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16(v_a_2306_, v_snd_2312_);
                v_fst_2314_ = lean_ctor_get(v___x_2313_, 0);
                v_snd_2315_ = lean_ctor_get(v___x_2313_, 1);
                v_isSharedCheck_2327_ = (!lean_is_exclusive(v___x_2313_)) as u8;
                if v_isSharedCheck_2327_ == 0 {
                    v___x_2317_ = v___x_2313_;
                    v_isShared_2318_ = v_isSharedCheck_2327_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2315_);
                    lean_inc(v_fst_2314_);
                    lean_dec(v___x_2313_);
                    v___x_2317_ = lean_box(0);
                    v_isShared_2318_ = v_isSharedCheck_2327_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_index_x3f_2319_ = lean_ctor_get(v_fst_2314_, 0);
                lean_inc(v_index_x3f_2319_);
                v_lowlink_x3f_2320_ = lean_ctor_get(v_fst_2314_, 1);
                lean_inc(v_lowlink_x3f_2320_);
                lean_dec(v_fst_2314_);
                v___x_2321_ = l_Option_instBEq_beq___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__25(v_lowlink_x3f_2320_, v_index_x3f_2319_);
                lean_dec(v_index_x3f_2319_);
                lean_dec(v_lowlink_x3f_2320_);
                if v___x_2321_ == 0 {
                    lean_dec(v_a_2306_);
                    v___x_2322_ = lean_box(0);
                    if v_isShared_2318_ == 0 {
                        lean_ctor_set(v___x_2317_, 0, v___x_2322_);
                        v___x_2324_ = v___x_2317_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
                        lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_snd_2315_);
                        v___x_2324_ = v_reuseFailAlloc_2325_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2317_);
                    v___x_2326_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___00__private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17_spec__26(v_a_2306_, v_snd_2315_);
                    lean_dec(v_a_2306_);
                    return v___x_2326_;
                }
            }
            2 => {
                return v___x_2324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__18(
    mut v_successorsOf_2328_: *mut LeanObject,
    mut v_as_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_x3f_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_2329_) == 0 {
                    lean_dec_ref(v_successorsOf_2328_);
                    v___x_2331_ = lean_box(0);
                    v___x_2332_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2332_, 0, v___x_2331_);
                    lean_ctor_set(v___x_2332_, 1, v___y_2330_);
                    return v___x_2332_;
                } else {
                    v_head_2333_ = lean_ctor_get(v_as_2329_, 0);
                    lean_inc(v_head_2333_);
                    v_tail_2334_ = lean_ctor_get(v_as_2329_, 1);
                    lean_inc(v_tail_2334_);
                    lean_dec_ref_known(v_as_2329_, 2);
                    v___x_2335_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16(v_head_2333_, v___y_2330_);
                    v_fst_2336_ = lean_ctor_get(v___x_2335_, 0);
                    lean_inc(v_fst_2336_);
                    v_index_x3f_2337_ = lean_ctor_get(v_fst_2336_, 0);
                    lean_inc(v_index_x3f_2337_);
                    lean_dec(v_fst_2336_);
                    if lean_obj_tag(v_index_x3f_2337_) == 0 {
                        v_snd_2338_ = lean_ctor_get(v___x_2335_, 1);
                        lean_inc(v_snd_2338_);
                        lean_dec_ref(v___x_2335_);
                        lean_inc_ref(v_successorsOf_2328_);
                        v___x_2339_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__17(v_successorsOf_2328_, v_head_2333_, v_snd_2338_);
                        v_snd_2340_ = lean_ctor_get(v___x_2339_, 1);
                        lean_inc(v_snd_2340_);
                        lean_dec_ref(v___x_2339_);
                        v_as_2329_ = v_tail_2334_;
                        v___y_2330_ = v_snd_2340_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref_known(v_index_x3f_2337_, 1);
                        lean_dec(v_head_2333_);
                        v_snd_2342_ = lean_ctor_get(v___x_2335_, 1);
                        lean_inc(v_snd_2342_);
                        lean_dec_ref(v___x_2335_);
                        v_as_2329_ = v_tail_2334_;
                        v___y_2330_ = v_snd_2342_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11___closed__0()
-> *mut LeanObject {
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    v___x_2344_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1_once), _init_l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1);
    v___x_2345_ = lean_unsigned_to_nat(0);
    v___x_2346_ = lean_box(0);
    v___x_2347_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2347_, 0, v___x_2346_);
    lean_ctor_set(v___x_2347_, 1, v___x_2345_);
    lean_ctor_set(v___x_2347_, 2, v___x_2344_);
    lean_ctor_set(v___x_2347_, 3, v___x_2346_);
    return v___x_2347_;
}
pub unsafe fn l_Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11(
    mut v_vertices_2348_: *mut LeanObject,
    mut v_successorsOf_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sccs_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    v___x_2350_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11___closed__0_once
        ),
        _init_l_Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11___closed__0,
    );
    v___x_2351_ =
        l_List_forM___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__18(
            v_successorsOf_2349_,
            v_vertices_2348_,
            v___x_2350_,
        );
    v_snd_2352_ = lean_ctor_get(v___x_2351_, 1);
    lean_inc(v_snd_2352_);
    lean_dec_ref(v___x_2351_);
    v_sccs_2353_ = lean_ctor_get(v_snd_2352_, 3);
    lean_inc(v_sccs_2353_);
    lean_dec(v_snd_2352_);
    v___x_2354_ = l_List_reverse___redArg(v_sccs_2353_);
    return v___x_2354_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_splitScc_spec__5(
    mut v_x_2355_: *mut LeanObject,
    mut v_x_2356_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2356_) == 0 {
        lean_inc(v_x_2355_);
        return v_x_2355_;
    } else {
        let mut v_key_2357_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
        v_key_2357_ = lean_ctor_get(v_x_2356_, 0);
        v_tail_2358_ = lean_ctor_get(v_x_2356_, 2);
        v___x_2359_ =
            l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_splitScc_spec__5(
                v_x_2355_,
                v_tail_2358_,
            );
        lean_inc(v_key_2357_);
        v___x_2360_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2360_, 0, v_key_2357_);
        lean_ctor_set(v___x_2360_, 1, v___x_2359_);
        return v___x_2360_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_splitScc_spec__5___boxed(
    mut v_x_2361_: *mut LeanObject,
    mut v_x_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2363_: *mut LeanObject = core::ptr::null_mut();
    v_res_2363_ =
        l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_splitScc_spec__5(
            v_x_2361_, v_x_2362_,
        );
    lean_dec(v_x_2362_);
    lean_dec(v_x_2361_);
    return v_res_2363_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_splitScc_spec__6(
    mut v_as_2364_: *mut LeanObject,
    mut v_i_2365_: usize,
    mut v_stop_2366_: usize,
    mut v_b_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2368_: u8 = 0;
    let mut v___x_2369_: usize = 0;
    let mut v___x_2370_: usize = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2368_ = lean_usize_dec_eq(v_i_2365_, v_stop_2366_);
                if v___x_2368_ == 0 {
                    v___x_2369_ = 1usize;
                    v___x_2370_ = lean_usize_sub(v_i_2365_, v___x_2369_);
                    v___x_2371_ = lean_array_uget_borrowed(v_as_2364_, v___x_2370_);
                    v___x_2372_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_splitScc_spec__5(v_b_2367_, v___x_2371_);
                    lean_dec(v_b_2367_);
                    v_i_2365_ = v___x_2370_;
                    v_b_2367_ = v___x_2372_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2367_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_splitScc_spec__6___boxed(
    mut v_as_2374_: *mut LeanObject,
    mut v_i_2375_: *mut LeanObject,
    mut v_stop_2376_: *mut LeanObject,
    mut v_b_2377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2378_: usize = 0;
    let mut v_stop_boxed_2379_: usize = 0;
    let mut v_res_2380_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2378_ = lean_unbox_usize(v_i_2375_);
    lean_dec(v_i_2375_);
    v_stop_boxed_2379_ = lean_unbox_usize(v_stop_2376_);
    lean_dec(v_stop_2376_);
    v_res_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_splitScc_spec__6(v_as_2374_, v_i_boxed_2378_, v_stop_boxed_2379_, v_b_2377_);
    lean_dec_ref(v_as_2374_);
    return v_res_2380_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__7___redArg(
    mut v_pu_2381_: u8,
    mut v_declMap_2382_: *mut LeanObject,
    mut v_sz_2383_: usize,
    mut v_i_2384_: usize,
    mut v_bs_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: usize = 0;
    let mut v___x_2404_: usize = 0;
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2411_: usize = 0;
    let mut v___x_2412_: usize = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_unused_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2387_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
                if v___x_2387_ == 0 {
                    v___x_2388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2388_, 0, v_bs_2385_);
                    return v___x_2388_;
                } else {
                    v_v_2389_ = lean_array_uget_borrowed(v_bs_2385_, v_i_2384_);
                    lean_inc(v_v_2389_);
                    v___x_2390_ = l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls(v_pu_2381_, v_declMap_2382_, v_v_2389_);
                    v_toSignature_2391_ = lean_ctor_get(v_v_2389_, 0);
                    v_name_2392_ = lean_ctor_get(v_toSignature_2391_, 0);
                    lean_inc(v_name_2392_);
                    v_buckets_2393_ = lean_ctor_get(v___x_2390_, 1);
                    v_isSharedCheck_2414_ = (!lean_is_exclusive(v___x_2390_)) as u8;
                    if v_isSharedCheck_2414_ == 0 {
                        v_unused_2415_ = lean_ctor_get(v___x_2390_, 0);
                        lean_dec(v_unused_2415_);
                        v___x_2395_ = v___x_2390_;
                        v_isShared_2396_ = v_isSharedCheck_2414_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_buckets_2393_);
                        lean_dec(v___x_2390_);
                        v___x_2395_ = lean_box(0);
                        v_isShared_2396_ = v_isSharedCheck_2414_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2397_ = lean_unsigned_to_nat(0);
                v_bs_x27_2398_ = lean_array_uset(v_bs_2385_, v_i_2384_, v___x_2397_);
                v___x_2408_ = lean_box(0);
                v___x_2409_ = lean_array_get_size(v_buckets_2393_);
                v___x_2410_ = lean_nat_dec_lt(v___x_2397_, v___x_2409_);
                if v___x_2410_ == 0 {
                    lean_dec_ref(v_buckets_2393_);
                    v___y_2400_ = v___x_2408_;
                    state = 2;
                    continue;
                } else {
                    v___x_2411_ = lean_usize_of_nat(v___x_2409_);
                    v___x_2412_ = 0usize;
                    v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_splitScc_spec__6(v_buckets_2393_, v___x_2411_, v___x_2412_, v___x_2408_);
                    lean_dec_ref(v_buckets_2393_);
                    v___y_2400_ = v___x_2413_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2396_ == 0 {
                    lean_ctor_set(v___x_2395_, 1, v___y_2400_);
                    lean_ctor_set(v___x_2395_, 0, v_name_2392_);
                    v___x_2402_ = v___x_2395_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_name_2392_);
                    lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___y_2400_);
                    v___x_2402_ = v_reuseFailAlloc_2407_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2403_ = 1usize;
                v___x_2404_ = lean_usize_add(v_i_2384_, v___x_2403_);
                v___x_2405_ = lean_array_uset(v_bs_x27_2398_, v_i_2384_, v___x_2402_);
                v_i_2384_ = v___x_2404_;
                v_bs_2385_ = v___x_2405_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__7___redArg___boxed(
    mut v_pu_2416_: *mut LeanObject,
    mut v_declMap_2417_: *mut LeanObject,
    mut v_sz_2418_: *mut LeanObject,
    mut v_i_2419_: *mut LeanObject,
    mut v_bs_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2422_: u8 = 0;
    let mut v_sz_boxed_2423_: usize = 0;
    let mut v_i_boxed_2424_: usize = 0;
    let mut v_res_2425_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2422_ = (lean_unbox(v_pu_2416_) as u8);
    v_sz_boxed_2423_ = lean_unbox_usize(v_sz_2418_);
    lean_dec(v_sz_2418_);
    v_i_boxed_2424_ = lean_unbox_usize(v_i_2419_);
    lean_dec(v_i_2419_);
    v_res_2425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__7___redArg(v_pu_boxed_2422_, v_declMap_2417_, v_sz_boxed_2423_, v_i_boxed_2424_, v_bs_2420_);
    lean_dec_ref(v_declMap_2417_);
    return v_res_2425_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_splitScc_spec__10(
    mut v_a_2426_: *mut LeanObject,
    mut v_a_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v_name_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut v_unused_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2426_) == 0 {
                    v___x_2428_ = l_List_reverse___redArg(v_a_2427_);
                    return v___x_2428_;
                } else {
                    v_head_2429_ = lean_ctor_get(v_a_2426_, 0);
                    v_toSignature_2430_ = lean_ctor_get(v_head_2429_, 0);
                    lean_inc_ref(v_toSignature_2430_);
                    v_tail_2431_ = lean_ctor_get(v_a_2426_, 1);
                    v_isSharedCheck_2440_ = (!lean_is_exclusive(v_a_2426_)) as u8;
                    if v_isSharedCheck_2440_ == 0 {
                        v_unused_2441_ = lean_ctor_get(v_a_2426_, 0);
                        lean_dec(v_unused_2441_);
                        v___x_2433_ = v_a_2426_;
                        v_isShared_2434_ = v_isSharedCheck_2440_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2431_);
                        lean_dec(v_a_2426_);
                        v___x_2433_ = lean_box(0);
                        v_isShared_2434_ = v_isSharedCheck_2440_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_2435_ = lean_ctor_get(v_toSignature_2430_, 0);
                lean_inc(v_name_2435_);
                lean_dec_ref(v_toSignature_2430_);
                if v_isShared_2434_ == 0 {
                    lean_ctor_set(v___x_2433_, 1, v_a_2427_);
                    lean_ctor_set(v___x_2433_, 0, v_name_2435_);
                    v___x_2437_ = v___x_2433_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_name_2435_);
                    lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_a_2427_);
                    v___x_2437_ = v_reuseFailAlloc_2439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2426_ = v_tail_2431_;
                v_a_2427_ = v___x_2437_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__1(
    mut v_sz_2442_: usize,
    mut v_i_2443_: usize,
    mut v_bs_2444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2445_: u8 = 0;
    let mut v_v_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: usize = 0;
    let mut v___x_2453_: usize = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2445_ = lean_usize_dec_lt(v_i_2443_, v_sz_2442_);
                if v___x_2445_ == 0 {
                    return v_bs_2444_;
                } else {
                    v_v_2446_ = lean_array_uget(v_bs_2444_, v_i_2443_);
                    v_toSignature_2447_ = lean_ctor_get(v_v_2446_, 0);
                    v_name_2448_ = lean_ctor_get(v_toSignature_2447_, 0);
                    lean_inc(v_name_2448_);
                    v___x_2449_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2450_ = lean_array_uset(v_bs_2444_, v_i_2443_, v___x_2449_);
                    v___x_2451_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2451_, 0, v_name_2448_);
                    lean_ctor_set(v___x_2451_, 1, v_v_2446_);
                    v___x_2452_ = 1usize;
                    v___x_2453_ = lean_usize_add(v_i_2443_, v___x_2452_);
                    v___x_2454_ = lean_array_uset(v_bs_x27_2450_, v_i_2443_, v___x_2451_);
                    v_i_2443_ = v___x_2453_;
                    v_bs_2444_ = v___x_2454_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__1___boxed(
    mut v_sz_2456_: *mut LeanObject,
    mut v_i_2457_: *mut LeanObject,
    mut v_bs_2458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2459_: usize = 0;
    let mut v_i_boxed_2460_: usize = 0;
    let mut v_res_2461_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2459_ = lean_unbox_usize(v_sz_2456_);
    lean_dec(v_sz_2456_);
    v_i_boxed_2460_ = lean_unbox_usize(v_i_2457_);
    lean_dec(v_i_2457_);
    v_res_2461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__1(v_sz_boxed_2459_, v_i_boxed_2460_, v_bs_2458_);
    return v_res_2461_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_splitScc_spec__0(
    mut v_a_2462_: *mut LeanObject,
    mut v_a_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2462_) == 0 {
                    v___x_2464_ = l_List_reverse___redArg(v_a_2463_);
                    return v___x_2464_;
                } else {
                    v_head_2465_ = lean_ctor_get(v_a_2462_, 0);
                    v_tail_2466_ = lean_ctor_get(v_a_2462_, 1);
                    v_isSharedCheck_2475_ = (!lean_is_exclusive(v_a_2462_)) as u8;
                    if v_isSharedCheck_2475_ == 0 {
                        v___x_2468_ = v_a_2462_;
                        v_isShared_2469_ = v_isSharedCheck_2475_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2466_);
                        lean_inc(v_head_2465_);
                        lean_dec(v_a_2462_);
                        v___x_2468_ = lean_box(0);
                        v_isShared_2469_ = v_isSharedCheck_2475_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2470_ = l_Lean_MessageData_ofName(v_head_2465_);
                if v_isShared_2469_ == 0 {
                    lean_ctor_set(v___x_2468_, 1, v_a_2463_);
                    lean_ctor_set(v___x_2468_, 0, v___x_2470_);
                    v___x_2472_ = v___x_2468_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2470_);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_a_2463_);
                    v___x_2472_ = v_reuseFailAlloc_2474_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2462_ = v_tail_2466_;
                v_a_2463_ = v___x_2472_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_splitScc_spec__13(
    mut v_a_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2476_) == 0 {
                    v___x_2478_ = l_List_reverse___redArg(v_a_2477_);
                    return v___x_2478_;
                } else {
                    v_head_2479_ = lean_ctor_get(v_a_2476_, 0);
                    v_tail_2480_ = lean_ctor_get(v_a_2476_, 1);
                    v_isSharedCheck_2491_ = (!lean_is_exclusive(v_a_2476_)) as u8;
                    if v_isSharedCheck_2491_ == 0 {
                        v___x_2482_ = v_a_2476_;
                        v_isShared_2483_ = v_isSharedCheck_2491_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2480_);
                        lean_inc(v_head_2479_);
                        lean_dec(v_a_2476_);
                        v___x_2482_ = lean_box(0);
                        v_isShared_2483_ = v_isSharedCheck_2491_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2484_ = lean_box(0);
                v___x_2485_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_splitScc_spec__0(
                    v_head_2479_,
                    v___x_2484_,
                );
                v___x_2486_ = l_Lean_MessageData_ofList(v___x_2485_);
                if v_isShared_2483_ == 0 {
                    lean_ctor_set(v___x_2482_, 1, v_a_2477_);
                    lean_ctor_set(v___x_2482_, 0, v___x_2486_);
                    v___x_2488_ = v___x_2482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2486_);
                    lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_a_2477_);
                    v___x_2488_ = v_reuseFailAlloc_2490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2476_ = v_tail_2480_;
                v_a_2477_ = v___x_2488_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__8_spec__11(
    mut v_as_2492_: *mut LeanObject,
    mut v_sz_2493_: usize,
    mut v_i_2494_: usize,
    mut v_b_2495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2496_: u8 = 0;
    let mut v_a_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: usize = 0;
    let mut v___x_2502_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2496_ = lean_usize_dec_lt(v_i_2494_, v_sz_2493_);
                if v___x_2496_ == 0 {
                    return v_b_2495_;
                } else {
                    v_a_2497_ = lean_array_uget_borrowed(v_as_2492_, v_i_2494_);
                    v_fst_2498_ = lean_ctor_get(v_a_2497_, 0);
                    v_snd_2499_ = lean_ctor_get(v_a_2497_, 1);
                    lean_inc(v_snd_2499_);
                    lean_inc(v_fst_2498_);
                    v_r_2500_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2___redArg(v_b_2495_, v_fst_2498_, v_snd_2499_);
                    v___x_2501_ = 1usize;
                    v___x_2502_ = lean_usize_add(v_i_2494_, v___x_2501_);
                    v_i_2494_ = v___x_2502_;
                    v_b_2495_ = v_r_2500_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__8_spec__11___boxed(
    mut v_as_2504_: *mut LeanObject,
    mut v_sz_2505_: *mut LeanObject,
    mut v_i_2506_: *mut LeanObject,
    mut v_b_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2508_: usize = 0;
    let mut v_i_boxed_2509_: usize = 0;
    let mut v_res_2510_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2508_ = lean_unbox_usize(v_sz_2505_);
    lean_dec(v_sz_2505_);
    v_i_boxed_2509_ = lean_unbox_usize(v_i_2506_);
    lean_dec(v_i_2506_);
    v_res_2510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__8_spec__11(v_as_2504_, v_sz_boxed_2508_, v_i_boxed_2509_, v_b_2507_);
    lean_dec_ref(v_as_2504_);
    return v_res_2510_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__8(
    mut v_m_2511_: *mut LeanObject,
    mut v_l_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2513_: usize = 0;
    let mut v___x_2514_: usize = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    v_sz_2513_ = lean_array_size(v_l_2512_);
    v___x_2514_ = 0usize;
    v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__8_spec__11(v_l_2512_, v_sz_2513_, v___x_2514_, v_m_2511_);
    return v___x_2515_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__8___boxed(
    mut v_m_2516_: *mut LeanObject,
    mut v_l_2517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2518_: *mut LeanObject = core::ptr::null_mut();
    v_res_2518_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__8(v_m_2516_, v_l_2517_);
    lean_dec_ref(v_l_2517_);
    return v_res_2518_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_splitScc___closed__5() -> *mut LeanObject {
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    v___x_2527_ = l_Lean_Compiler_LCNF_splitScc___closed__2;
    v___x_2528_ = l_Lean_Compiler_LCNF_splitScc___closed__4;
    v___x_2529_ = l_Lean_Name_append(v___x_2528_, v___x_2527_);
    return v___x_2529_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_splitScc___closed__7() -> *mut LeanObject {
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    v___x_2531_ = l_Lean_Compiler_LCNF_splitScc___closed__6;
    v___x_2532_ = l_Lean_stringToMessageData(v___x_2531_);
    return v___x_2532_;
}
pub unsafe fn l_Lean_Compiler_LCNF_splitScc(
    mut v_pu_2533_: u8,
    mut v_scc_2534_: *mut LeanObject,
    mut v_a_2535_: *mut LeanObject,
    mut v_a_2536_: *mut LeanObject,
    mut v_a_2537_: *mut LeanObject,
    mut v_a_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    let mut v_sz_2543_: usize = 0;
    let mut v___x_2544_: usize = 0;
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declMap_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v_inheritedTraceOptions_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2555_: u8 = 0;
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2564_: usize = 0;
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_a_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2593_: u8 = 0;
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2540_ = lean_array_get_size(v_scc_2534_);
                v___x_2541_ = lean_unsigned_to_nat(1);
                v___x_2542_ = lean_nat_dec_eq(v___x_2540_, v___x_2541_);
                if v___x_2542_ == 0 {
                    v_sz_2543_ = lean_array_size(v_scc_2534_);
                    v___x_2544_ = 0usize;
                    lean_inc_ref_n(v_scc_2534_, 2);
                    v___x_2545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__1(v_sz_2543_, v___x_2544_, v_scc_2534_);
                    v___x_2546_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1_once), _init_l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_SplitScc_findSccCalls___closed__1);
                    v_declMap_2547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2(v___x_2546_, v___x_2545_);
                    lean_dec_ref(v___x_2545_);
                    v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__7___redArg(v_pu_2533_, v_declMap_2547_, v_sz_2543_, v___x_2544_, v_scc_2534_);
                    if lean_obj_tag(v___x_2548_) == 0 {
                        v_options_2549_ = lean_ctor_get(v_a_2537_, 2);
                        v_a_2550_ = lean_ctor_get(v___x_2548_, 0);
                        v_isSharedCheck_2585_ = (!lean_is_exclusive(v___x_2548_)) as u8;
                        if v_isSharedCheck_2585_ == 0 {
                            v___x_2552_ = v___x_2548_;
                            v_isShared_2553_ = v_isSharedCheck_2585_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2550_);
                            lean_dec(v___x_2548_);
                            v___x_2552_ = lean_box(0);
                            v_isShared_2553_ = v_isSharedCheck_2585_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_declMap_2547_);
                        lean_dec_ref(v_scc_2534_);
                        v_a_2586_ = lean_ctor_get(v___x_2548_, 0);
                        v_isSharedCheck_2593_ = (!lean_is_exclusive(v___x_2548_)) as u8;
                        if v_isSharedCheck_2593_ == 0 {
                            v___x_2588_ = v___x_2548_;
                            v_isShared_2589_ = v_isSharedCheck_2593_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2586_);
                            lean_dec(v___x_2548_);
                            v___x_2588_ = lean_box(0);
                            v_isShared_2589_ = v_isSharedCheck_2593_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_2594_ = lean_mk_empty_array_with_capacity(v___x_2541_);
                    v___x_2595_ = lean_array_push(v___x_2594_, v_scc_2534_);
                    v___x_2596_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2596_, 0, v___x_2595_);
                    return v___x_2596_;
                }
            }
            1 => {
                v_inheritedTraceOptions_2554_ = lean_ctor_get(v_a_2537_, 13);
                v_hasTrace_2555_ = lean_ctor_get_uint8(
                    v_options_2549_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_2556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__8(v___x_2546_, v_a_2550_);
                lean_dec(v_a_2550_);
                v___f_2557_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_splitScc___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2557_, 0, v___x_2556_);
                v___x_2558_ = lean_array_to_list(v_scc_2534_);
                v___x_2559_ = lean_box(0);
                v___x_2560_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_splitScc_spec__10(
                    v___x_2558_,
                    v___x_2559_,
                );
                v___x_2561_ = l_Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11(
                    v___x_2560_,
                    v___f_2557_,
                );
                if v_hasTrace_2555_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_2569_ = l_Lean_Compiler_LCNF_splitScc___closed__2;
                    v___x_2570_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_splitScc___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_splitScc___closed__5_once),
                        _init_l_Lean_Compiler_LCNF_splitScc___closed__5,
                    );
                    v___x_2571_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2554_,
                        v_options_2549_,
                        v___x_2570_,
                    );
                    if v___x_2571_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_2572_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_splitScc___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_splitScc___closed__7_once),
                            _init_l_Lean_Compiler_LCNF_splitScc___closed__7,
                        );
                        lean_inc(v___x_2561_);
                        v___x_2573_ =
                            l_List_mapTR_loop___at___00Lean_Compiler_LCNF_splitScc_spec__13(
                                v___x_2561_,
                                v___x_2559_,
                            );
                        v___x_2574_ = l_Lean_MessageData_ofList(v___x_2573_);
                        v___x_2575_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2575_, 0, v___x_2572_);
                        lean_ctor_set(v___x_2575_, 1, v___x_2574_);
                        v___x_2576_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_splitScc_spec__14(
                            v___x_2569_,
                            v___x_2575_,
                            v_a_2535_,
                            v_a_2536_,
                            v_a_2537_,
                            v_a_2538_,
                        );
                        if lean_obj_tag(v___x_2576_) == 0 {
                            lean_dec_ref_known(v___x_2576_, 1);
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_2561_);
                            lean_del_object(v___x_2552_);
                            lean_dec_ref(v_declMap_2547_);
                            v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
                            v_isSharedCheck_2584_ = (!lean_is_exclusive(v___x_2576_)) as u8;
                            if v_isSharedCheck_2584_ == 0 {
                                v___x_2579_ = v___x_2576_;
                                v_isShared_2580_ = v_isSharedCheck_2584_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2577_);
                                lean_dec(v___x_2576_);
                                v___x_2579_ = lean_box(0);
                                v_isShared_2580_ = v_isSharedCheck_2584_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2563_ = lean_array_mk(v___x_2561_);
                v_sz_2564_ = lean_array_size(v___x_2563_);
                v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__12(v_pu_2533_, v_declMap_2547_, v_sz_2564_, v___x_2544_, v___x_2563_);
                lean_dec_ref(v_declMap_2547_);
                if v_isShared_2553_ == 0 {
                    lean_ctor_set(v___x_2552_, 0, v___x_2565_);
                    v___x_2567_ = v___x_2552_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
                    v___x_2567_ = v_reuseFailAlloc_2568_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2567_;
            }
            4 => {
                if v_isShared_2580_ == 0 {
                    v___x_2582_ = v___x_2579_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
                    v___x_2582_ = v_reuseFailAlloc_2583_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2582_;
            }
            6 => {
                if v_isShared_2589_ == 0 {
                    v___x_2591_ = v___x_2588_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
                    v___x_2591_ = v_reuseFailAlloc_2592_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_splitScc___boxed(
    mut v_pu_2597_: *mut LeanObject,
    mut v_scc_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_a_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
    mut v_a_2602_: *mut LeanObject,
    mut v_a_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2604_: u8 = 0;
    let mut v_res_2605_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2604_ = (lean_unbox(v_pu_2597_) as u8);
    v_res_2605_ = l_Lean_Compiler_LCNF_splitScc(
        v_pu_boxed_2604_,
        v_scc_2598_,
        v_a_2599_,
        v_a_2600_,
        v_a_2601_,
        v_a_2602_,
    );
    lean_dec(v_a_2602_);
    lean_dec_ref(v_a_2601_);
    lean_dec(v_a_2600_);
    lean_dec_ref(v_a_2599_);
    return v_res_2605_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__7(
    mut v_pu_2606_: u8,
    mut v_declMap_2607_: *mut LeanObject,
    mut v_sz_2608_: usize,
    mut v_i_2609_: usize,
    mut v_bs_2610_: *mut LeanObject,
    mut v___y_2611_: *mut LeanObject,
    mut v___y_2612_: *mut LeanObject,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__7___redArg(v_pu_2606_, v_declMap_2607_, v_sz_2608_, v_i_2609_, v_bs_2610_);
    return v___x_2616_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__7___boxed(
    mut v_pu_2617_: *mut LeanObject,
    mut v_declMap_2618_: *mut LeanObject,
    mut v_sz_2619_: *mut LeanObject,
    mut v_i_2620_: *mut LeanObject,
    mut v_bs_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2627_: u8 = 0;
    let mut v_sz_boxed_2628_: usize = 0;
    let mut v_i_boxed_2629_: usize = 0;
    let mut v_res_2630_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2627_ = (lean_unbox(v_pu_2617_) as u8);
    v_sz_boxed_2628_ = lean_unbox_usize(v_sz_2619_);
    lean_dec(v_sz_2619_);
    v_i_boxed_2629_ = lean_unbox_usize(v_i_2620_);
    lean_dec(v_i_2620_);
    v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_splitScc_spec__7(v_pu_boxed_2627_, v_declMap_2618_, v_sz_boxed_2628_, v_i_boxed_2629_, v_bs_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
    lean_dec(v___y_2625_);
    lean_dec_ref(v___y_2624_);
    lean_dec(v___y_2623_);
    lean_dec_ref(v___y_2622_);
    lean_dec_ref(v_declMap_2618_);
    return v_res_2630_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9(
    mut v_00_u03b2_2631_: *mut LeanObject,
    mut v_m_2632_: *mut LeanObject,
    mut v_a_2633_: *mut LeanObject,
    mut v_fallback_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    v___x_2635_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9___redArg(v_m_2632_, v_a_2633_, v_fallback_2634_);
    return v___x_2635_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9___boxed(
    mut v_00_u03b2_2636_: *mut LeanObject,
    mut v_m_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_fallback_2639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2640_: *mut LeanObject = core::ptr::null_mut();
    v_res_2640_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9(
            v_00_u03b2_2636_,
            v_m_2637_,
            v_a_2638_,
            v_fallback_2639_,
        );
    lean_dec(v_fallback_2639_);
    lean_dec(v_a_2638_);
    lean_dec_ref(v_m_2637_);
    return v_res_2640_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2(
    mut v_00_u03b2_2641_: *mut LeanObject,
    mut v_m_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
    mut v_b_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2___redArg(v_m_2642_, v_a_2643_, v_b_2644_);
    return v___x_2645_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9_spec__13(
    mut v_00_u03b2_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_fallback_2648_: *mut LeanObject,
    mut v_x_2649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    v___x_2650_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9_spec__13___redArg(v_a_2647_, v_fallback_2648_, v_x_2649_);
    return v___x_2650_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9_spec__13___boxed(
    mut v_00_u03b2_2651_: *mut LeanObject,
    mut v_a_2652_: *mut LeanObject,
    mut v_fallback_2653_: *mut LeanObject,
    mut v_x_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2655_: *mut LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_splitScc_spec__9_spec__13(v_00_u03b2_2651_, v_a_2652_, v_fallback_2653_, v_x_2654_);
    lean_dec(v_x_2654_);
    lean_dec(v_fallback_2653_);
    lean_dec(v_a_2652_);
    return v_res_2655_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2_spec__4(
    mut v_00_u03b2_2656_: *mut LeanObject,
    mut v_a_2657_: *mut LeanObject,
    mut v_b_2658_: *mut LeanObject,
    mut v_x_2659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    v___x_2660_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_splitScc_spec__2_spec__2_spec__4___redArg(v_a_2657_, v_b_2658_, v_x_2659_);
    return v___x_2660_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20(
    mut v_00_u03b2_2661_: *mut LeanObject,
    mut v_m_2662_: *mut LeanObject,
    mut v_a_2663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    v___x_2664_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20___redArg(v_m_2662_, v_a_2663_);
    return v___x_2664_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20___boxed(
    mut v_00_u03b2_2665_: *mut LeanObject,
    mut v_m_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2668_: *mut LeanObject = core::ptr::null_mut();
    v_res_2668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20(v_00_u03b2_2665_, v_m_2666_, v_a_2667_);
    lean_dec(v_a_2667_);
    lean_dec_ref(v_m_2666_);
    return v_res_2668_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20_spec__23(
    mut v_00_u03b2_2669_: *mut LeanObject,
    mut v_a_2670_: *mut LeanObject,
    mut v_x_2671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    v___x_2672_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20_spec__23___redArg(v_a_2670_, v_x_2671_);
    return v___x_2672_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20_spec__23___boxed(
    mut v_00_u03b2_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v_x_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2676_: *mut LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___00Lean_SCC_scc___at___00Lean_Compiler_LCNF_splitScc_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_2673_, v_a_2674_, v_x_2675_);
    lean_dec(v_x_2675_);
    lean_dec(v_a_2674_);
    return v_res_2676_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: u8 = 0;
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    v___x_2743_ = l_Lean_Compiler_LCNF_splitScc___closed__2;
    v___x_2744_ = 1;
    v___x_2745_ = l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_;
    v___x_2746_ = l_Lean_registerTraceClass(v___x_2743_, v___x_2744_, v___x_2745_);
    return v___x_2746_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2____boxed(
    mut v_a_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2748_: *mut LeanObject = core::ptr::null_mut();
    v_res_2748_ = l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_();
    return v_res_2748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_SplitSCC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SCC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_SplitSCC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SplitSCC_1807176231____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_SplitSCC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_SplitSCC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_SCC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SplitSCC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_SplitSCC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_SplitSCC(builtin);
}
