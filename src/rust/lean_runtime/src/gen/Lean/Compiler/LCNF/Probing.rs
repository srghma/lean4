// Lean compiler output
// Module: Lean.Compiler.LCNF.Probing
// Imports: Lean.Compiler.LCNF.PhaseExt
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_instMonadFunctor___aux__1___boxed,
    l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Data::ToString::Extra::l_List_toString___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg,
    l_Nat_add___boxed, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadFunctor___lam__0, l_ReaderT_instMonadLift___lam__0___boxed,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_Decl_size;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadQuotationCoreM, l_Lean_Core_instMonadTraceCoreM,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_lt;
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_addTrace___redArg,
    l_Lean_instMonadTraceOfMonadLift___redArg, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldlM___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__6_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_getJps___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Compiler_LCNF_Probe_getJps___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_getJps___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [35, 0],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 114, 111, 98, 101, 0],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        13095857534955479762 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value) as *mut crate::leanh::LeanObject,3499148146074162748 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [80, 114, 111, 98, 105, 110, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5802720256800895147 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,11572946786707595030 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12063948276346226623 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,5428550382256321361 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14470542412501557332 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [80, 114, 111, 98, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16988565922186321117 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15622052837606737620 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,630934416289210621 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2301426728531480328 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,1528838252800921602 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10961775325370607267 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8019961748949287873 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3723_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0,
    );
    v___x_3725_ = l_StateRefT_x27_instMonad___redArg(v___x_3724_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_map___redArg(
    mut v_f_3730_: *mut crate::leanh::LeanObject,
    mut v_data_3731_: *mut crate::leanh::LeanObject,
    mut v_a_3732_: *mut crate::leanh::LeanObject,
    mut v_a_3733_: *mut crate::leanh::LeanObject,
    mut v_a_3734_: *mut crate::leanh::LeanObject,
    mut v_a_3735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v_toFunctor_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v___f_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3777_: usize = 0;
    let mut v___x_3778_: usize = 0;
    let mut v___x_7__overap_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut v_unused_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_unused_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3737_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_3738_ = crate::leanh::lean_ctor_get(v___x_3737_, 0);
                v_toFunctor_3739_ = crate::leanh::lean_ctor_get(v_toApplicative_3738_, 0);
                v_toSeq_3740_ = crate::leanh::lean_ctor_get(v_toApplicative_3738_, 2);
                v_toSeqLeft_3741_ = crate::leanh::lean_ctor_get(v_toApplicative_3738_, 3);
                v_toSeqRight_3742_ = crate::leanh::lean_ctor_get(v_toApplicative_3738_, 4);
                v___f_3743_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_3744_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3739_, 2);
                v___f_3745_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3745_, 0, v_toFunctor_3739_);
                v___f_3746_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3746_, 0, v_toFunctor_3739_);
                v___x_3747_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3747_, 0, v___f_3745_);
                crate::leanh::lean_ctor_set(v___x_3747_, 1, v___f_3746_);
                crate::leanh::lean_inc(v_toSeqRight_3742_);
                v___f_3748_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3748_, 0, v_toSeqRight_3742_);
                crate::leanh::lean_inc(v_toSeqLeft_3741_);
                v___f_3749_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3749_, 0, v_toSeqLeft_3741_);
                crate::leanh::lean_inc(v_toSeq_3740_);
                v___f_3750_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3750_, 0, v_toSeq_3740_);
                v___x_3751_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3751_, 0, v___x_3747_);
                crate::leanh::lean_ctor_set(v___x_3751_, 1, v___f_3743_);
                crate::leanh::lean_ctor_set(v___x_3751_, 2, v___f_3750_);
                crate::leanh::lean_ctor_set(v___x_3751_, 3, v___f_3749_);
                crate::leanh::lean_ctor_set(v___x_3751_, 4, v___f_3748_);
                v___x_3752_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3752_, 0, v___x_3751_);
                crate::leanh::lean_ctor_set(v___x_3752_, 1, v___f_3744_);
                v___x_3753_ = l_StateRefT_x27_instMonad___redArg(v___x_3752_);
                v_toApplicative_3754_ = crate::leanh::lean_ctor_get(v___x_3753_, 0);
                v_isSharedCheck_3785_ = (!crate::leanh::lean_is_exclusive(v___x_3753_)) as u8;
                if v_isSharedCheck_3785_ == 0 {
                    v_unused_3786_ = crate::leanh::lean_ctor_get(v___x_3753_, 1);
                    crate::leanh::lean_dec(v_unused_3786_);
                    v___x_3756_ = v___x_3753_;
                    v_isShared_3757_ = v_isSharedCheck_3785_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3754_);
                    crate::leanh::lean_dec(v___x_3753_);
                    v___x_3756_ = crate::leanh::lean_box(0);
                    v_isShared_3757_ = v_isSharedCheck_3785_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3758_ = crate::leanh::lean_ctor_get(v_toApplicative_3754_, 0);
                v_toSeq_3759_ = crate::leanh::lean_ctor_get(v_toApplicative_3754_, 2);
                v_toSeqLeft_3760_ = crate::leanh::lean_ctor_get(v_toApplicative_3754_, 3);
                v_toSeqRight_3761_ = crate::leanh::lean_ctor_get(v_toApplicative_3754_, 4);
                v_isSharedCheck_3783_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3754_)) as u8;
                if v_isSharedCheck_3783_ == 0 {
                    v_unused_3784_ = crate::leanh::lean_ctor_get(v_toApplicative_3754_, 1);
                    crate::leanh::lean_dec(v_unused_3784_);
                    v___x_3763_ = v_toApplicative_3754_;
                    v_isShared_3764_ = v_isSharedCheck_3783_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3761_);
                    crate::leanh::lean_inc(v_toSeqLeft_3760_);
                    crate::leanh::lean_inc(v_toSeq_3759_);
                    crate::leanh::lean_inc(v_toFunctor_3758_);
                    crate::leanh::lean_dec(v_toApplicative_3754_);
                    v___x_3763_ = crate::leanh::lean_box(0);
                    v_isShared_3764_ = v_isSharedCheck_3783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3765_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_3766_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_3758_);
                v___f_3767_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3767_, 0, v_toFunctor_3758_);
                v___f_3768_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3768_, 0, v_toFunctor_3758_);
                v___x_3769_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3769_, 0, v___f_3767_);
                crate::leanh::lean_ctor_set(v___x_3769_, 1, v___f_3768_);
                v___f_3770_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3770_, 0, v_toSeqRight_3761_);
                v___f_3771_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3771_, 0, v_toSeqLeft_3760_);
                v___f_3772_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3772_, 0, v_toSeq_3759_);
                if v_isShared_3764_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3763_, 4, v___f_3770_);
                    crate::leanh::lean_ctor_set(v___x_3763_, 3, v___f_3771_);
                    crate::leanh::lean_ctor_set(v___x_3763_, 2, v___f_3772_);
                    crate::leanh::lean_ctor_set(v___x_3763_, 1, v___f_3765_);
                    crate::leanh::lean_ctor_set(v___x_3763_, 0, v___x_3769_);
                    v___x_3774_ = v___x_3763_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 1, v___f_3765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 2, v___f_3772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 3, v___f_3771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 4, v___f_3770_);
                    v___x_3774_ = v_reuseFailAlloc_3782_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3756_, 1, v___f_3766_);
                    crate::leanh::lean_ctor_set(v___x_3756_, 0, v___x_3774_);
                    v___x_3776_ = v___x_3756_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 1, v___f_3766_);
                    v___x_3776_ = v_reuseFailAlloc_3781_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_3777_ = lean_array_size(v_data_3731_);
                v___x_3778_ = 0usize;
                v___x_7__overap_3779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3776_,
                    v_f_3730_,
                    v_sz_3777_,
                    v___x_3778_,
                    v_data_3731_,
                );
                crate::leanh::lean_inc(v_a_3735_);
                crate::leanh::lean_inc_ref(v_a_3734_);
                crate::leanh::lean_inc(v_a_3733_);
                crate::leanh::lean_inc_ref(v_a_3732_);
                v___x_3780_ = crate::leanh::lean_apply_5(
                    v___x_7__overap_3779_,
                    v_a_3732_,
                    v_a_3733_,
                    v_a_3734_,
                    v_a_3735_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_map___redArg___boxed(
    mut v_f_3787_: *mut crate::leanh::LeanObject,
    mut v_data_3788_: *mut crate::leanh::LeanObject,
    mut v_a_3789_: *mut crate::leanh::LeanObject,
    mut v_a_3790_: *mut crate::leanh::LeanObject,
    mut v_a_3791_: *mut crate::leanh::LeanObject,
    mut v_a_3792_: *mut crate::leanh::LeanObject,
    mut v_a_3793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3794_ = l_Lean_Compiler_LCNF_Probe_map___redArg(
        v_f_3787_,
        v_data_3788_,
        v_a_3789_,
        v_a_3790_,
        v_a_3791_,
        v_a_3792_,
    );
    crate::leanh::lean_dec(v_a_3792_);
    crate::leanh::lean_dec_ref(v_a_3791_);
    crate::leanh::lean_dec(v_a_3790_);
    crate::leanh::lean_dec_ref(v_a_3789_);
    return v_res_3794_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_map(
    mut v_00_u03b1_3795_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3796_: *mut crate::leanh::LeanObject,
    mut v_f_3797_: *mut crate::leanh::LeanObject,
    mut v_data_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
    mut v_a_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3824_: u8 = 0;
    let mut v_toFunctor_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___f_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3844_: usize = 0;
    let mut v___x_3845_: usize = 0;
    let mut v___x_57__overap_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_unused_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_unused_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3804_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_3805_ = crate::leanh::lean_ctor_get(v___x_3804_, 0);
                v_toFunctor_3806_ = crate::leanh::lean_ctor_get(v_toApplicative_3805_, 0);
                v_toSeq_3807_ = crate::leanh::lean_ctor_get(v_toApplicative_3805_, 2);
                v_toSeqLeft_3808_ = crate::leanh::lean_ctor_get(v_toApplicative_3805_, 3);
                v_toSeqRight_3809_ = crate::leanh::lean_ctor_get(v_toApplicative_3805_, 4);
                v___f_3810_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_3811_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3806_, 2);
                v___f_3812_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3812_, 0, v_toFunctor_3806_);
                v___f_3813_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3813_, 0, v_toFunctor_3806_);
                v___x_3814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3814_, 0, v___f_3812_);
                crate::leanh::lean_ctor_set(v___x_3814_, 1, v___f_3813_);
                crate::leanh::lean_inc(v_toSeqRight_3809_);
                v___f_3815_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3815_, 0, v_toSeqRight_3809_);
                crate::leanh::lean_inc(v_toSeqLeft_3808_);
                v___f_3816_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3816_, 0, v_toSeqLeft_3808_);
                crate::leanh::lean_inc(v_toSeq_3807_);
                v___f_3817_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3817_, 0, v_toSeq_3807_);
                v___x_3818_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3818_, 0, v___x_3814_);
                crate::leanh::lean_ctor_set(v___x_3818_, 1, v___f_3810_);
                crate::leanh::lean_ctor_set(v___x_3818_, 2, v___f_3817_);
                crate::leanh::lean_ctor_set(v___x_3818_, 3, v___f_3816_);
                crate::leanh::lean_ctor_set(v___x_3818_, 4, v___f_3815_);
                v___x_3819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3819_, 0, v___x_3818_);
                crate::leanh::lean_ctor_set(v___x_3819_, 1, v___f_3811_);
                v___x_3820_ = l_StateRefT_x27_instMonad___redArg(v___x_3819_);
                v_toApplicative_3821_ = crate::leanh::lean_ctor_get(v___x_3820_, 0);
                v_isSharedCheck_3852_ = (!crate::leanh::lean_is_exclusive(v___x_3820_)) as u8;
                if v_isSharedCheck_3852_ == 0 {
                    v_unused_3853_ = crate::leanh::lean_ctor_get(v___x_3820_, 1);
                    crate::leanh::lean_dec(v_unused_3853_);
                    v___x_3823_ = v___x_3820_;
                    v_isShared_3824_ = v_isSharedCheck_3852_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3821_);
                    crate::leanh::lean_dec(v___x_3820_);
                    v___x_3823_ = crate::leanh::lean_box(0);
                    v_isShared_3824_ = v_isSharedCheck_3852_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3825_ = crate::leanh::lean_ctor_get(v_toApplicative_3821_, 0);
                v_toSeq_3826_ = crate::leanh::lean_ctor_get(v_toApplicative_3821_, 2);
                v_toSeqLeft_3827_ = crate::leanh::lean_ctor_get(v_toApplicative_3821_, 3);
                v_toSeqRight_3828_ = crate::leanh::lean_ctor_get(v_toApplicative_3821_, 4);
                v_isSharedCheck_3850_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3821_)) as u8;
                if v_isSharedCheck_3850_ == 0 {
                    v_unused_3851_ = crate::leanh::lean_ctor_get(v_toApplicative_3821_, 1);
                    crate::leanh::lean_dec(v_unused_3851_);
                    v___x_3830_ = v_toApplicative_3821_;
                    v_isShared_3831_ = v_isSharedCheck_3850_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3828_);
                    crate::leanh::lean_inc(v_toSeqLeft_3827_);
                    crate::leanh::lean_inc(v_toSeq_3826_);
                    crate::leanh::lean_inc(v_toFunctor_3825_);
                    crate::leanh::lean_dec(v_toApplicative_3821_);
                    v___x_3830_ = crate::leanh::lean_box(0);
                    v_isShared_3831_ = v_isSharedCheck_3850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3832_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_3833_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_3825_);
                v___f_3834_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3834_, 0, v_toFunctor_3825_);
                v___f_3835_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3835_, 0, v_toFunctor_3825_);
                v___x_3836_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3836_, 0, v___f_3834_);
                crate::leanh::lean_ctor_set(v___x_3836_, 1, v___f_3835_);
                v___f_3837_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3837_, 0, v_toSeqRight_3828_);
                v___f_3838_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3838_, 0, v_toSeqLeft_3827_);
                v___f_3839_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3839_, 0, v_toSeq_3826_);
                if v_isShared_3831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3830_, 4, v___f_3837_);
                    crate::leanh::lean_ctor_set(v___x_3830_, 3, v___f_3838_);
                    crate::leanh::lean_ctor_set(v___x_3830_, 2, v___f_3839_);
                    crate::leanh::lean_ctor_set(v___x_3830_, 1, v___f_3832_);
                    crate::leanh::lean_ctor_set(v___x_3830_, 0, v___x_3836_);
                    v___x_3841_ = v___x_3830_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 1, v___f_3832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 2, v___f_3839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 3, v___f_3838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 4, v___f_3837_);
                    v___x_3841_ = v_reuseFailAlloc_3849_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3823_, 1, v___f_3833_);
                    crate::leanh::lean_ctor_set(v___x_3823_, 0, v___x_3841_);
                    v___x_3843_ = v___x_3823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___f_3833_);
                    v___x_3843_ = v_reuseFailAlloc_3848_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_3844_ = lean_array_size(v_data_3798_);
                v___x_3845_ = 0usize;
                v___x_57__overap_3846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3843_,
                    v_f_3797_,
                    v_sz_3844_,
                    v___x_3845_,
                    v_data_3798_,
                );
                crate::leanh::lean_inc(v_a_3802_);
                crate::leanh::lean_inc_ref(v_a_3801_);
                crate::leanh::lean_inc(v_a_3800_);
                crate::leanh::lean_inc_ref(v_a_3799_);
                v___x_3847_ = crate::leanh::lean_apply_5(
                    v___x_57__overap_3846_,
                    v_a_3799_,
                    v_a_3800_,
                    v_a_3801_,
                    v_a_3802_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_map___boxed(
    mut v_00_u03b1_3854_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3855_: *mut crate::leanh::LeanObject,
    mut v_f_3856_: *mut crate::leanh::LeanObject,
    mut v_data_3857_: *mut crate::leanh::LeanObject,
    mut v_a_3858_: *mut crate::leanh::LeanObject,
    mut v_a_3859_: *mut crate::leanh::LeanObject,
    mut v_a_3860_: *mut crate::leanh::LeanObject,
    mut v_a_3861_: *mut crate::leanh::LeanObject,
    mut v_a_3862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3863_ = l_Lean_Compiler_LCNF_Probe_map(
        v_00_u03b1_3854_,
        v_00_u03b2_3855_,
        v_f_3856_,
        v_data_3857_,
        v_a_3858_,
        v_a_3859_,
        v_a_3860_,
        v_a_3861_,
    );
    crate::leanh::lean_dec(v_a_3861_);
    crate::leanh::lean_dec_ref(v_a_3860_);
    crate::leanh::lean_dec(v_a_3859_);
    crate::leanh::lean_dec_ref(v_a_3858_);
    return v_res_3863_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(
    mut v_f_3864_: *mut crate::leanh::LeanObject,
    mut v_acc_3865_: *mut crate::leanh::LeanObject,
    mut v_a_3866_: *mut crate::leanh::LeanObject,
    mut v___y_3867_: *mut crate::leanh::LeanObject,
    mut v___y_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3876_: u8 = 0;
    let mut v___x_3877_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3885_: u8 = 0;
    let mut v_a_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3889_: u8 = 0;
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3870_);
                crate::leanh::lean_inc_ref(v___y_3869_);
                crate::leanh::lean_inc(v___y_3868_);
                crate::leanh::lean_inc_ref(v___y_3867_);
                crate::leanh::lean_inc(v_a_3866_);
                v___x_3872_ = crate::leanh::lean_apply_6(
                    v_f_3864_,
                    v_a_3866_,
                    v___y_3867_,
                    v___y_3868_,
                    v___y_3869_,
                    v___y_3870_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3872_) == 0 {
                    v_a_3873_ = crate::leanh::lean_ctor_get(v___x_3872_, 0);
                    v_isSharedCheck_3885_ = (!crate::leanh::lean_is_exclusive(v___x_3872_)) as u8;
                    if v_isSharedCheck_3885_ == 0 {
                        v___x_3875_ = v___x_3872_;
                        v_isShared_3876_ = v_isSharedCheck_3885_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3873_);
                        crate::leanh::lean_dec(v___x_3872_);
                        v___x_3875_ = crate::leanh::lean_box(0);
                        v_isShared_3876_ = v_isSharedCheck_3885_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3866_);
                    crate::leanh::lean_dec_ref(v_acc_3865_);
                    v_a_3886_ = crate::leanh::lean_ctor_get(v___x_3872_, 0);
                    v_isSharedCheck_3893_ = (!crate::leanh::lean_is_exclusive(v___x_3872_)) as u8;
                    if v_isSharedCheck_3893_ == 0 {
                        v___x_3888_ = v___x_3872_;
                        v_isShared_3889_ = v_isSharedCheck_3893_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3886_);
                        crate::leanh::lean_dec(v___x_3872_);
                        v___x_3888_ = crate::leanh::lean_box(0);
                        v_isShared_3889_ = v_isSharedCheck_3893_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3877_ = (crate::leanh::lean_unbox(v_a_3873_) as u8);
                crate::leanh::lean_dec(v_a_3873_);
                if v___x_3877_ == 0 {
                    crate::leanh::lean_dec(v_a_3866_);
                    if v_isShared_3876_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3875_, 0, v_acc_3865_);
                        v___x_3879_ = v___x_3875_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3880_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_acc_3865_);
                        v___x_3879_ = v_reuseFailAlloc_3880_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3881_ = lean_array_push(v_acc_3865_, v_a_3866_);
                    if v_isShared_3876_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3875_, 0, v___x_3881_);
                        v___x_3883_ = v___x_3875_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3881_);
                        v___x_3883_ = v_reuseFailAlloc_3884_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3879_;
            }
            3 => {
                return v___x_3883_;
            }
            4 => {
                if v_isShared_3889_ == 0 {
                    v___x_3891_ = v___x_3888_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
                    v___x_3891_ = v_reuseFailAlloc_3892_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed(
    mut v_f_3894_: *mut crate::leanh::LeanObject,
    mut v_acc_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
    mut v___y_3897_: *mut crate::leanh::LeanObject,
    mut v___y_3898_: *mut crate::leanh::LeanObject,
    mut v___y_3899_: *mut crate::leanh::LeanObject,
    mut v___y_3900_: *mut crate::leanh::LeanObject,
    mut v___y_3901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3902_ = l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(
        v_f_3894_,
        v_acc_3895_,
        v_a_3896_,
        v___y_3897_,
        v___y_3898_,
        v___y_3899_,
        v___y_3900_,
    );
    crate::leanh::lean_dec(v___y_3900_);
    crate::leanh::lean_dec_ref(v___y_3899_);
    crate::leanh::lean_dec(v___y_3898_);
    crate::leanh::lean_dec_ref(v___y_3897_);
    return v_res_3902_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filter___redArg(
    mut v_f_3905_: *mut crate::leanh::LeanObject,
    mut v_data_3906_: *mut crate::leanh::LeanObject,
    mut v_a_3907_: *mut crate::leanh::LeanObject,
    mut v_a_3908_: *mut crate::leanh::LeanObject,
    mut v_a_3909_: *mut crate::leanh::LeanObject,
    mut v_a_3910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3932_: u8 = 0;
    let mut v_toFunctor_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___f_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: u8 = 0;
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: usize = 0;
    let mut v___x_3961_: usize = 0;
    let mut v___x_359__overap_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: usize = 0;
    let mut v___x_3965_: usize = 0;
    let mut v___x_364__overap_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut v_unused_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_unused_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3912_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_3913_ = crate::leanh::lean_ctor_get(v___x_3912_, 0);
                v_toFunctor_3914_ = crate::leanh::lean_ctor_get(v_toApplicative_3913_, 0);
                v_toSeq_3915_ = crate::leanh::lean_ctor_get(v_toApplicative_3913_, 2);
                v_toSeqLeft_3916_ = crate::leanh::lean_ctor_get(v_toApplicative_3913_, 3);
                v_toSeqRight_3917_ = crate::leanh::lean_ctor_get(v_toApplicative_3913_, 4);
                v___f_3918_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_3919_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3914_, 2);
                v___f_3920_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3920_, 0, v_toFunctor_3914_);
                v___f_3921_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3921_, 0, v_toFunctor_3914_);
                v___x_3922_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3922_, 0, v___f_3920_);
                crate::leanh::lean_ctor_set(v___x_3922_, 1, v___f_3921_);
                crate::leanh::lean_inc(v_toSeqRight_3917_);
                v___f_3923_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3923_, 0, v_toSeqRight_3917_);
                crate::leanh::lean_inc(v_toSeqLeft_3916_);
                v___f_3924_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3924_, 0, v_toSeqLeft_3916_);
                crate::leanh::lean_inc(v_toSeq_3915_);
                v___f_3925_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3925_, 0, v_toSeq_3915_);
                v___x_3926_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3926_, 0, v___x_3922_);
                crate::leanh::lean_ctor_set(v___x_3926_, 1, v___f_3918_);
                crate::leanh::lean_ctor_set(v___x_3926_, 2, v___f_3925_);
                crate::leanh::lean_ctor_set(v___x_3926_, 3, v___f_3924_);
                crate::leanh::lean_ctor_set(v___x_3926_, 4, v___f_3923_);
                v___x_3927_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3927_, 0, v___x_3926_);
                crate::leanh::lean_ctor_set(v___x_3927_, 1, v___f_3919_);
                v___x_3928_ = l_StateRefT_x27_instMonad___redArg(v___x_3927_);
                v_toApplicative_3929_ = crate::leanh::lean_ctor_get(v___x_3928_, 0);
                v_isSharedCheck_3972_ = (!crate::leanh::lean_is_exclusive(v___x_3928_)) as u8;
                if v_isSharedCheck_3972_ == 0 {
                    v_unused_3973_ = crate::leanh::lean_ctor_get(v___x_3928_, 1);
                    crate::leanh::lean_dec(v_unused_3973_);
                    v___x_3931_ = v___x_3928_;
                    v_isShared_3932_ = v_isSharedCheck_3972_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3929_);
                    crate::leanh::lean_dec(v___x_3928_);
                    v___x_3931_ = crate::leanh::lean_box(0);
                    v_isShared_3932_ = v_isSharedCheck_3972_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3933_ = crate::leanh::lean_ctor_get(v_toApplicative_3929_, 0);
                v_toSeq_3934_ = crate::leanh::lean_ctor_get(v_toApplicative_3929_, 2);
                v_toSeqLeft_3935_ = crate::leanh::lean_ctor_get(v_toApplicative_3929_, 3);
                v_toSeqRight_3936_ = crate::leanh::lean_ctor_get(v_toApplicative_3929_, 4);
                v_isSharedCheck_3970_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3929_)) as u8;
                if v_isSharedCheck_3970_ == 0 {
                    v_unused_3971_ = crate::leanh::lean_ctor_get(v_toApplicative_3929_, 1);
                    crate::leanh::lean_dec(v_unused_3971_);
                    v___x_3938_ = v_toApplicative_3929_;
                    v_isShared_3939_ = v_isSharedCheck_3970_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3936_);
                    crate::leanh::lean_inc(v_toSeqLeft_3935_);
                    crate::leanh::lean_inc(v_toSeq_3934_);
                    crate::leanh::lean_inc(v_toFunctor_3933_);
                    crate::leanh::lean_dec(v_toApplicative_3929_);
                    v___x_3938_ = crate::leanh::lean_box(0);
                    v_isShared_3939_ = v_isSharedCheck_3970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3940_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_3941_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_3933_);
                v___f_3942_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3942_, 0, v_toFunctor_3933_);
                v___f_3943_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3943_, 0, v_toFunctor_3933_);
                v___x_3944_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3944_, 0, v___f_3942_);
                crate::leanh::lean_ctor_set(v___x_3944_, 1, v___f_3943_);
                v___f_3945_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3945_, 0, v_toSeqRight_3936_);
                v___f_3946_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3946_, 0, v_toSeqLeft_3935_);
                v___f_3947_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3947_, 0, v_toSeq_3934_);
                if v_isShared_3939_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3938_, 4, v___f_3945_);
                    crate::leanh::lean_ctor_set(v___x_3938_, 3, v___f_3946_);
                    crate::leanh::lean_ctor_set(v___x_3938_, 2, v___f_3947_);
                    crate::leanh::lean_ctor_set(v___x_3938_, 1, v___f_3940_);
                    crate::leanh::lean_ctor_set(v___x_3938_, 0, v___x_3944_);
                    v___x_3949_ = v___x_3938_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 1, v___f_3940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 2, v___f_3947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 3, v___f_3946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 4, v___f_3945_);
                    v___x_3949_ = v_reuseFailAlloc_3969_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3931_, 1, v___f_3941_);
                    crate::leanh::lean_ctor_set(v___x_3931_, 0, v___x_3949_);
                    v___x_3951_ = v___x_3931_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3968_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 1, v___f_3941_);
                    v___x_3951_ = v_reuseFailAlloc_3968_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3952_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3953_ = lean_array_get_size(v_data_3906_);
                v___x_3954_ = l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0;
                v___x_3955_ = lean_nat_dec_lt(v___x_3952_, v___x_3953_);
                if v___x_3955_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3951_);
                    crate::leanh::lean_dec_ref(v_data_3906_);
                    crate::leanh::lean_dec_ref(v_f_3905_);
                    v___x_3956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3956_, 0, v___x_3954_);
                    return v___x_3956_;
                } else {
                    v___f_3957_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        8,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3957_, 0, v_f_3905_);
                    v___x_3958_ = lean_nat_dec_le(v___x_3953_, v___x_3953_);
                    if v___x_3958_ == 0 {
                        if v___x_3955_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_3957_);
                            crate::leanh::lean_dec_ref(v___x_3951_);
                            crate::leanh::lean_dec_ref(v_data_3906_);
                            v___x_3959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3959_, 0, v___x_3954_);
                            return v___x_3959_;
                        } else {
                            v___x_3960_ = 0usize;
                            v___x_3961_ = lean_usize_of_nat(v___x_3953_);
                            v___x_359__overap_3962_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_3951_,
                                    v___f_3957_,
                                    v_data_3906_,
                                    v___x_3960_,
                                    v___x_3961_,
                                    v___x_3954_,
                                );
                            crate::leanh::lean_inc(v_a_3910_);
                            crate::leanh::lean_inc_ref(v_a_3909_);
                            crate::leanh::lean_inc(v_a_3908_);
                            crate::leanh::lean_inc_ref(v_a_3907_);
                            v___x_3963_ = crate::leanh::lean_apply_5(
                                v___x_359__overap_3962_,
                                v_a_3907_,
                                v_a_3908_,
                                v_a_3909_,
                                v_a_3910_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_3963_;
                        }
                    } else {
                        v___x_3964_ = 0usize;
                        v___x_3965_ = lean_usize_of_nat(v___x_3953_);
                        v___x_364__overap_3966_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3951_,
                                v___f_3957_,
                                v_data_3906_,
                                v___x_3964_,
                                v___x_3965_,
                                v___x_3954_,
                            );
                        crate::leanh::lean_inc(v_a_3910_);
                        crate::leanh::lean_inc_ref(v_a_3909_);
                        crate::leanh::lean_inc(v_a_3908_);
                        crate::leanh::lean_inc_ref(v_a_3907_);
                        v___x_3967_ = crate::leanh::lean_apply_5(
                            v___x_364__overap_3966_,
                            v_a_3907_,
                            v_a_3908_,
                            v_a_3909_,
                            v_a_3910_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3967_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filter___redArg___boxed(
    mut v_f_3974_: *mut crate::leanh::LeanObject,
    mut v_data_3975_: *mut crate::leanh::LeanObject,
    mut v_a_3976_: *mut crate::leanh::LeanObject,
    mut v_a_3977_: *mut crate::leanh::LeanObject,
    mut v_a_3978_: *mut crate::leanh::LeanObject,
    mut v_a_3979_: *mut crate::leanh::LeanObject,
    mut v_a_3980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3981_ = l_Lean_Compiler_LCNF_Probe_filter___redArg(
        v_f_3974_,
        v_data_3975_,
        v_a_3976_,
        v_a_3977_,
        v_a_3978_,
        v_a_3979_,
    );
    crate::leanh::lean_dec(v_a_3979_);
    crate::leanh::lean_dec_ref(v_a_3978_);
    crate::leanh::lean_dec(v_a_3977_);
    crate::leanh::lean_dec_ref(v_a_3976_);
    return v_res_3981_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filter(
    mut v_00_u03b1_3982_: *mut crate::leanh::LeanObject,
    mut v_f_3983_: *mut crate::leanh::LeanObject,
    mut v_data_3984_: *mut crate::leanh::LeanObject,
    mut v_a_3985_: *mut crate::leanh::LeanObject,
    mut v_a_3986_: *mut crate::leanh::LeanObject,
    mut v_a_3987_: *mut crate::leanh::LeanObject,
    mut v_a_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4010_: u8 = 0;
    let mut v_toFunctor_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4017_: u8 = 0;
    let mut v___f_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: u8 = 0;
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: usize = 0;
    let mut v___x_4039_: usize = 0;
    let mut v___x_448__overap_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: usize = 0;
    let mut v___x_4043_: usize = 0;
    let mut v___x_451__overap_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4048_: u8 = 0;
    let mut v_unused_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4050_: u8 = 0;
    let mut v_unused_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3990_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_3991_ = crate::leanh::lean_ctor_get(v___x_3990_, 0);
                v_toFunctor_3992_ = crate::leanh::lean_ctor_get(v_toApplicative_3991_, 0);
                v_toSeq_3993_ = crate::leanh::lean_ctor_get(v_toApplicative_3991_, 2);
                v_toSeqLeft_3994_ = crate::leanh::lean_ctor_get(v_toApplicative_3991_, 3);
                v_toSeqRight_3995_ = crate::leanh::lean_ctor_get(v_toApplicative_3991_, 4);
                v___f_3996_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_3997_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3992_, 2);
                v___f_3998_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3998_, 0, v_toFunctor_3992_);
                v___f_3999_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3999_, 0, v_toFunctor_3992_);
                v___x_4000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4000_, 0, v___f_3998_);
                crate::leanh::lean_ctor_set(v___x_4000_, 1, v___f_3999_);
                crate::leanh::lean_inc(v_toSeqRight_3995_);
                v___f_4001_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4001_, 0, v_toSeqRight_3995_);
                crate::leanh::lean_inc(v_toSeqLeft_3994_);
                v___f_4002_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4002_, 0, v_toSeqLeft_3994_);
                crate::leanh::lean_inc(v_toSeq_3993_);
                v___f_4003_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4003_, 0, v_toSeq_3993_);
                v___x_4004_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4004_, 0, v___x_4000_);
                crate::leanh::lean_ctor_set(v___x_4004_, 1, v___f_3996_);
                crate::leanh::lean_ctor_set(v___x_4004_, 2, v___f_4003_);
                crate::leanh::lean_ctor_set(v___x_4004_, 3, v___f_4002_);
                crate::leanh::lean_ctor_set(v___x_4004_, 4, v___f_4001_);
                v___x_4005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4005_, 0, v___x_4004_);
                crate::leanh::lean_ctor_set(v___x_4005_, 1, v___f_3997_);
                v___x_4006_ = l_StateRefT_x27_instMonad___redArg(v___x_4005_);
                v_toApplicative_4007_ = crate::leanh::lean_ctor_get(v___x_4006_, 0);
                v_isSharedCheck_4050_ = (!crate::leanh::lean_is_exclusive(v___x_4006_)) as u8;
                if v_isSharedCheck_4050_ == 0 {
                    v_unused_4051_ = crate::leanh::lean_ctor_get(v___x_4006_, 1);
                    crate::leanh::lean_dec(v_unused_4051_);
                    v___x_4009_ = v___x_4006_;
                    v_isShared_4010_ = v_isSharedCheck_4050_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4007_);
                    crate::leanh::lean_dec(v___x_4006_);
                    v___x_4009_ = crate::leanh::lean_box(0);
                    v_isShared_4010_ = v_isSharedCheck_4050_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4011_ = crate::leanh::lean_ctor_get(v_toApplicative_4007_, 0);
                v_toSeq_4012_ = crate::leanh::lean_ctor_get(v_toApplicative_4007_, 2);
                v_toSeqLeft_4013_ = crate::leanh::lean_ctor_get(v_toApplicative_4007_, 3);
                v_toSeqRight_4014_ = crate::leanh::lean_ctor_get(v_toApplicative_4007_, 4);
                v_isSharedCheck_4048_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4007_)) as u8;
                if v_isSharedCheck_4048_ == 0 {
                    v_unused_4049_ = crate::leanh::lean_ctor_get(v_toApplicative_4007_, 1);
                    crate::leanh::lean_dec(v_unused_4049_);
                    v___x_4016_ = v_toApplicative_4007_;
                    v_isShared_4017_ = v_isSharedCheck_4048_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4014_);
                    crate::leanh::lean_inc(v_toSeqLeft_4013_);
                    crate::leanh::lean_inc(v_toSeq_4012_);
                    crate::leanh::lean_inc(v_toFunctor_4011_);
                    crate::leanh::lean_dec(v_toApplicative_4007_);
                    v___x_4016_ = crate::leanh::lean_box(0);
                    v_isShared_4017_ = v_isSharedCheck_4048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4018_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_4019_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_4011_);
                v___f_4020_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4020_, 0, v_toFunctor_4011_);
                v___f_4021_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4021_, 0, v_toFunctor_4011_);
                v___x_4022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4022_, 0, v___f_4020_);
                crate::leanh::lean_ctor_set(v___x_4022_, 1, v___f_4021_);
                v___f_4023_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4023_, 0, v_toSeqRight_4014_);
                v___f_4024_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4024_, 0, v_toSeqLeft_4013_);
                v___f_4025_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4025_, 0, v_toSeq_4012_);
                if v_isShared_4017_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4016_, 4, v___f_4023_);
                    crate::leanh::lean_ctor_set(v___x_4016_, 3, v___f_4024_);
                    crate::leanh::lean_ctor_set(v___x_4016_, 2, v___f_4025_);
                    crate::leanh::lean_ctor_set(v___x_4016_, 1, v___f_4018_);
                    crate::leanh::lean_ctor_set(v___x_4016_, 0, v___x_4022_);
                    v___x_4027_ = v___x_4016_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4047_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___f_4018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4047_, 2, v___f_4025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4047_, 3, v___f_4024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4047_, 4, v___f_4023_);
                    v___x_4027_ = v_reuseFailAlloc_4047_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4010_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4009_, 1, v___f_4019_);
                    crate::leanh::lean_ctor_set(v___x_4009_, 0, v___x_4027_);
                    v___x_4029_ = v___x_4009_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4046_, 1, v___f_4019_);
                    v___x_4029_ = v_reuseFailAlloc_4046_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4030_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4031_ = lean_array_get_size(v_data_3984_);
                v___x_4032_ = l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0;
                v___x_4033_ = lean_nat_dec_lt(v___x_4030_, v___x_4031_);
                if v___x_4033_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4029_);
                    crate::leanh::lean_dec_ref(v_data_3984_);
                    crate::leanh::lean_dec_ref(v_f_3983_);
                    v___x_4034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4034_, 0, v___x_4032_);
                    return v___x_4034_;
                } else {
                    v___f_4035_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        8,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4035_, 0, v_f_3983_);
                    v___x_4036_ = lean_nat_dec_le(v___x_4031_, v___x_4031_);
                    if v___x_4036_ == 0 {
                        if v___x_4033_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_4035_);
                            crate::leanh::lean_dec_ref(v___x_4029_);
                            crate::leanh::lean_dec_ref(v_data_3984_);
                            v___x_4037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4037_, 0, v___x_4032_);
                            return v___x_4037_;
                        } else {
                            v___x_4038_ = 0usize;
                            v___x_4039_ = lean_usize_of_nat(v___x_4031_);
                            v___x_448__overap_4040_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_4029_,
                                    v___f_4035_,
                                    v_data_3984_,
                                    v___x_4038_,
                                    v___x_4039_,
                                    v___x_4032_,
                                );
                            crate::leanh::lean_inc(v_a_3988_);
                            crate::leanh::lean_inc_ref(v_a_3987_);
                            crate::leanh::lean_inc(v_a_3986_);
                            crate::leanh::lean_inc_ref(v_a_3985_);
                            v___x_4041_ = crate::leanh::lean_apply_5(
                                v___x_448__overap_4040_,
                                v_a_3985_,
                                v_a_3986_,
                                v_a_3987_,
                                v_a_3988_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_4041_;
                        }
                    } else {
                        v___x_4042_ = 0usize;
                        v___x_4043_ = lean_usize_of_nat(v___x_4031_);
                        v___x_451__overap_4044_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_4029_,
                                v___f_4035_,
                                v_data_3984_,
                                v___x_4042_,
                                v___x_4043_,
                                v___x_4032_,
                            );
                        crate::leanh::lean_inc(v_a_3988_);
                        crate::leanh::lean_inc_ref(v_a_3987_);
                        crate::leanh::lean_inc(v_a_3986_);
                        crate::leanh::lean_inc_ref(v_a_3985_);
                        v___x_4045_ = crate::leanh::lean_apply_5(
                            v___x_451__overap_4044_,
                            v_a_3985_,
                            v_a_3986_,
                            v_a_3987_,
                            v_a_3988_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_4045_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filter___boxed(
    mut v_00_u03b1_4052_: *mut crate::leanh::LeanObject,
    mut v_f_4053_: *mut crate::leanh::LeanObject,
    mut v_data_4054_: *mut crate::leanh::LeanObject,
    mut v_a_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
    mut v_a_4058_: *mut crate::leanh::LeanObject,
    mut v_a_4059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4060_ = l_Lean_Compiler_LCNF_Probe_filter(
        v_00_u03b1_4052_,
        v_f_4053_,
        v_data_4054_,
        v_a_4055_,
        v_a_4056_,
        v_a_4057_,
        v_a_4058_,
    );
    crate::leanh::lean_dec(v_a_4058_);
    crate::leanh::lean_dec_ref(v_a_4057_);
    crate::leanh::lean_dec(v_a_4056_);
    crate::leanh::lean_dec_ref(v_a_4055_);
    return v_res_4060_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(
    mut v_inst_4061_: *mut crate::leanh::LeanObject,
    mut v_x1_4062_: *mut crate::leanh::LeanObject,
    mut v_x2_4063_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    v___x_4064_ = crate::leanh::lean_apply_2(v_inst_4061_, v_x1_4062_, v_x2_4063_);
    v___x_4065_ = (crate::leanh::lean_unbox(v___x_4064_) as u8);
    return v___x_4065_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed(
    mut v_inst_4066_: *mut crate::leanh::LeanObject,
    mut v_x1_4067_: *mut crate::leanh::LeanObject,
    mut v_x2_4068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4069_: u8 = 0;
    let mut v_r_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4069_ =
        l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(v_inst_4066_, v_x1_4067_, v_x2_4068_);
    v_r_4070_ = crate::leanh::lean_box((v_res_4069_) as usize);
    return v_r_4070_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sorted___redArg(
    mut v_inst_4071_: *mut crate::leanh::LeanObject,
    mut v_data_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u8 = 0;
    let mut v___f_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4074_ = lean_array_get_size(v_data_4072_);
                v___x_4075_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4076_ = lean_nat_dec_eq(v___x_4074_, v___x_4075_);
                if v___x_4076_ == 0 {
                    v___f_4077_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4077_, 0, v_inst_4071_);
                    v___x_4083_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4084_ = lean_nat_sub(v___x_4074_, v___x_4083_);
                    v___x_4088_ = lean_nat_dec_le(v___x_4075_, v___x_4084_);
                    if v___x_4088_ == 0 {
                        crate::leanh::lean_inc(v___x_4084_);
                        v___y_4086_ = v___x_4084_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4086_ = v___x_4075_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_4071_);
                    v___x_4089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4089_, 0, v_data_4072_);
                    return v___x_4089_;
                }
            }
            1 => {
                v___x_4081_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___f_4077_,
                    v___x_4074_,
                    v_data_4072_,
                    v___y_4079_,
                    v___y_4080_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_4080_);
                v___x_4082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4082_, 0, v___x_4081_);
                return v___x_4082_;
            }
            2 => {
                v___x_4087_ = lean_nat_dec_le(v___y_4086_, v___x_4084_);
                if v___x_4087_ == 0 {
                    crate::leanh::lean_dec(v___x_4084_);
                    crate::leanh::lean_inc(v___y_4086_);
                    v___y_4079_ = v___y_4086_;
                    v___y_4080_ = v___y_4086_;
                    state = 1;
                    continue;
                } else {
                    v___y_4079_ = v___y_4086_;
                    v___y_4080_ = v___x_4084_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sorted___redArg___boxed(
    mut v_inst_4090_: *mut crate::leanh::LeanObject,
    mut v_data_4091_: *mut crate::leanh::LeanObject,
    mut v_a_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4093_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg(v_inst_4090_, v_data_4091_);
    return v_res_4093_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sorted(
    mut v_00_u03b1_4094_: *mut crate::leanh::LeanObject,
    mut v_inst_4095_: *mut crate::leanh::LeanObject,
    mut v_inst_4096_: *mut crate::leanh::LeanObject,
    mut v_inst_4097_: *mut crate::leanh::LeanObject,
    mut v_data_4098_: *mut crate::leanh::LeanObject,
    mut v_a_4099_: *mut crate::leanh::LeanObject,
    mut v_a_4100_: *mut crate::leanh::LeanObject,
    mut v_a_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: u8 = 0;
    let mut v___f_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: u8 = 0;
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4104_ = lean_array_get_size(v_data_4098_);
                v___x_4105_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4106_ = lean_nat_dec_eq(v___x_4104_, v___x_4105_);
                if v___x_4106_ == 0 {
                    v___f_4107_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4107_, 0, v_inst_4097_);
                    v___x_4113_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4114_ = lean_nat_sub(v___x_4104_, v___x_4113_);
                    v___x_4118_ = lean_nat_dec_le(v___x_4105_, v___x_4114_);
                    if v___x_4118_ == 0 {
                        crate::leanh::lean_inc(v___x_4114_);
                        v___y_4116_ = v___x_4114_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4116_ = v___x_4105_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_4097_);
                    v___x_4119_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4119_, 0, v_data_4098_);
                    return v___x_4119_;
                }
            }
            1 => {
                v___x_4111_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___f_4107_,
                    v___x_4104_,
                    v_data_4098_,
                    v___y_4109_,
                    v___y_4110_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_4110_);
                v___x_4112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4112_, 0, v___x_4111_);
                return v___x_4112_;
            }
            2 => {
                v___x_4117_ = lean_nat_dec_le(v___y_4116_, v___x_4114_);
                if v___x_4117_ == 0 {
                    crate::leanh::lean_dec(v___x_4114_);
                    crate::leanh::lean_inc(v___y_4116_);
                    v___y_4109_ = v___y_4116_;
                    v___y_4110_ = v___y_4116_;
                    state = 1;
                    continue;
                } else {
                    v___y_4109_ = v___y_4116_;
                    v___y_4110_ = v___x_4114_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sorted___boxed(
    mut v_00_u03b1_4120_: *mut crate::leanh::LeanObject,
    mut v_inst_4121_: *mut crate::leanh::LeanObject,
    mut v_inst_4122_: *mut crate::leanh::LeanObject,
    mut v_inst_4123_: *mut crate::leanh::LeanObject,
    mut v_data_4124_: *mut crate::leanh::LeanObject,
    mut v_a_4125_: *mut crate::leanh::LeanObject,
    mut v_a_4126_: *mut crate::leanh::LeanObject,
    mut v_a_4127_: *mut crate::leanh::LeanObject,
    mut v_a_4128_: *mut crate::leanh::LeanObject,
    mut v_a_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l_Lean_Compiler_LCNF_Probe_sorted(
        v_00_u03b1_4120_,
        v_inst_4121_,
        v_inst_4122_,
        v_inst_4123_,
        v_data_4124_,
        v_a_4125_,
        v_a_4126_,
        v_a_4127_,
        v_a_4128_,
    );
    crate::leanh::lean_dec(v_a_4128_);
    crate::leanh::lean_dec_ref(v_a_4127_);
    crate::leanh::lean_dec(v_a_4126_);
    crate::leanh::lean_dec_ref(v_a_4125_);
    crate::leanh::lean_dec(v_inst_4121_);
    return v_res_4130_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(
    mut v_pu_4131_: u8,
    mut v_x_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4133_ = l_Lean_Compiler_LCNF_Decl_size(v_pu_4131_, v_x_4132_);
    v___x_4134_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4134_, 0, v___x_4133_);
    crate::leanh::lean_ctor_set(v___x_4134_, 1, v_x_4132_);
    return v___x_4134_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed(
    mut v_pu_4135_: *mut crate::leanh::LeanObject,
    mut v_x_4136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4137_: u8 = 0;
    let mut v_res_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4137_ = (crate::leanh::lean_unbox(v_pu_4135_) as u8);
    v_res_4138_ =
        l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(v_pu_boxed_4137_, v_x_4136_);
    return v_res_4138_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(
    mut v_x_4139_: *mut crate::leanh::LeanObject,
    mut v_x_4140_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: u8 = 0;
    v_fst_4141_ = crate::leanh::lean_ctor_get(v_x_4139_, 0);
    v_snd_4142_ = crate::leanh::lean_ctor_get(v_x_4139_, 1);
    v_fst_4143_ = crate::leanh::lean_ctor_get(v_x_4140_, 0);
    v_snd_4144_ = crate::leanh::lean_ctor_get(v_x_4140_, 1);
    v___x_4145_ = lean_nat_dec_eq(v_fst_4141_, v_fst_4143_);
    if v___x_4145_ == 0 {
        let mut v___x_4146_: u8 = 0;
        v___x_4146_ = lean_nat_dec_lt(v_fst_4141_, v_fst_4143_);
        return v___x_4146_;
    } else {
        let mut v_toSignature_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toSignature_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4151_: u8 = 0;
        v_toSignature_4147_ = crate::leanh::lean_ctor_get(v_snd_4142_, 0);
        v_toSignature_4148_ = crate::leanh::lean_ctor_get(v_snd_4144_, 0);
        v_name_4149_ = crate::leanh::lean_ctor_get(v_toSignature_4147_, 0);
        v_name_4150_ = crate::leanh::lean_ctor_get(v_toSignature_4148_, 0);
        v___x_4151_ = l_Lean_Name_lt(v_name_4149_, v_name_4150_);
        return v___x_4151_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1___boxed(
    mut v_x_4152_: *mut crate::leanh::LeanObject,
    mut v_x_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4154_: u8 = 0;
    let mut v_r_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4154_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(v_x_4152_, v_x_4153_);
    crate::leanh::lean_dec_ref(v_x_4153_);
    crate::leanh::lean_dec_ref(v_x_4152_);
    v_r_4155_ = crate::leanh::lean_box((v_res_4154_) as usize);
    return v_r_4155_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(
    mut v_pu_4176_: u8,
    mut v_decls_4177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4182_: usize = 0;
    let mut v___x_4183_: usize = 0;
    let mut v_decls_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: u8 = 0;
    let mut v___f_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: u8 = 0;
    let mut v___x_4199_: u8 = 0;
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4179_ = crate::leanh::lean_box((v_pu_4176_) as usize);
                v___f_4180_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4180_, 0, v___x_4179_);
                v___x_4181_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9;
                v_sz_4182_ = lean_array_size(v_decls_4177_);
                v___x_4183_ = 0usize;
                v_decls_4184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4181_,
                    v___f_4180_,
                    v_sz_4182_,
                    v___x_4183_,
                    v_decls_4177_,
                );
                v___x_4185_ = lean_array_get_size(v_decls_4184_);
                v___x_4186_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4187_ = lean_nat_dec_eq(v___x_4185_, v___x_4186_);
                if v___x_4187_ == 0 {
                    v___f_4188_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10;
                    v___x_4194_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4195_ = lean_nat_sub(v___x_4185_, v___x_4194_);
                    v___x_4199_ = lean_nat_dec_le(v___x_4186_, v___x_4195_);
                    if v___x_4199_ == 0 {
                        crate::leanh::lean_inc(v___x_4195_);
                        v___y_4197_ = v___x_4195_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4197_ = v___x_4186_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4200_, 0, v_decls_4184_);
                    return v___x_4200_;
                }
            }
            1 => {
                v___x_4192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___f_4188_,
                    v___x_4185_,
                    v_decls_4184_,
                    v___y_4190_,
                    v___y_4191_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_4191_);
                v___x_4193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4192_);
                return v___x_4193_;
            }
            2 => {
                v___x_4198_ = lean_nat_dec_le(v___y_4197_, v___x_4195_);
                if v___x_4198_ == 0 {
                    crate::leanh::lean_dec(v___x_4195_);
                    crate::leanh::lean_inc(v___y_4197_);
                    v___y_4190_ = v___y_4197_;
                    v___y_4191_ = v___y_4197_;
                    state = 1;
                    continue;
                } else {
                    v___y_4190_ = v___y_4197_;
                    v___y_4191_ = v___x_4195_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___boxed(
    mut v_pu_4201_: *mut crate::leanh::LeanObject,
    mut v_decls_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4204_: u8 = 0;
    let mut v_res_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4204_ = (crate::leanh::lean_unbox(v_pu_4201_) as u8);
    v_res_4205_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(v_pu_boxed_4204_, v_decls_4202_);
    return v_res_4205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sortedBySize(
    mut v_pu_4206_: u8,
    mut v_decls_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4216_: usize = 0;
    let mut v___x_4217_: usize = 0;
    let mut v_decls_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: u8 = 0;
    let mut v___f_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: u8 = 0;
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4213_ = crate::leanh::lean_box((v_pu_4206_) as usize);
                v___f_4214_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4214_, 0, v___x_4213_);
                v___x_4215_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9;
                v_sz_4216_ = lean_array_size(v_decls_4207_);
                v___x_4217_ = 0usize;
                v_decls_4218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4215_,
                    v___f_4214_,
                    v_sz_4216_,
                    v___x_4217_,
                    v_decls_4207_,
                );
                v___x_4219_ = lean_array_get_size(v_decls_4218_);
                v___x_4220_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4221_ = lean_nat_dec_eq(v___x_4219_, v___x_4220_);
                if v___x_4221_ == 0 {
                    v___f_4222_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10;
                    v___x_4228_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4229_ = lean_nat_sub(v___x_4219_, v___x_4228_);
                    v___x_4233_ = lean_nat_dec_le(v___x_4220_, v___x_4229_);
                    if v___x_4233_ == 0 {
                        crate::leanh::lean_inc(v___x_4229_);
                        v___y_4231_ = v___x_4229_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4231_ = v___x_4220_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4234_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4234_, 0, v_decls_4218_);
                    return v___x_4234_;
                }
            }
            1 => {
                v___x_4226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___f_4222_,
                    v___x_4219_,
                    v_decls_4218_,
                    v___y_4224_,
                    v___y_4225_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_4225_);
                v___x_4227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4226_);
                return v___x_4227_;
            }
            2 => {
                v___x_4232_ = lean_nat_dec_le(v___y_4231_, v___x_4229_);
                if v___x_4232_ == 0 {
                    crate::leanh::lean_dec(v___x_4229_);
                    crate::leanh::lean_inc(v___y_4231_);
                    v___y_4224_ = v___y_4231_;
                    v___y_4225_ = v___y_4231_;
                    state = 1;
                    continue;
                } else {
                    v___y_4224_ = v___y_4231_;
                    v___y_4225_ = v___x_4229_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sortedBySize___boxed(
    mut v_pu_4235_: *mut crate::leanh::LeanObject,
    mut v_decls_4236_: *mut crate::leanh::LeanObject,
    mut v_a_4237_: *mut crate::leanh::LeanObject,
    mut v_a_4238_: *mut crate::leanh::LeanObject,
    mut v_a_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
    mut v_a_4241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4242_: u8 = 0;
    let mut v_res_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4242_ = (crate::leanh::lean_unbox(v_pu_4235_) as u8);
    v_res_4243_ = l_Lean_Compiler_LCNF_Probe_sortedBySize(
        v_pu_boxed_4242_,
        v_decls_4236_,
        v_a_4237_,
        v_a_4238_,
        v_a_4239_,
        v_a_4240_,
    );
    crate::leanh::lean_dec(v_a_4240_);
    crate::leanh::lean_dec_ref(v_a_4239_);
    crate::leanh::lean_dec(v_a_4238_);
    crate::leanh::lean_dec_ref(v_a_4237_);
    return v_res_4243_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(
    mut v_inst_4244_: *mut crate::leanh::LeanObject,
    mut v_inst_4245_: *mut crate::leanh::LeanObject,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_x_4247_: *mut crate::leanh::LeanObject,
    mut v___y_4248_: *mut crate::leanh::LeanObject,
    mut v___y_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_4246_);
                crate::leanh::lean_inc_ref(v_inst_4245_);
                crate::leanh::lean_inc_ref(v_inst_4244_);
                v___x_4254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_4244_,
                    v_inst_4245_,
                    v___y_4248_,
                    v_a_4246_,
                );
                if crate::leanh::lean_obj_tag(v___x_4254_) == 1 {
                    v_val_4255_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                    v_isSharedCheck_4266_ = (!crate::leanh::lean_is_exclusive(v___x_4254_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4257_ = v___x_4254_;
                        v_isShared_4258_ = v_isSharedCheck_4266_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4255_);
                        crate::leanh::lean_dec(v___x_4254_);
                        v___x_4257_ = crate::leanh::lean_box(0);
                        v_isShared_4258_ = v_isSharedCheck_4266_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4254_);
                    v___x_4267_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4268_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_inst_4244_,
                        v_inst_4245_,
                        v___y_4248_,
                        v_a_4246_,
                        v___x_4267_,
                    );
                    v___x_4269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4269_, 0, v___x_4268_);
                    v___x_4270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4270_, 0, v___x_4269_);
                    return v___x_4270_;
                }
            }
            1 => {
                v___x_4259_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4260_ = lean_nat_add(v_val_4255_, v___x_4259_);
                crate::leanh::lean_dec(v_val_4255_);
                v___x_4261_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v_inst_4244_,
                    v_inst_4245_,
                    v___y_4248_,
                    v_a_4246_,
                    v___x_4260_,
                );
                if v_isShared_4258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4257_, 0, v___x_4261_);
                    v___x_4263_ = v___x_4257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4261_);
                    v___x_4263_ = v_reuseFailAlloc_4265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4264_, 0, v___x_4263_);
                return v___x_4264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed(
    mut v_inst_4271_: *mut crate::leanh::LeanObject,
    mut v_inst_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
    mut v_x_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
    mut v___y_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4281_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(
        v_inst_4271_,
        v_inst_4272_,
        v_a_4273_,
        v_x_4274_,
        v___y_4275_,
        v___y_4276_,
        v___y_4277_,
        v___y_4278_,
        v___y_4279_,
    );
    crate::leanh::lean_dec(v___y_4279_);
    crate::leanh::lean_dec_ref(v___y_4278_);
    crate::leanh::lean_dec(v___y_4277_);
    crate::leanh::lean_dec_ref(v___y_4276_);
    return v_res_4281_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1(
    mut v_x1_4282_: *mut crate::leanh::LeanObject,
    mut v_x2_4283_: *mut crate::leanh::LeanObject,
    mut v_x3_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4285_, 0, v_x2_4283_);
    crate::leanh::lean_ctor_set(v___x_4285_, 1, v_x3_4284_);
    v___x_4286_ = lean_array_push(v_x1_4282_, v___x_4285_);
    return v___x_4286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__2(
    mut v___x_4287_: *mut crate::leanh::LeanObject,
    mut v___f_4288_: *mut crate::leanh::LeanObject,
    mut v_acc_4289_: *mut crate::leanh::LeanObject,
    mut v_l_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4287_,
        v___f_4288_,
        v_acc_4289_,
        v_l_4290_,
    );
    return v___x_4291_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUnique___redArg(
    mut v_inst_4296_: *mut crate::leanh::LeanObject,
    mut v_inst_4297_: *mut crate::leanh::LeanObject,
    mut v_data_4298_: *mut crate::leanh::LeanObject,
    mut v_a_4299_: *mut crate::leanh::LeanObject,
    mut v_a_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v_toFunctor_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4331_: u8 = 0;
    let mut v___f_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4355_: usize = 0;
    let mut v___x_4356_: usize = 0;
    let mut v___x_747__overap_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v_size_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: usize = 0;
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4387_: u8 = 0;
    let mut v_a_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4395_: u8 = 0;
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_unused_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4400_: u8 = 0;
    let mut v_unused_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4304_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_4305_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                v_toFunctor_4306_ = crate::leanh::lean_ctor_get(v_toApplicative_4305_, 0);
                v_toSeq_4307_ = crate::leanh::lean_ctor_get(v_toApplicative_4305_, 2);
                v_toSeqLeft_4308_ = crate::leanh::lean_ctor_get(v_toApplicative_4305_, 3);
                v_toSeqRight_4309_ = crate::leanh::lean_ctor_get(v_toApplicative_4305_, 4);
                v___f_4310_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_4311_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_4306_, 2);
                v___f_4312_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4312_, 0, v_toFunctor_4306_);
                v___f_4313_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4313_, 0, v_toFunctor_4306_);
                v___x_4314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4314_, 0, v___f_4312_);
                crate::leanh::lean_ctor_set(v___x_4314_, 1, v___f_4313_);
                crate::leanh::lean_inc(v_toSeqRight_4309_);
                v___f_4315_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4315_, 0, v_toSeqRight_4309_);
                crate::leanh::lean_inc(v_toSeqLeft_4308_);
                v___f_4316_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4316_, 0, v_toSeqLeft_4308_);
                crate::leanh::lean_inc(v_toSeq_4307_);
                v___f_4317_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4317_, 0, v_toSeq_4307_);
                v___x_4318_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4318_, 0, v___x_4314_);
                crate::leanh::lean_ctor_set(v___x_4318_, 1, v___f_4310_);
                crate::leanh::lean_ctor_set(v___x_4318_, 2, v___f_4317_);
                crate::leanh::lean_ctor_set(v___x_4318_, 3, v___f_4316_);
                crate::leanh::lean_ctor_set(v___x_4318_, 4, v___f_4315_);
                v___x_4319_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4319_, 0, v___x_4318_);
                crate::leanh::lean_ctor_set(v___x_4319_, 1, v___f_4311_);
                v___x_4320_ = l_StateRefT_x27_instMonad___redArg(v___x_4319_);
                v_toApplicative_4321_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                v_isSharedCheck_4400_ = (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                if v_isSharedCheck_4400_ == 0 {
                    v_unused_4401_ = crate::leanh::lean_ctor_get(v___x_4320_, 1);
                    crate::leanh::lean_dec(v_unused_4401_);
                    v___x_4323_ = v___x_4320_;
                    v_isShared_4324_ = v_isSharedCheck_4400_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4321_);
                    crate::leanh::lean_dec(v___x_4320_);
                    v___x_4323_ = crate::leanh::lean_box(0);
                    v_isShared_4324_ = v_isSharedCheck_4400_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4325_ = crate::leanh::lean_ctor_get(v_toApplicative_4321_, 0);
                v_toSeq_4326_ = crate::leanh::lean_ctor_get(v_toApplicative_4321_, 2);
                v_toSeqLeft_4327_ = crate::leanh::lean_ctor_get(v_toApplicative_4321_, 3);
                v_toSeqRight_4328_ = crate::leanh::lean_ctor_get(v_toApplicative_4321_, 4);
                v_isSharedCheck_4398_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4321_)) as u8;
                if v_isSharedCheck_4398_ == 0 {
                    v_unused_4399_ = crate::leanh::lean_ctor_get(v_toApplicative_4321_, 1);
                    crate::leanh::lean_dec(v_unused_4399_);
                    v___x_4330_ = v_toApplicative_4321_;
                    v_isShared_4331_ = v_isSharedCheck_4398_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4328_);
                    crate::leanh::lean_inc(v_toSeqLeft_4327_);
                    crate::leanh::lean_inc(v_toSeq_4326_);
                    crate::leanh::lean_inc(v_toFunctor_4325_);
                    crate::leanh::lean_dec(v_toApplicative_4321_);
                    v___x_4330_ = crate::leanh::lean_box(0);
                    v_isShared_4331_ = v_isSharedCheck_4398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4332_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4332_, 0, v_inst_4296_);
                crate::leanh::lean_closure_set(v___f_4332_, 1, v_inst_4297_);
                v___f_4333_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_4334_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_4325_);
                v___f_4335_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4335_, 0, v_toFunctor_4325_);
                v___f_4336_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4336_, 0, v_toFunctor_4325_);
                v___x_4337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4337_, 0, v___f_4335_);
                crate::leanh::lean_ctor_set(v___x_4337_, 1, v___f_4336_);
                v___f_4338_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4338_, 0, v_toSeqRight_4328_);
                v___f_4339_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4339_, 0, v_toSeqLeft_4327_);
                v___f_4340_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4340_, 0, v_toSeq_4326_);
                if v_isShared_4331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4330_, 4, v___f_4338_);
                    crate::leanh::lean_ctor_set(v___x_4330_, 3, v___f_4339_);
                    crate::leanh::lean_ctor_set(v___x_4330_, 2, v___f_4340_);
                    crate::leanh::lean_ctor_set(v___x_4330_, 1, v___f_4333_);
                    crate::leanh::lean_ctor_set(v___x_4330_, 0, v___x_4337_);
                    v___x_4342_ = v___x_4330_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4397_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 1, v___f_4333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 2, v___f_4340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 3, v___f_4339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 4, v___f_4338_);
                    v___x_4342_ = v_reuseFailAlloc_4397_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4323_, 1, v___f_4334_);
                    crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4342_);
                    v___x_4344_ = v___x_4323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 1, v___f_4334_);
                    v___x_4344_ = v_reuseFailAlloc_4396_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4345_ = lean_array_get_size(v_data_4298_);
                v___x_4346_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4347_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4348_ = lean_nat_mul(v___x_4345_, v___x_4347_);
                v___x_4349_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4350_ = lean_nat_div(v___x_4348_, v___x_4349_);
                crate::leanh::lean_dec(v___x_4348_);
                v___x_4351_ = l_Nat_nextPowerOfTwo(v___x_4350_);
                crate::leanh::lean_dec(v___x_4350_);
                v___x_4352_ = crate::leanh::lean_box(0);
                v___x_4353_ = lean_mk_array(v___x_4351_, v___x_4352_);
                v_map_4354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_map_4354_, 0, v___x_4346_);
                crate::leanh::lean_ctor_set(v_map_4354_, 1, v___x_4353_);
                v_sz_4355_ = lean_array_size(v_data_4298_);
                v___x_4356_ = 0usize;
                v___x_747__overap_4357_ =
                    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_4344_,
                        v_data_4298_,
                        v___f_4332_,
                        v_sz_4355_,
                        v___x_4356_,
                        v_map_4354_,
                    );
                crate::leanh::lean_inc(v_a_4302_);
                crate::leanh::lean_inc_ref(v_a_4301_);
                crate::leanh::lean_inc(v_a_4300_);
                crate::leanh::lean_inc_ref(v_a_4299_);
                v___x_4358_ = crate::leanh::lean_apply_5(
                    v___x_747__overap_4357_,
                    v_a_4299_,
                    v_a_4300_,
                    v_a_4301_,
                    v_a_4302_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4358_) == 0 {
                    v_a_4359_ = crate::leanh::lean_ctor_get(v___x_4358_, 0);
                    v_isSharedCheck_4387_ = (!crate::leanh::lean_is_exclusive(v___x_4358_)) as u8;
                    if v_isSharedCheck_4387_ == 0 {
                        v___x_4361_ = v___x_4358_;
                        v_isShared_4362_ = v_isSharedCheck_4387_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4359_);
                        crate::leanh::lean_dec(v___x_4358_);
                        v___x_4361_ = crate::leanh::lean_box(0);
                        v_isShared_4362_ = v_isSharedCheck_4387_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_4388_ = crate::leanh::lean_ctor_get(v___x_4358_, 0);
                    v_isSharedCheck_4395_ = (!crate::leanh::lean_is_exclusive(v___x_4358_)) as u8;
                    if v_isSharedCheck_4395_ == 0 {
                        v___x_4390_ = v___x_4358_;
                        v_isShared_4391_ = v_isSharedCheck_4395_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4388_);
                        crate::leanh::lean_dec(v___x_4358_);
                        v___x_4390_ = crate::leanh::lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4395_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v_size_4363_ = crate::leanh::lean_ctor_get(v_a_4359_, 0);
                crate::leanh::lean_inc(v_size_4363_);
                v_buckets_4364_ = crate::leanh::lean_ctor_get(v_a_4359_, 1);
                crate::leanh::lean_inc_ref(v_buckets_4364_);
                crate::leanh::lean_dec(v_a_4359_);
                v___x_4365_ = lean_mk_empty_array_with_capacity(v_size_4363_);
                crate::leanh::lean_dec(v_size_4363_);
                v___x_4366_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9;
                v___x_4367_ = lean_array_get_size(v_buckets_4364_);
                v___x_4368_ = lean_nat_dec_lt(v___x_4346_, v___x_4367_);
                if v___x_4368_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_4364_);
                    if v_isShared_4362_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4365_);
                        v___x_4370_ = v___x_4361_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4365_);
                        v___x_4370_ = v_reuseFailAlloc_4371_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___f_4372_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1;
                    v___x_4373_ = lean_nat_dec_le(v___x_4367_, v___x_4367_);
                    if v___x_4373_ == 0 {
                        if v___x_4368_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_4364_);
                            if v_isShared_4362_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4365_);
                                v___x_4375_ = v___x_4361_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_4376_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4365_);
                                v___x_4375_ = v_reuseFailAlloc_4376_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___x_4377_ = lean_usize_of_nat(v___x_4367_);
                            v___x_4378_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_4366_,
                                    v___f_4372_,
                                    v_buckets_4364_,
                                    v___x_4356_,
                                    v___x_4377_,
                                    v___x_4365_,
                                );
                            if v_isShared_4362_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4378_);
                                v___x_4380_ = v___x_4361_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_4381_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
                                v___x_4380_ = v_reuseFailAlloc_4381_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        v___x_4382_ = lean_usize_of_nat(v___x_4367_);
                        v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4366_,
                            v___f_4372_,
                            v_buckets_4364_,
                            v___x_4356_,
                            v___x_4382_,
                            v___x_4365_,
                        );
                        if v_isShared_4362_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4383_);
                            v___x_4385_ = v___x_4361_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_4386_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
                            v___x_4385_ = v_reuseFailAlloc_4386_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_4370_;
            }
            7 => {
                return v___x_4375_;
            }
            8 => {
                return v___x_4380_;
            }
            9 => {
                return v___x_4385_;
            }
            10 => {
                if v_isShared_4391_ == 0 {
                    v___x_4393_ = v___x_4390_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4394_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
                    v___x_4393_ = v_reuseFailAlloc_4394_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUnique___redArg___boxed(
    mut v_inst_4402_: *mut crate::leanh::LeanObject,
    mut v_inst_4403_: *mut crate::leanh::LeanObject,
    mut v_data_4404_: *mut crate::leanh::LeanObject,
    mut v_a_4405_: *mut crate::leanh::LeanObject,
    mut v_a_4406_: *mut crate::leanh::LeanObject,
    mut v_a_4407_: *mut crate::leanh::LeanObject,
    mut v_a_4408_: *mut crate::leanh::LeanObject,
    mut v_a_4409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4410_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(
        v_inst_4402_,
        v_inst_4403_,
        v_data_4404_,
        v_a_4405_,
        v_a_4406_,
        v_a_4407_,
        v_a_4408_,
    );
    crate::leanh::lean_dec(v_a_4408_);
    crate::leanh::lean_dec_ref(v_a_4407_);
    crate::leanh::lean_dec(v_a_4406_);
    crate::leanh::lean_dec_ref(v_a_4405_);
    return v_res_4410_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUnique(
    mut v_00_u03b1_4411_: *mut crate::leanh::LeanObject,
    mut v_inst_4412_: *mut crate::leanh::LeanObject,
    mut v_inst_4413_: *mut crate::leanh::LeanObject,
    mut v_inst_4414_: *mut crate::leanh::LeanObject,
    mut v_data_4415_: *mut crate::leanh::LeanObject,
    mut v_a_4416_: *mut crate::leanh::LeanObject,
    mut v_a_4417_: *mut crate::leanh::LeanObject,
    mut v_a_4418_: *mut crate::leanh::LeanObject,
    mut v_a_4419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4421_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(
        v_inst_4413_,
        v_inst_4414_,
        v_data_4415_,
        v_a_4416_,
        v_a_4417_,
        v_a_4418_,
        v_a_4419_,
    );
    return v___x_4421_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUnique___boxed(
    mut v_00_u03b1_4422_: *mut crate::leanh::LeanObject,
    mut v_inst_4423_: *mut crate::leanh::LeanObject,
    mut v_inst_4424_: *mut crate::leanh::LeanObject,
    mut v_inst_4425_: *mut crate::leanh::LeanObject,
    mut v_data_4426_: *mut crate::leanh::LeanObject,
    mut v_a_4427_: *mut crate::leanh::LeanObject,
    mut v_a_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
    mut v_a_4430_: *mut crate::leanh::LeanObject,
    mut v_a_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4432_ = l_Lean_Compiler_LCNF_Probe_countUnique(
        v_00_u03b1_4422_,
        v_inst_4423_,
        v_inst_4424_,
        v_inst_4425_,
        v_data_4426_,
        v_a_4427_,
        v_a_4428_,
        v_a_4429_,
        v_a_4430_,
    );
    crate::leanh::lean_dec(v_a_4430_);
    crate::leanh::lean_dec_ref(v_a_4429_);
    crate::leanh::lean_dec(v_a_4428_);
    crate::leanh::lean_dec_ref(v_a_4427_);
    crate::leanh::lean_dec_ref(v_inst_4423_);
    return v_res_4432_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(
    mut v_l_4433_: *mut crate::leanh::LeanObject,
    mut v_r_4434_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_snd_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: u8 = 0;
    v_snd_4435_ = crate::leanh::lean_ctor_get(v_l_4433_, 1);
    v_snd_4436_ = crate::leanh::lean_ctor_get(v_r_4434_, 1);
    v___x_4437_ = lean_nat_dec_lt(v_snd_4435_, v_snd_4436_);
    return v___x_4437_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed(
    mut v_l_4438_: *mut crate::leanh::LeanObject,
    mut v_r_4439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4440_: u8 = 0;
    let mut v_r_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4440_ =
        l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(v_l_4438_, v_r_4439_);
    crate::leanh::lean_dec_ref(v_r_4439_);
    crate::leanh::lean_dec_ref(v_l_4438_);
    v_r_4441_ = crate::leanh::lean_box((v_res_4440_) as usize);
    return v_r_4441_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(
    mut v_inst_4443_: *mut crate::leanh::LeanObject,
    mut v_inst_4444_: *mut crate::leanh::LeanObject,
    mut v_a_4445_: *mut crate::leanh::LeanObject,
    mut v_a_4446_: *mut crate::leanh::LeanObject,
    mut v_a_4447_: *mut crate::leanh::LeanObject,
    mut v_a_4448_: *mut crate::leanh::LeanObject,
    mut v_a_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___f_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: u8 = 0;
    let mut v___x_4472_: u8 = 0;
    let mut v_isSharedCheck_4473_: u8 = 0;
    let mut v_unused_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4451_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(
                    v_inst_4443_,
                    v_inst_4444_,
                    v_a_4445_,
                    v_a_4446_,
                    v_a_4447_,
                    v_a_4448_,
                    v_a_4449_,
                );
                if crate::leanh::lean_obj_tag(v___x_4451_) == 0 {
                    v_a_4452_ = crate::leanh::lean_ctor_get(v___x_4451_, 0);
                    crate::leanh::lean_inc(v_a_4452_);
                    v___x_4453_ = lean_array_get_size(v_a_4452_);
                    v___x_4454_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4455_ = lean_nat_dec_eq(v___x_4453_, v___x_4454_);
                    if v___x_4455_ == 0 {
                        v_isSharedCheck_4473_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4451_)) as u8;
                        if v_isSharedCheck_4473_ == 0 {
                            v_unused_4474_ = crate::leanh::lean_ctor_get(v___x_4451_, 0);
                            crate::leanh::lean_dec(v_unused_4474_);
                            v___x_4457_ = v___x_4451_;
                            v_isShared_4458_ = v_isSharedCheck_4473_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4451_);
                            v___x_4457_ = crate::leanh::lean_box(0);
                            v_isShared_4458_ = v_isSharedCheck_4473_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4452_);
                        return v___x_4451_;
                    }
                } else {
                    return v___x_4451_;
                }
            }
            1 => {
                v___f_4459_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0;
                v___x_4467_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4468_ = lean_nat_sub(v___x_4453_, v___x_4467_);
                v___x_4472_ = lean_nat_dec_le(v___x_4454_, v___x_4468_);
                if v___x_4472_ == 0 {
                    crate::leanh::lean_inc(v___x_4468_);
                    v___y_4470_ = v___x_4468_;
                    state = 4;
                    continue;
                } else {
                    v___y_4470_ = v___x_4454_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_4463_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___f_4459_,
                    v___x_4453_,
                    v_a_4452_,
                    v___y_4461_,
                    v___y_4462_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_4462_);
                if v_isShared_4458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4457_, 0, v___x_4463_);
                    v___x_4465_ = v___x_4457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
                    v___x_4465_ = v_reuseFailAlloc_4466_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4465_;
            }
            4 => {
                v___x_4471_ = lean_nat_dec_le(v___y_4470_, v___x_4468_);
                if v___x_4471_ == 0 {
                    crate::leanh::lean_dec(v___x_4468_);
                    crate::leanh::lean_inc(v___y_4470_);
                    v___y_4461_ = v___y_4470_;
                    v___y_4462_ = v___y_4470_;
                    state = 2;
                    continue;
                } else {
                    v___y_4461_ = v___y_4470_;
                    v___y_4462_ = v___x_4468_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(
    mut v_inst_4475_: *mut crate::leanh::LeanObject,
    mut v_inst_4476_: *mut crate::leanh::LeanObject,
    mut v_a_4477_: *mut crate::leanh::LeanObject,
    mut v_a_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
    mut v_a_4480_: *mut crate::leanh::LeanObject,
    mut v_a_4481_: *mut crate::leanh::LeanObject,
    mut v_a_4482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4483_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(
        v_inst_4475_,
        v_inst_4476_,
        v_a_4477_,
        v_a_4478_,
        v_a_4479_,
        v_a_4480_,
        v_a_4481_,
    );
    crate::leanh::lean_dec(v_a_4481_);
    crate::leanh::lean_dec_ref(v_a_4480_);
    crate::leanh::lean_dec(v_a_4479_);
    crate::leanh::lean_dec_ref(v_a_4478_);
    return v_res_4483_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUniqueSorted(
    mut v_00_u03b1_4484_: *mut crate::leanh::LeanObject,
    mut v_inst_4485_: *mut crate::leanh::LeanObject,
    mut v_inst_4486_: *mut crate::leanh::LeanObject,
    mut v_inst_4487_: *mut crate::leanh::LeanObject,
    mut v_inst_4488_: *mut crate::leanh::LeanObject,
    mut v_a_4489_: *mut crate::leanh::LeanObject,
    mut v_a_4490_: *mut crate::leanh::LeanObject,
    mut v_a_4491_: *mut crate::leanh::LeanObject,
    mut v_a_4492_: *mut crate::leanh::LeanObject,
    mut v_a_4493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___f_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: u8 = 0;
    let mut v___x_4516_: u8 = 0;
    let mut v_isSharedCheck_4517_: u8 = 0;
    let mut v_unused_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4495_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(
                    v_inst_4486_,
                    v_inst_4487_,
                    v_a_4489_,
                    v_a_4490_,
                    v_a_4491_,
                    v_a_4492_,
                    v_a_4493_,
                );
                if crate::leanh::lean_obj_tag(v___x_4495_) == 0 {
                    v_a_4496_ = crate::leanh::lean_ctor_get(v___x_4495_, 0);
                    crate::leanh::lean_inc(v_a_4496_);
                    v___x_4497_ = lean_array_get_size(v_a_4496_);
                    v___x_4498_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4499_ = lean_nat_dec_eq(v___x_4497_, v___x_4498_);
                    if v___x_4499_ == 0 {
                        v_isSharedCheck_4517_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4495_)) as u8;
                        if v_isSharedCheck_4517_ == 0 {
                            v_unused_4518_ = crate::leanh::lean_ctor_get(v___x_4495_, 0);
                            crate::leanh::lean_dec(v_unused_4518_);
                            v___x_4501_ = v___x_4495_;
                            v_isShared_4502_ = v_isSharedCheck_4517_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4495_);
                            v___x_4501_ = crate::leanh::lean_box(0);
                            v_isShared_4502_ = v_isSharedCheck_4517_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4496_);
                        return v___x_4495_;
                    }
                } else {
                    return v___x_4495_;
                }
            }
            1 => {
                v___f_4503_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0;
                v___x_4511_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4512_ = lean_nat_sub(v___x_4497_, v___x_4511_);
                v___x_4516_ = lean_nat_dec_le(v___x_4498_, v___x_4512_);
                if v___x_4516_ == 0 {
                    crate::leanh::lean_inc(v___x_4512_);
                    v___y_4514_ = v___x_4512_;
                    state = 4;
                    continue;
                } else {
                    v___y_4514_ = v___x_4498_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_4507_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___f_4503_,
                    v___x_4497_,
                    v_a_4496_,
                    v___y_4505_,
                    v___y_4506_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_4506_);
                if v_isShared_4502_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4501_, 0, v___x_4507_);
                    v___x_4509_ = v___x_4501_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
                    v___x_4509_ = v_reuseFailAlloc_4510_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4509_;
            }
            4 => {
                v___x_4515_ = lean_nat_dec_le(v___y_4514_, v___x_4512_);
                if v___x_4515_ == 0 {
                    crate::leanh::lean_dec(v___x_4512_);
                    crate::leanh::lean_inc(v___y_4514_);
                    v___y_4505_ = v___y_4514_;
                    v___y_4506_ = v___y_4514_;
                    state = 2;
                    continue;
                } else {
                    v___y_4505_ = v___y_4514_;
                    v___y_4506_ = v___x_4512_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(
    mut v_00_u03b1_4519_: *mut crate::leanh::LeanObject,
    mut v_inst_4520_: *mut crate::leanh::LeanObject,
    mut v_inst_4521_: *mut crate::leanh::LeanObject,
    mut v_inst_4522_: *mut crate::leanh::LeanObject,
    mut v_inst_4523_: *mut crate::leanh::LeanObject,
    mut v_a_4524_: *mut crate::leanh::LeanObject,
    mut v_a_4525_: *mut crate::leanh::LeanObject,
    mut v_a_4526_: *mut crate::leanh::LeanObject,
    mut v_a_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_a_4529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4530_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(
        v_00_u03b1_4519_,
        v_inst_4520_,
        v_inst_4521_,
        v_inst_4522_,
        v_inst_4523_,
        v_a_4524_,
        v_a_4525_,
        v_a_4526_,
        v_a_4527_,
        v_a_4528_,
    );
    crate::leanh::lean_dec(v_a_4528_);
    crate::leanh::lean_dec_ref(v_a_4527_);
    crate::leanh::lean_dec(v_a_4526_);
    crate::leanh::lean_dec_ref(v_a_4525_);
    crate::leanh::lean_dec(v_inst_4523_);
    crate::leanh::lean_dec_ref(v_inst_4520_);
    return v_res_4530_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(
    mut v_pu_4531_: u8,
    mut v_c_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
    mut v_a_4534_: *mut crate::leanh::LeanObject,
    mut v_a_4535_: *mut crate::leanh::LeanObject,
    mut v_a_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v_alts_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: u8 = 0;
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: usize = 0;
    let mut v___x_4573_: usize = 0;
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: usize = 0;
    let mut v___x_4576_: usize = 0;
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut v_k_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_c_4532_) {
                0 => {
                    v_decl_4539_ = crate::leanh::lean_ctor_get(v_c_4532_, 0);
                    crate::leanh::lean_inc_ref(v_decl_4539_);
                    v_k_4540_ = crate::leanh::lean_ctor_get(v_c_4532_, 1);
                    crate::leanh::lean_inc_ref(v_k_4540_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 2);
                    v___x_4541_ = lean_st_ref_take(v_a_4533_);
                    v_value_4542_ = crate::leanh::lean_ctor_get(v_decl_4539_, 3);
                    crate::leanh::lean_inc(v_value_4542_);
                    crate::leanh::lean_dec_ref(v_decl_4539_);
                    v___x_4543_ = lean_array_push(v___x_4541_, v_value_4542_);
                    v___x_4544_ = lean_st_ref_set(v_a_4533_, v___x_4543_);
                    v_c_4532_ = v_k_4540_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_4546_ = crate::leanh::lean_ctor_get(v_c_4532_, 0);
                    crate::leanh::lean_inc_ref(v_decl_4546_);
                    v_k_4547_ = crate::leanh::lean_ctor_get(v_c_4532_, 1);
                    crate::leanh::lean_inc_ref(v_k_4547_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 2);
                    v_value_4548_ = crate::leanh::lean_ctor_get(v_decl_4546_, 4);
                    crate::leanh::lean_inc_ref(v_value_4548_);
                    crate::leanh::lean_dec_ref(v_decl_4546_);
                    v___x_4549_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_4531_, v_value_4548_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
                    if crate::leanh::lean_obj_tag(v___x_4549_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4549_, 1);
                        v_c_4532_ = v_k_4547_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_4547_);
                        return v___x_4549_;
                    }
                }
                2 => {
                    v_decl_4551_ = crate::leanh::lean_ctor_get(v_c_4532_, 0);
                    crate::leanh::lean_inc_ref(v_decl_4551_);
                    v_k_4552_ = crate::leanh::lean_ctor_get(v_c_4532_, 1);
                    crate::leanh::lean_inc_ref(v_k_4552_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 2);
                    v_value_4553_ = crate::leanh::lean_ctor_get(v_decl_4551_, 4);
                    crate::leanh::lean_inc_ref(v_value_4553_);
                    crate::leanh::lean_dec_ref(v_decl_4551_);
                    v___x_4554_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_4531_, v_value_4553_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
                    if crate::leanh::lean_obj_tag(v___x_4554_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4554_, 1);
                        v_c_4532_ = v_k_4552_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_4552_);
                        return v___x_4554_;
                    }
                }
                4 => {
                    v_cases_4556_ = crate::leanh::lean_ctor_get(v_c_4532_, 0);
                    v_isSharedCheck_4578_ = (!crate::leanh::lean_is_exclusive(v_c_4532_)) as u8;
                    if v_isSharedCheck_4578_ == 0 {
                        v___x_4558_ = v_c_4532_;
                        v_isShared_4559_ = v_isSharedCheck_4578_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_4556_);
                        crate::leanh::lean_dec(v_c_4532_);
                        v___x_4558_ = crate::leanh::lean_box(0);
                        v_isShared_4559_ = v_isSharedCheck_4578_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_k_4579_ = crate::leanh::lean_ctor_get(v_c_4532_, 3);
                    crate::leanh::lean_inc_ref(v_k_4579_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 4);
                    v_c_4532_ = v_k_4579_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_4581_ = crate::leanh::lean_ctor_get(v_c_4532_, 3);
                    crate::leanh::lean_inc_ref(v_k_4581_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 4);
                    v_c_4532_ = v_k_4581_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_4583_ = crate::leanh::lean_ctor_get(v_c_4532_, 5);
                    crate::leanh::lean_inc_ref(v_k_4583_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 6);
                    v_c_4532_ = v_k_4583_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_4585_ = crate::leanh::lean_ctor_get(v_c_4532_, 2);
                    crate::leanh::lean_inc_ref(v_k_4585_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 3);
                    v_c_4532_ = v_k_4585_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_4587_ = crate::leanh::lean_ctor_get(v_c_4532_, 2);
                    crate::leanh::lean_inc_ref(v_k_4587_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 3);
                    v_c_4532_ = v_k_4587_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_4589_ = crate::leanh::lean_ctor_get(v_c_4532_, 3);
                    crate::leanh::lean_inc_ref(v_k_4589_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 4);
                    v_c_4532_ = v_k_4589_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_4591_ = crate::leanh::lean_ctor_get(v_c_4532_, 1);
                    crate::leanh::lean_inc_ref(v_k_4591_);
                    crate::leanh::lean_dec_ref_known(v_c_4532_, 2);
                    v_c_4532_ = v_k_4591_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_c_4532_);
                    v___x_4593_ = crate::leanh::lean_box(0);
                    v___x_4594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4594_, 0, v___x_4593_);
                    return v___x_4594_;
                }
            },
            1 => {
                v_alts_4560_ = crate::leanh::lean_ctor_get(v_cases_4556_, 3);
                crate::leanh::lean_inc_ref(v_alts_4560_);
                crate::leanh::lean_dec_ref(v_cases_4556_);
                v___x_4561_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4562_ = lean_array_get_size(v_alts_4560_);
                v___x_4563_ = crate::leanh::lean_box(0);
                v___x_4564_ = lean_nat_dec_lt(v___x_4561_, v___x_4562_);
                if v___x_4564_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_4560_);
                    if v_isShared_4559_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4558_, 0);
                        crate::leanh::lean_ctor_set(v___x_4558_, 0, v___x_4563_);
                        v___x_4566_ = v___x_4558_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4563_);
                        v___x_4566_ = v_reuseFailAlloc_4567_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4568_ = lean_nat_dec_le(v___x_4562_, v___x_4562_);
                    if v___x_4568_ == 0 {
                        if v___x_4564_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_4560_);
                            if v_isShared_4559_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4558_, 0);
                                crate::leanh::lean_ctor_set(v___x_4558_, 0, v___x_4563_);
                                v___x_4570_ = v___x_4558_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4571_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4563_);
                                v___x_4570_ = v_reuseFailAlloc_4571_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4558_);
                            v___x_4572_ = 0usize;
                            v___x_4573_ = lean_usize_of_nat(v___x_4562_);
                            v___x_4574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_4531_, v_alts_4560_, v___x_4572_, v___x_4573_, v___x_4563_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
                            crate::leanh::lean_dec_ref(v_alts_4560_);
                            return v___x_4574_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4558_);
                        v___x_4575_ = 0usize;
                        v___x_4576_ = lean_usize_of_nat(v___x_4562_);
                        v___x_4577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_4531_, v_alts_4560_, v___x_4575_, v___x_4576_, v___x_4563_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
                        crate::leanh::lean_dec_ref(v_alts_4560_);
                        return v___x_4577_;
                    }
                }
            }
            2 => {
                return v___x_4566_;
            }
            3 => {
                return v___x_4570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(
    mut v_pu_4595_: u8,
    mut v_as_4596_: *mut crate::leanh::LeanObject,
    mut v_i_4597_: usize,
    mut v_stop_4598_: usize,
    mut v_b_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
    mut v___y_4601_: *mut crate::leanh::LeanObject,
    mut v___y_4602_: *mut crate::leanh::LeanObject,
    mut v___y_4603_: *mut crate::leanh::LeanObject,
    mut v___y_4604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: usize = 0;
    let mut v___x_4611_: usize = 0;
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4613_ = lean_usize_dec_eq(v_i_4597_, v_stop_4598_);
                if v___x_4613_ == 0 {
                    v___x_4614_ = lean_array_uget_borrowed(v_as_4596_, v_i_4597_);
                    match crate::leanh::lean_obj_tag(v___x_4614_) {
                        0 => {
                            v_code_4615_ = crate::leanh::lean_ctor_get(v___x_4614_, 2);
                            crate::leanh::lean_inc_ref(v_code_4615_);
                            v___y_4607_ = v_code_4615_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_4616_ = crate::leanh::lean_ctor_get(v___x_4614_, 1);
                            crate::leanh::lean_inc_ref(v_code_4616_);
                            v___y_4607_ = v_code_4616_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_4617_ = crate::leanh::lean_ctor_get(v___x_4614_, 0);
                            crate::leanh::lean_inc_ref(v_code_4617_);
                            v___y_4607_ = v_code_4617_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_4618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4618_, 0, v_b_4599_);
                    return v___x_4618_;
                }
            }
            1 => {
                v___x_4608_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_4595_, v___y_4607_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
                if crate::leanh::lean_obj_tag(v___x_4608_) == 0 {
                    v_a_4609_ = crate::leanh::lean_ctor_get(v___x_4608_, 0);
                    crate::leanh::lean_inc(v_a_4609_);
                    crate::leanh::lean_dec_ref_known(v___x_4608_, 1);
                    v___x_4610_ = 1usize;
                    v___x_4611_ = lean_usize_add(v_i_4597_, v___x_4610_);
                    v_i_4597_ = v___x_4611_;
                    v_b_4599_ = v_a_4609_;
                    state = 0;
                    continue;
                } else {
                    return v___x_4608_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(
    mut v_pu_4619_: *mut crate::leanh::LeanObject,
    mut v_as_4620_: *mut crate::leanh::LeanObject,
    mut v_i_4621_: *mut crate::leanh::LeanObject,
    mut v_stop_4622_: *mut crate::leanh::LeanObject,
    mut v_b_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4630_: u8 = 0;
    let mut v_i_boxed_4631_: usize = 0;
    let mut v_stop_boxed_4632_: usize = 0;
    let mut v_res_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4630_ = (crate::leanh::lean_unbox(v_pu_4619_) as u8);
    v_i_boxed_4631_ = crate::leanh::lean_unbox_usize(v_i_4621_);
    crate::leanh::lean_dec(v_i_4621_);
    v_stop_boxed_4632_ = crate::leanh::lean_unbox_usize(v_stop_4622_);
    crate::leanh::lean_dec(v_stop_4622_);
    v_res_4633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_boxed_4630_, v_as_4620_, v_i_boxed_4631_, v_stop_boxed_4632_, v_b_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
    crate::leanh::lean_dec(v___y_4628_);
    crate::leanh::lean_dec_ref(v___y_4627_);
    crate::leanh::lean_dec(v___y_4626_);
    crate::leanh::lean_dec_ref(v___y_4625_);
    crate::leanh::lean_dec(v___y_4624_);
    crate::leanh::lean_dec_ref(v_as_4620_);
    return v_res_4633_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(
    mut v_pu_4634_: *mut crate::leanh::LeanObject,
    mut v_c_4635_: *mut crate::leanh::LeanObject,
    mut v_a_4636_: *mut crate::leanh::LeanObject,
    mut v_a_4637_: *mut crate::leanh::LeanObject,
    mut v_a_4638_: *mut crate::leanh::LeanObject,
    mut v_a_4639_: *mut crate::leanh::LeanObject,
    mut v_a_4640_: *mut crate::leanh::LeanObject,
    mut v_a_4641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4642_: u8 = 0;
    let mut v_res_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4642_ = (crate::leanh::lean_unbox(v_pu_4634_) as u8);
    v_res_4643_ =
        l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(
            v_pu_boxed_4642_,
            v_c_4635_,
            v_a_4636_,
            v_a_4637_,
            v_a_4638_,
            v_a_4639_,
            v_a_4640_,
        );
    crate::leanh::lean_dec(v_a_4640_);
    crate::leanh::lean_dec_ref(v_a_4639_);
    crate::leanh::lean_dec(v_a_4638_);
    crate::leanh::lean_dec_ref(v_a_4637_);
    crate::leanh::lean_dec(v_a_4636_);
    return v_res_4643_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(
    mut v_f_4644_: *mut crate::leanh::LeanObject,
    mut v_v_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4656_: u8 = 0;
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4661_: u8 = 0;
    let mut v_unused_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_4645_) == 0 {
                    v_code_4652_ = crate::leanh::lean_ctor_get(v_v_4645_, 0);
                    crate::leanh::lean_inc_ref(v_code_4652_);
                    crate::leanh::lean_dec_ref_known(v_v_4645_, 1);
                    crate::leanh::lean_inc(v___y_4650_);
                    crate::leanh::lean_inc_ref(v___y_4649_);
                    crate::leanh::lean_inc(v___y_4648_);
                    crate::leanh::lean_inc_ref(v___y_4647_);
                    crate::leanh::lean_inc(v___y_4646_);
                    v___x_4653_ = crate::leanh::lean_apply_7(
                        v_f_4644_,
                        v_code_4652_,
                        v___y_4646_,
                        v___y_4647_,
                        v___y_4648_,
                        v___y_4649_,
                        v___y_4650_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4653_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_4644_);
                    v_isSharedCheck_4661_ = (!crate::leanh::lean_is_exclusive(v_v_4645_)) as u8;
                    if v_isSharedCheck_4661_ == 0 {
                        v_unused_4662_ = crate::leanh::lean_ctor_get(v_v_4645_, 0);
                        crate::leanh::lean_dec(v_unused_4662_);
                        v___x_4655_ = v_v_4645_;
                        v_isShared_4656_ = v_isSharedCheck_4661_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_4645_);
                        v___x_4655_ = crate::leanh::lean_box(0);
                        v_isShared_4656_ = v_isSharedCheck_4661_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4657_ = crate::leanh::lean_box(0);
                if v_isShared_4656_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4655_, 0);
                    crate::leanh::lean_ctor_set(v___x_4655_, 0, v___x_4657_);
                    v___x_4659_ = v___x_4655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4657_);
                    v___x_4659_ = v_reuseFailAlloc_4660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(
    mut v_f_4663_: *mut crate::leanh::LeanObject,
    mut v_v_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
    mut v___y_4668_: *mut crate::leanh::LeanObject,
    mut v___y_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4671_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_4663_, v_v_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
    crate::leanh::lean_dec(v___y_4669_);
    crate::leanh::lean_dec_ref(v___y_4668_);
    crate::leanh::lean_dec(v___y_4667_);
    crate::leanh::lean_dec_ref(v___y_4666_);
    crate::leanh::lean_dec(v___y_4665_);
    return v_res_4671_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(
    mut v_pu_4672_: u8,
    mut v_f_4673_: *mut crate::leanh::LeanObject,
    mut v_v_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
    mut v___y_4676_: *mut crate::leanh::LeanObject,
    mut v___y_4677_: *mut crate::leanh::LeanObject,
    mut v___y_4678_: *mut crate::leanh::LeanObject,
    mut v___y_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4681_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_4673_, v_v_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
    return v___x_4681_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(
    mut v_pu_4682_: *mut crate::leanh::LeanObject,
    mut v_f_4683_: *mut crate::leanh::LeanObject,
    mut v_v_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4691_: u8 = 0;
    let mut v_res_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4691_ = (crate::leanh::lean_unbox(v_pu_4682_) as u8);
    v_res_4692_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_boxed_4691_, v_f_4683_, v_v_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
    crate::leanh::lean_dec(v___y_4689_);
    crate::leanh::lean_dec_ref(v___y_4688_);
    crate::leanh::lean_dec(v___y_4687_);
    crate::leanh::lean_dec_ref(v___y_4686_);
    crate::leanh::lean_dec(v___y_4685_);
    return v_res_4692_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(
    mut v_pu_4693_: u8,
    mut v_as_4694_: *mut crate::leanh::LeanObject,
    mut v_i_4695_: usize,
    mut v_stop_4696_: usize,
    mut v_b_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
    mut v___y_4699_: *mut crate::leanh::LeanObject,
    mut v___y_4700_: *mut crate::leanh::LeanObject,
    mut v___y_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4704_: u8 = 0;
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: usize = 0;
    let mut v___x_4712_: usize = 0;
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4704_ = lean_usize_dec_eq(v_i_4695_, v_stop_4696_);
                if v___x_4704_ == 0 {
                    v___x_4705_ = lean_array_uget_borrowed(v_as_4694_, v_i_4695_);
                    v_value_4706_ = crate::leanh::lean_ctor_get(v___x_4705_, 1);
                    v___x_4707_ = crate::leanh::lean_box((v_pu_4693_) as usize);
                    v___x_4708_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___x_4708_, 0, v___x_4707_);
                    crate::leanh::lean_inc_ref(v_value_4706_);
                    v___x_4709_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v___x_4708_, v_value_4706_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
                    if crate::leanh::lean_obj_tag(v___x_4709_) == 0 {
                        v_a_4710_ = crate::leanh::lean_ctor_get(v___x_4709_, 0);
                        crate::leanh::lean_inc(v_a_4710_);
                        crate::leanh::lean_dec_ref_known(v___x_4709_, 1);
                        v___x_4711_ = 1usize;
                        v___x_4712_ = lean_usize_add(v_i_4695_, v___x_4711_);
                        v_i_4695_ = v___x_4712_;
                        v_b_4697_ = v_a_4710_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4709_;
                    }
                } else {
                    v___x_4714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4714_, 0, v_b_4697_);
                    return v___x_4714_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1___boxed(
    mut v_pu_4715_: *mut crate::leanh::LeanObject,
    mut v_as_4716_: *mut crate::leanh::LeanObject,
    mut v_i_4717_: *mut crate::leanh::LeanObject,
    mut v_stop_4718_: *mut crate::leanh::LeanObject,
    mut v_b_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
    mut v___y_4722_: *mut crate::leanh::LeanObject,
    mut v___y_4723_: *mut crate::leanh::LeanObject,
    mut v___y_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4726_: u8 = 0;
    let mut v_i_boxed_4727_: usize = 0;
    let mut v_stop_boxed_4728_: usize = 0;
    let mut v_res_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4726_ = (crate::leanh::lean_unbox(v_pu_4715_) as u8);
    v_i_boxed_4727_ = crate::leanh::lean_unbox_usize(v_i_4717_);
    crate::leanh::lean_dec(v_i_4717_);
    v_stop_boxed_4728_ = crate::leanh::lean_unbox_usize(v_stop_4718_);
    crate::leanh::lean_dec(v_stop_4718_);
    v_res_4729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_boxed_4726_, v_as_4716_, v_i_boxed_4727_, v_stop_boxed_4728_, v_b_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
    crate::leanh::lean_dec(v___y_4724_);
    crate::leanh::lean_dec_ref(v___y_4723_);
    crate::leanh::lean_dec(v___y_4722_);
    crate::leanh::lean_dec_ref(v___y_4721_);
    crate::leanh::lean_dec(v___y_4720_);
    crate::leanh::lean_dec_ref(v_as_4716_);
    return v_res_4729_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(
    mut v_pu_4730_: u8,
    mut v_decls_4731_: *mut crate::leanh::LeanObject,
    mut v_a_4732_: *mut crate::leanh::LeanObject,
    mut v_a_4733_: *mut crate::leanh::LeanObject,
    mut v_a_4734_: *mut crate::leanh::LeanObject,
    mut v_a_4735_: *mut crate::leanh::LeanObject,
    mut v_a_4736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: u8 = 0;
    v___x_4738_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4739_ = lean_array_get_size(v_decls_4731_);
    v___x_4740_ = crate::leanh::lean_box(0);
    v___x_4741_ = lean_nat_dec_lt(v___x_4738_, v___x_4739_);
    if v___x_4741_ == 0 {
        let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4742_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4742_, 0, v___x_4740_);
        return v___x_4742_;
    } else {
        let mut v___x_4743_: u8 = 0;
        v___x_4743_ = lean_nat_dec_le(v___x_4739_, v___x_4739_);
        if v___x_4743_ == 0 {
            if v___x_4741_ == 0 {
                let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4744_, 0, v___x_4740_);
                return v___x_4744_;
            } else {
                let mut v___x_4745_: usize = 0;
                let mut v___x_4746_: usize = 0;
                let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4745_ = 0usize;
                v___x_4746_ = lean_usize_of_nat(v___x_4739_);
                v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_4730_, v_decls_4731_, v___x_4745_, v___x_4746_, v___x_4740_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
                return v___x_4747_;
            }
        } else {
            let mut v___x_4748_: usize = 0;
            let mut v___x_4749_: usize = 0;
            let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4748_ = 0usize;
            v___x_4749_ = lean_usize_of_nat(v___x_4739_);
            v___x_4750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_4730_, v_decls_4731_, v___x_4748_, v___x_4749_, v___x_4740_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
            return v___x_4750_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(
    mut v_pu_4751_: *mut crate::leanh::LeanObject,
    mut v_decls_4752_: *mut crate::leanh::LeanObject,
    mut v_a_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v_a_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4759_: u8 = 0;
    let mut v_res_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4759_ = (crate::leanh::lean_unbox(v_pu_4751_) as u8);
    v_res_4760_ =
        l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(
            v_pu_boxed_4759_,
            v_decls_4752_,
            v_a_4753_,
            v_a_4754_,
            v_a_4755_,
            v_a_4756_,
            v_a_4757_,
        );
    crate::leanh::lean_dec(v_a_4757_);
    crate::leanh::lean_dec_ref(v_a_4756_);
    crate::leanh::lean_dec(v_a_4755_);
    crate::leanh::lean_dec_ref(v_a_4754_);
    crate::leanh::lean_dec(v_a_4753_);
    crate::leanh::lean_dec_ref(v_decls_4752_);
    return v_res_4760_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_getLetValues(
    mut v_pu_4763_: u8,
    mut v_decls_4764_: *mut crate::leanh::LeanObject,
    mut v_a_4765_: *mut crate::leanh::LeanObject,
    mut v_a_4766_: *mut crate::leanh::LeanObject,
    mut v_a_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4775_: u8 = 0;
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4780_: u8 = 0;
    let mut v_unused_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4785_: u8 = 0;
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4770_ = l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0;
                v___x_4771_ = lean_st_mk_ref(v___x_4770_);
                v___x_4772_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_4763_, v_decls_4764_, v___x_4771_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
                if crate::leanh::lean_obj_tag(v___x_4772_) == 0 {
                    v_isSharedCheck_4780_ = (!crate::leanh::lean_is_exclusive(v___x_4772_)) as u8;
                    if v_isSharedCheck_4780_ == 0 {
                        v_unused_4781_ = crate::leanh::lean_ctor_get(v___x_4772_, 0);
                        crate::leanh::lean_dec(v_unused_4781_);
                        v___x_4774_ = v___x_4772_;
                        v_isShared_4775_ = v_isSharedCheck_4780_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4772_);
                        v___x_4774_ = crate::leanh::lean_box(0);
                        v_isShared_4775_ = v_isSharedCheck_4780_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4771_);
                    v_a_4782_ = crate::leanh::lean_ctor_get(v___x_4772_, 0);
                    v_isSharedCheck_4789_ = (!crate::leanh::lean_is_exclusive(v___x_4772_)) as u8;
                    if v_isSharedCheck_4789_ == 0 {
                        v___x_4784_ = v___x_4772_;
                        v_isShared_4785_ = v_isSharedCheck_4789_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4782_);
                        crate::leanh::lean_dec(v___x_4772_);
                        v___x_4784_ = crate::leanh::lean_box(0);
                        v_isShared_4785_ = v_isSharedCheck_4789_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4776_ = lean_st_ref_get(v___x_4771_);
                crate::leanh::lean_dec(v___x_4771_);
                if v_isShared_4775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4774_, 0, v___x_4776_);
                    v___x_4778_ = v___x_4774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
                    v___x_4778_ = v_reuseFailAlloc_4779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4778_;
            }
            3 => {
                if v_isShared_4785_ == 0 {
                    v___x_4787_ = v___x_4784_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4788_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
                    v___x_4787_ = v_reuseFailAlloc_4788_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(
    mut v_pu_4790_: *mut crate::leanh::LeanObject,
    mut v_decls_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
    mut v_a_4793_: *mut crate::leanh::LeanObject,
    mut v_a_4794_: *mut crate::leanh::LeanObject,
    mut v_a_4795_: *mut crate::leanh::LeanObject,
    mut v_a_4796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4797_: u8 = 0;
    let mut v_res_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4797_ = (crate::leanh::lean_unbox(v_pu_4790_) as u8);
    v_res_4798_ = l_Lean_Compiler_LCNF_Probe_getLetValues(
        v_pu_boxed_4797_,
        v_decls_4791_,
        v_a_4792_,
        v_a_4793_,
        v_a_4794_,
        v_a_4795_,
    );
    crate::leanh::lean_dec(v_a_4795_);
    crate::leanh::lean_dec_ref(v_a_4794_);
    crate::leanh::lean_dec(v_a_4793_);
    crate::leanh::lean_dec_ref(v_a_4792_);
    crate::leanh::lean_dec_ref(v_decls_4791_);
    return v_res_4798_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(
    mut v_pu_4799_: u8,
    mut v_code_4800_: *mut crate::leanh::LeanObject,
    mut v_a_4801_: *mut crate::leanh::LeanObject,
    mut v_a_4802_: *mut crate::leanh::LeanObject,
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v_alts_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: u8 = 0;
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: usize = 0;
    let mut v___x_4839_: usize = 0;
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: usize = 0;
    let mut v___x_4842_: usize = 0;
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4844_: u8 = 0;
    let mut v_k_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_4800_) {
                0 => {
                    v_k_4807_ = crate::leanh::lean_ctor_get(v_code_4800_, 1);
                    crate::leanh::lean_inc_ref(v_k_4807_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 2);
                    v_code_4800_ = v_k_4807_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_4809_ = crate::leanh::lean_ctor_get(v_code_4800_, 0);
                    crate::leanh::lean_inc_ref(v_decl_4809_);
                    v_k_4810_ = crate::leanh::lean_ctor_get(v_code_4800_, 1);
                    crate::leanh::lean_inc_ref(v_k_4810_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 2);
                    v_value_4811_ = crate::leanh::lean_ctor_get(v_decl_4809_, 4);
                    crate::leanh::lean_inc_ref(v_value_4811_);
                    crate::leanh::lean_dec_ref(v_decl_4809_);
                    v___x_4812_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_4799_, v_value_4811_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
                    if crate::leanh::lean_obj_tag(v___x_4812_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4812_, 1);
                        v_code_4800_ = v_k_4810_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_4810_);
                        return v___x_4812_;
                    }
                }
                2 => {
                    v_decl_4814_ = crate::leanh::lean_ctor_get(v_code_4800_, 0);
                    crate::leanh::lean_inc_ref_n(v_decl_4814_, 2);
                    v_k_4815_ = crate::leanh::lean_ctor_get(v_code_4800_, 1);
                    crate::leanh::lean_inc_ref(v_k_4815_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 2);
                    v___x_4816_ = lean_st_ref_take(v_a_4801_);
                    v___x_4817_ = lean_array_push(v___x_4816_, v_decl_4814_);
                    v___x_4818_ = lean_st_ref_set(v_a_4801_, v___x_4817_);
                    v_value_4819_ = crate::leanh::lean_ctor_get(v_decl_4814_, 4);
                    crate::leanh::lean_inc_ref(v_value_4819_);
                    crate::leanh::lean_dec_ref(v_decl_4814_);
                    v___x_4820_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_4799_, v_value_4819_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
                    if crate::leanh::lean_obj_tag(v___x_4820_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4820_, 1);
                        v_code_4800_ = v_k_4815_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_4815_);
                        return v___x_4820_;
                    }
                }
                4 => {
                    v_cases_4822_ = crate::leanh::lean_ctor_get(v_code_4800_, 0);
                    v_isSharedCheck_4844_ = (!crate::leanh::lean_is_exclusive(v_code_4800_)) as u8;
                    if v_isSharedCheck_4844_ == 0 {
                        v___x_4824_ = v_code_4800_;
                        v_isShared_4825_ = v_isSharedCheck_4844_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_4822_);
                        crate::leanh::lean_dec(v_code_4800_);
                        v___x_4824_ = crate::leanh::lean_box(0);
                        v_isShared_4825_ = v_isSharedCheck_4844_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_k_4845_ = crate::leanh::lean_ctor_get(v_code_4800_, 3);
                    crate::leanh::lean_inc_ref(v_k_4845_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 4);
                    v_code_4800_ = v_k_4845_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_4847_ = crate::leanh::lean_ctor_get(v_code_4800_, 3);
                    crate::leanh::lean_inc_ref(v_k_4847_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 4);
                    v_code_4800_ = v_k_4847_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_4849_ = crate::leanh::lean_ctor_get(v_code_4800_, 5);
                    crate::leanh::lean_inc_ref(v_k_4849_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 6);
                    v_code_4800_ = v_k_4849_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_4851_ = crate::leanh::lean_ctor_get(v_code_4800_, 2);
                    crate::leanh::lean_inc_ref(v_k_4851_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 3);
                    v_code_4800_ = v_k_4851_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_4853_ = crate::leanh::lean_ctor_get(v_code_4800_, 2);
                    crate::leanh::lean_inc_ref(v_k_4853_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 3);
                    v_code_4800_ = v_k_4853_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_4855_ = crate::leanh::lean_ctor_get(v_code_4800_, 3);
                    crate::leanh::lean_inc_ref(v_k_4855_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 4);
                    v_code_4800_ = v_k_4855_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_4857_ = crate::leanh::lean_ctor_get(v_code_4800_, 1);
                    crate::leanh::lean_inc_ref(v_k_4857_);
                    crate::leanh::lean_dec_ref_known(v_code_4800_, 2);
                    v_code_4800_ = v_k_4857_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_code_4800_);
                    v___x_4859_ = crate::leanh::lean_box(0);
                    v___x_4860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4860_, 0, v___x_4859_);
                    return v___x_4860_;
                }
            },
            1 => {
                v_alts_4826_ = crate::leanh::lean_ctor_get(v_cases_4822_, 3);
                crate::leanh::lean_inc_ref(v_alts_4826_);
                crate::leanh::lean_dec_ref(v_cases_4822_);
                v___x_4827_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4828_ = lean_array_get_size(v_alts_4826_);
                v___x_4829_ = crate::leanh::lean_box(0);
                v___x_4830_ = lean_nat_dec_lt(v___x_4827_, v___x_4828_);
                if v___x_4830_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_4826_);
                    if v_isShared_4825_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4824_, 0);
                        crate::leanh::lean_ctor_set(v___x_4824_, 0, v___x_4829_);
                        v___x_4832_ = v___x_4824_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4829_);
                        v___x_4832_ = v_reuseFailAlloc_4833_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4834_ = lean_nat_dec_le(v___x_4828_, v___x_4828_);
                    if v___x_4834_ == 0 {
                        if v___x_4830_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_4826_);
                            if v_isShared_4825_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4824_, 0);
                                crate::leanh::lean_ctor_set(v___x_4824_, 0, v___x_4829_);
                                v___x_4836_ = v___x_4824_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4837_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___x_4829_);
                                v___x_4836_ = v_reuseFailAlloc_4837_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4824_);
                            v___x_4838_ = 0usize;
                            v___x_4839_ = lean_usize_of_nat(v___x_4828_);
                            v___x_4840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_4799_, v_alts_4826_, v___x_4838_, v___x_4839_, v___x_4829_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
                            crate::leanh::lean_dec_ref(v_alts_4826_);
                            return v___x_4840_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4824_);
                        v___x_4841_ = 0usize;
                        v___x_4842_ = lean_usize_of_nat(v___x_4828_);
                        v___x_4843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_4799_, v_alts_4826_, v___x_4841_, v___x_4842_, v___x_4829_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
                        crate::leanh::lean_dec_ref(v_alts_4826_);
                        return v___x_4843_;
                    }
                }
            }
            2 => {
                return v___x_4832_;
            }
            3 => {
                return v___x_4836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(
    mut v_pu_4861_: u8,
    mut v_as_4862_: *mut crate::leanh::LeanObject,
    mut v_i_4863_: usize,
    mut v_stop_4864_: usize,
    mut v_b_4865_: *mut crate::leanh::LeanObject,
    mut v___y_4866_: *mut crate::leanh::LeanObject,
    mut v___y_4867_: *mut crate::leanh::LeanObject,
    mut v___y_4868_: *mut crate::leanh::LeanObject,
    mut v___y_4869_: *mut crate::leanh::LeanObject,
    mut v___y_4870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: usize = 0;
    let mut v___x_4877_: usize = 0;
    let mut v___x_4879_: u8 = 0;
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4879_ = lean_usize_dec_eq(v_i_4863_, v_stop_4864_);
                if v___x_4879_ == 0 {
                    v___x_4880_ = lean_array_uget_borrowed(v_as_4862_, v_i_4863_);
                    match crate::leanh::lean_obj_tag(v___x_4880_) {
                        0 => {
                            v_code_4881_ = crate::leanh::lean_ctor_get(v___x_4880_, 2);
                            crate::leanh::lean_inc_ref(v_code_4881_);
                            v___y_4873_ = v_code_4881_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_4882_ = crate::leanh::lean_ctor_get(v___x_4880_, 1);
                            crate::leanh::lean_inc_ref(v_code_4882_);
                            v___y_4873_ = v_code_4882_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_4883_ = crate::leanh::lean_ctor_get(v___x_4880_, 0);
                            crate::leanh::lean_inc_ref(v_code_4883_);
                            v___y_4873_ = v_code_4883_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_4884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4884_, 0, v_b_4865_);
                    return v___x_4884_;
                }
            }
            1 => {
                v___x_4874_ =
                    l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(
                        v_pu_4861_,
                        v___y_4873_,
                        v___y_4866_,
                        v___y_4867_,
                        v___y_4868_,
                        v___y_4869_,
                        v___y_4870_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4874_) == 0 {
                    v_a_4875_ = crate::leanh::lean_ctor_get(v___x_4874_, 0);
                    crate::leanh::lean_inc(v_a_4875_);
                    crate::leanh::lean_dec_ref_known(v___x_4874_, 1);
                    v___x_4876_ = 1usize;
                    v___x_4877_ = lean_usize_add(v_i_4863_, v___x_4876_);
                    v_i_4863_ = v___x_4877_;
                    v_b_4865_ = v_a_4875_;
                    state = 0;
                    continue;
                } else {
                    return v___x_4874_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(
    mut v_pu_4885_: *mut crate::leanh::LeanObject,
    mut v_as_4886_: *mut crate::leanh::LeanObject,
    mut v_i_4887_: *mut crate::leanh::LeanObject,
    mut v_stop_4888_: *mut crate::leanh::LeanObject,
    mut v_b_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
    mut v___y_4891_: *mut crate::leanh::LeanObject,
    mut v___y_4892_: *mut crate::leanh::LeanObject,
    mut v___y_4893_: *mut crate::leanh::LeanObject,
    mut v___y_4894_: *mut crate::leanh::LeanObject,
    mut v___y_4895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4896_: u8 = 0;
    let mut v_i_boxed_4897_: usize = 0;
    let mut v_stop_boxed_4898_: usize = 0;
    let mut v_res_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4896_ = (crate::leanh::lean_unbox(v_pu_4885_) as u8);
    v_i_boxed_4897_ = crate::leanh::lean_unbox_usize(v_i_4887_);
    crate::leanh::lean_dec(v_i_4887_);
    v_stop_boxed_4898_ = crate::leanh::lean_unbox_usize(v_stop_4888_);
    crate::leanh::lean_dec(v_stop_4888_);
    v_res_4899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_boxed_4896_, v_as_4886_, v_i_boxed_4897_, v_stop_boxed_4898_, v_b_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
    crate::leanh::lean_dec(v___y_4894_);
    crate::leanh::lean_dec_ref(v___y_4893_);
    crate::leanh::lean_dec(v___y_4892_);
    crate::leanh::lean_dec_ref(v___y_4891_);
    crate::leanh::lean_dec(v___y_4890_);
    crate::leanh::lean_dec_ref(v_as_4886_);
    return v_res_4899_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(
    mut v_pu_4900_: *mut crate::leanh::LeanObject,
    mut v_code_4901_: *mut crate::leanh::LeanObject,
    mut v_a_4902_: *mut crate::leanh::LeanObject,
    mut v_a_4903_: *mut crate::leanh::LeanObject,
    mut v_a_4904_: *mut crate::leanh::LeanObject,
    mut v_a_4905_: *mut crate::leanh::LeanObject,
    mut v_a_4906_: *mut crate::leanh::LeanObject,
    mut v_a_4907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4908_: u8 = 0;
    let mut v_res_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4908_ = (crate::leanh::lean_unbox(v_pu_4900_) as u8);
    v_res_4909_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(
        v_pu_boxed_4908_,
        v_code_4901_,
        v_a_4902_,
        v_a_4903_,
        v_a_4904_,
        v_a_4905_,
        v_a_4906_,
    );
    crate::leanh::lean_dec(v_a_4906_);
    crate::leanh::lean_dec_ref(v_a_4905_);
    crate::leanh::lean_dec(v_a_4904_);
    crate::leanh::lean_dec_ref(v_a_4903_);
    crate::leanh::lean_dec(v_a_4902_);
    return v_res_4909_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(
    mut v_f_4910_: *mut crate::leanh::LeanObject,
    mut v_v_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
    mut v___y_4915_: *mut crate::leanh::LeanObject,
    mut v___y_4916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4922_: u8 = 0;
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut v_unused_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_4911_) == 0 {
                    v_code_4918_ = crate::leanh::lean_ctor_get(v_v_4911_, 0);
                    crate::leanh::lean_inc_ref(v_code_4918_);
                    crate::leanh::lean_dec_ref_known(v_v_4911_, 1);
                    crate::leanh::lean_inc(v___y_4916_);
                    crate::leanh::lean_inc_ref(v___y_4915_);
                    crate::leanh::lean_inc(v___y_4914_);
                    crate::leanh::lean_inc_ref(v___y_4913_);
                    crate::leanh::lean_inc(v___y_4912_);
                    v___x_4919_ = crate::leanh::lean_apply_7(
                        v_f_4910_,
                        v_code_4918_,
                        v___y_4912_,
                        v___y_4913_,
                        v___y_4914_,
                        v___y_4915_,
                        v___y_4916_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4919_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_4910_);
                    v_isSharedCheck_4927_ = (!crate::leanh::lean_is_exclusive(v_v_4911_)) as u8;
                    if v_isSharedCheck_4927_ == 0 {
                        v_unused_4928_ = crate::leanh::lean_ctor_get(v_v_4911_, 0);
                        crate::leanh::lean_dec(v_unused_4928_);
                        v___x_4921_ = v_v_4911_;
                        v_isShared_4922_ = v_isSharedCheck_4927_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_4911_);
                        v___x_4921_ = crate::leanh::lean_box(0);
                        v_isShared_4922_ = v_isSharedCheck_4927_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4923_ = crate::leanh::lean_box(0);
                if v_isShared_4922_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4921_, 0);
                    crate::leanh::lean_ctor_set(v___x_4921_, 0, v___x_4923_);
                    v___x_4925_ = v___x_4921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4923_);
                    v___x_4925_ = v_reuseFailAlloc_4926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(
    mut v_f_4929_: *mut crate::leanh::LeanObject,
    mut v_v_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4937_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_4929_, v_v_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
    crate::leanh::lean_dec(v___y_4935_);
    crate::leanh::lean_dec_ref(v___y_4934_);
    crate::leanh::lean_dec(v___y_4933_);
    crate::leanh::lean_dec_ref(v___y_4932_);
    crate::leanh::lean_dec(v___y_4931_);
    return v_res_4937_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(
    mut v_pu_4938_: u8,
    mut v_f_4939_: *mut crate::leanh::LeanObject,
    mut v_v_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
    mut v___y_4943_: *mut crate::leanh::LeanObject,
    mut v___y_4944_: *mut crate::leanh::LeanObject,
    mut v___y_4945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4947_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_4939_, v_v_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
    return v___x_4947_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(
    mut v_pu_4948_: *mut crate::leanh::LeanObject,
    mut v_f_4949_: *mut crate::leanh::LeanObject,
    mut v_v_4950_: *mut crate::leanh::LeanObject,
    mut v___y_4951_: *mut crate::leanh::LeanObject,
    mut v___y_4952_: *mut crate::leanh::LeanObject,
    mut v___y_4953_: *mut crate::leanh::LeanObject,
    mut v___y_4954_: *mut crate::leanh::LeanObject,
    mut v___y_4955_: *mut crate::leanh::LeanObject,
    mut v___y_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4957_: u8 = 0;
    let mut v_res_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4957_ = (crate::leanh::lean_unbox(v_pu_4948_) as u8);
    v_res_4958_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_boxed_4957_, v_f_4949_, v_v_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
    crate::leanh::lean_dec(v___y_4955_);
    crate::leanh::lean_dec_ref(v___y_4954_);
    crate::leanh::lean_dec(v___y_4953_);
    crate::leanh::lean_dec_ref(v___y_4952_);
    crate::leanh::lean_dec(v___y_4951_);
    return v_res_4958_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(
    mut v_pu_4959_: u8,
    mut v_as_4960_: *mut crate::leanh::LeanObject,
    mut v_i_4961_: usize,
    mut v_stop_4962_: usize,
    mut v_b_4963_: *mut crate::leanh::LeanObject,
    mut v___y_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
    mut v___y_4966_: *mut crate::leanh::LeanObject,
    mut v___y_4967_: *mut crate::leanh::LeanObject,
    mut v___y_4968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4970_: u8 = 0;
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: usize = 0;
    let mut v___x_4978_: usize = 0;
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4970_ = lean_usize_dec_eq(v_i_4961_, v_stop_4962_);
                if v___x_4970_ == 0 {
                    v___x_4971_ = lean_array_uget_borrowed(v_as_4960_, v_i_4961_);
                    v_value_4972_ = crate::leanh::lean_ctor_get(v___x_4971_, 1);
                    v___x_4973_ = crate::leanh::lean_box((v_pu_4959_) as usize);
                    v___x_4974_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___x_4974_, 0, v___x_4973_);
                    crate::leanh::lean_inc_ref(v_value_4972_);
                    v___x_4975_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v___x_4974_, v_value_4972_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
                    if crate::leanh::lean_obj_tag(v___x_4975_) == 0 {
                        v_a_4976_ = crate::leanh::lean_ctor_get(v___x_4975_, 0);
                        crate::leanh::lean_inc(v_a_4976_);
                        crate::leanh::lean_dec_ref_known(v___x_4975_, 1);
                        v___x_4977_ = 1usize;
                        v___x_4978_ = lean_usize_add(v_i_4961_, v___x_4977_);
                        v_i_4961_ = v___x_4978_;
                        v_b_4963_ = v_a_4976_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4975_;
                    }
                } else {
                    v___x_4980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4980_, 0, v_b_4963_);
                    return v___x_4980_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(
    mut v_pu_4981_: *mut crate::leanh::LeanObject,
    mut v_as_4982_: *mut crate::leanh::LeanObject,
    mut v_i_4983_: *mut crate::leanh::LeanObject,
    mut v_stop_4984_: *mut crate::leanh::LeanObject,
    mut v_b_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
    mut v___y_4988_: *mut crate::leanh::LeanObject,
    mut v___y_4989_: *mut crate::leanh::LeanObject,
    mut v___y_4990_: *mut crate::leanh::LeanObject,
    mut v___y_4991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4992_: u8 = 0;
    let mut v_i_boxed_4993_: usize = 0;
    let mut v_stop_boxed_4994_: usize = 0;
    let mut v_res_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4992_ = (crate::leanh::lean_unbox(v_pu_4981_) as u8);
    v_i_boxed_4993_ = crate::leanh::lean_unbox_usize(v_i_4983_);
    crate::leanh::lean_dec(v_i_4983_);
    v_stop_boxed_4994_ = crate::leanh::lean_unbox_usize(v_stop_4984_);
    crate::leanh::lean_dec(v_stop_4984_);
    v_res_4995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_boxed_4992_, v_as_4982_, v_i_boxed_4993_, v_stop_boxed_4994_, v_b_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
    crate::leanh::lean_dec(v___y_4990_);
    crate::leanh::lean_dec_ref(v___y_4989_);
    crate::leanh::lean_dec(v___y_4988_);
    crate::leanh::lean_dec_ref(v___y_4987_);
    crate::leanh::lean_dec(v___y_4986_);
    crate::leanh::lean_dec_ref(v_as_4982_);
    return v_res_4995_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(
    mut v_pu_4996_: u8,
    mut v_decls_4997_: *mut crate::leanh::LeanObject,
    mut v_a_4998_: *mut crate::leanh::LeanObject,
    mut v_a_4999_: *mut crate::leanh::LeanObject,
    mut v_a_5000_: *mut crate::leanh::LeanObject,
    mut v_a_5001_: *mut crate::leanh::LeanObject,
    mut v_a_5002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: u8 = 0;
    v___x_5004_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5005_ = lean_array_get_size(v_decls_4997_);
    v___x_5006_ = crate::leanh::lean_box(0);
    v___x_5007_ = lean_nat_dec_lt(v___x_5004_, v___x_5005_);
    if v___x_5007_ == 0 {
        let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5008_, 0, v___x_5006_);
        return v___x_5008_;
    } else {
        let mut v___x_5009_: u8 = 0;
        v___x_5009_ = lean_nat_dec_le(v___x_5005_, v___x_5005_);
        if v___x_5009_ == 0 {
            if v___x_5007_ == 0 {
                let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5010_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5010_, 0, v___x_5006_);
                return v___x_5010_;
            } else {
                let mut v___x_5011_: usize = 0;
                let mut v___x_5012_: usize = 0;
                let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5011_ = 0usize;
                v___x_5012_ = lean_usize_of_nat(v___x_5005_);
                v___x_5013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_4996_, v_decls_4997_, v___x_5011_, v___x_5012_, v___x_5006_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
                return v___x_5013_;
            }
        } else {
            let mut v___x_5014_: usize = 0;
            let mut v___x_5015_: usize = 0;
            let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5014_ = 0usize;
            v___x_5015_ = lean_usize_of_nat(v___x_5005_);
            v___x_5016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_4996_, v_decls_4997_, v___x_5014_, v___x_5015_, v___x_5006_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
            return v___x_5016_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(
    mut v_pu_5017_: *mut crate::leanh::LeanObject,
    mut v_decls_5018_: *mut crate::leanh::LeanObject,
    mut v_a_5019_: *mut crate::leanh::LeanObject,
    mut v_a_5020_: *mut crate::leanh::LeanObject,
    mut v_a_5021_: *mut crate::leanh::LeanObject,
    mut v_a_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_a_5024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5025_: u8 = 0;
    let mut v_res_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5025_ = (crate::leanh::lean_unbox(v_pu_5017_) as u8);
    v_res_5026_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(
        v_pu_boxed_5025_,
        v_decls_5018_,
        v_a_5019_,
        v_a_5020_,
        v_a_5021_,
        v_a_5022_,
        v_a_5023_,
    );
    crate::leanh::lean_dec(v_a_5023_);
    crate::leanh::lean_dec_ref(v_a_5022_);
    crate::leanh::lean_dec(v_a_5021_);
    crate::leanh::lean_dec_ref(v_a_5020_);
    crate::leanh::lean_dec(v_a_5019_);
    crate::leanh::lean_dec_ref(v_decls_5018_);
    return v_res_5026_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_getJps(
    mut v_pu_5029_: u8,
    mut v_decls_5030_: *mut crate::leanh::LeanObject,
    mut v_a_5031_: *mut crate::leanh::LeanObject,
    mut v_a_5032_: *mut crate::leanh::LeanObject,
    mut v_a_5033_: *mut crate::leanh::LeanObject,
    mut v_a_5034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5041_: u8 = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5046_: u8 = 0;
    let mut v_unused_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5036_ = l_Lean_Compiler_LCNF_Probe_getJps___closed__0;
                v___x_5037_ = lean_st_mk_ref(v___x_5036_);
                v___x_5038_ =
                    l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(
                        v_pu_5029_,
                        v_decls_5030_,
                        v___x_5037_,
                        v_a_5031_,
                        v_a_5032_,
                        v_a_5033_,
                        v_a_5034_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5038_) == 0 {
                    v_isSharedCheck_5046_ = (!crate::leanh::lean_is_exclusive(v___x_5038_)) as u8;
                    if v_isSharedCheck_5046_ == 0 {
                        v_unused_5047_ = crate::leanh::lean_ctor_get(v___x_5038_, 0);
                        crate::leanh::lean_dec(v_unused_5047_);
                        v___x_5040_ = v___x_5038_;
                        v_isShared_5041_ = v_isSharedCheck_5046_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5038_);
                        v___x_5040_ = crate::leanh::lean_box(0);
                        v_isShared_5041_ = v_isSharedCheck_5046_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5037_);
                    v_a_5048_ = crate::leanh::lean_ctor_get(v___x_5038_, 0);
                    v_isSharedCheck_5055_ = (!crate::leanh::lean_is_exclusive(v___x_5038_)) as u8;
                    if v_isSharedCheck_5055_ == 0 {
                        v___x_5050_ = v___x_5038_;
                        v_isShared_5051_ = v_isSharedCheck_5055_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5048_);
                        crate::leanh::lean_dec(v___x_5038_);
                        v___x_5050_ = crate::leanh::lean_box(0);
                        v_isShared_5051_ = v_isSharedCheck_5055_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5042_ = lean_st_ref_get(v___x_5037_);
                crate::leanh::lean_dec(v___x_5037_);
                if v_isShared_5041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5040_, 0, v___x_5042_);
                    v___x_5044_ = v___x_5040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5042_);
                    v___x_5044_ = v_reuseFailAlloc_5045_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5044_;
            }
            3 => {
                if v_isShared_5051_ == 0 {
                    v___x_5053_ = v___x_5050_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
                    v___x_5053_ = v_reuseFailAlloc_5054_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_getJps___boxed(
    mut v_pu_5056_: *mut crate::leanh::LeanObject,
    mut v_decls_5057_: *mut crate::leanh::LeanObject,
    mut v_a_5058_: *mut crate::leanh::LeanObject,
    mut v_a_5059_: *mut crate::leanh::LeanObject,
    mut v_a_5060_: *mut crate::leanh::LeanObject,
    mut v_a_5061_: *mut crate::leanh::LeanObject,
    mut v_a_5062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5063_: u8 = 0;
    let mut v_res_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5063_ = (crate::leanh::lean_unbox(v_pu_5056_) as u8);
    v_res_5064_ = l_Lean_Compiler_LCNF_Probe_getJps(
        v_pu_boxed_5063_,
        v_decls_5057_,
        v_a_5058_,
        v_a_5059_,
        v_a_5060_,
        v_a_5061_,
    );
    crate::leanh::lean_dec(v_a_5061_);
    crate::leanh::lean_dec_ref(v_a_5060_);
    crate::leanh::lean_dec(v_a_5059_);
    crate::leanh::lean_dec_ref(v_a_5058_);
    crate::leanh::lean_dec_ref(v_decls_5057_);
    return v_res_5064_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(
    mut v_pu_5065_: u8,
    mut v_f_5066_: *mut crate::leanh::LeanObject,
    mut v_a_5067_: *mut crate::leanh::LeanObject,
    mut v_a_5068_: *mut crate::leanh::LeanObject,
    mut v_a_5069_: *mut crate::leanh::LeanObject,
    mut v_a_5070_: *mut crate::leanh::LeanObject,
    mut v_a_5071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: u8 = 0;
    let mut v_decl_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: u8 = 0;
    let mut v_decl_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: u8 = 0;
    let mut v_cases_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5096_: u8 = 0;
    let mut v_alts_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: u8 = 0;
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: usize = 0;
    let mut v___x_5110_: usize = 0;
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5112_: u8 = 0;
    let mut v_k_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_5067_) {
                0 => {
                    v_decl_5073_ = crate::leanh::lean_ctor_get(v_a_5067_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5073_);
                    v_k_5074_ = crate::leanh::lean_ctor_get(v_a_5067_, 1);
                    crate::leanh::lean_inc_ref(v_k_5074_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 2);
                    crate::leanh::lean_inc_ref(v_f_5066_);
                    crate::leanh::lean_inc(v_a_5071_);
                    crate::leanh::lean_inc_ref(v_a_5070_);
                    crate::leanh::lean_inc(v_a_5069_);
                    crate::leanh::lean_inc_ref(v_a_5068_);
                    v___x_5075_ = crate::leanh::lean_apply_6(
                        v_f_5066_,
                        v_decl_5073_,
                        v_a_5068_,
                        v_a_5069_,
                        v_a_5070_,
                        v_a_5071_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5075_) == 0 {
                        v_a_5076_ = crate::leanh::lean_ctor_get(v___x_5075_, 0);
                        crate::leanh::lean_inc(v_a_5076_);
                        v___x_5077_ = (crate::leanh::lean_unbox(v_a_5076_) as u8);
                        crate::leanh::lean_dec(v_a_5076_);
                        if v___x_5077_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5075_, 1);
                            v_a_5067_ = v_k_5074_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5074_);
                            crate::leanh::lean_dec_ref(v_f_5066_);
                            return v___x_5075_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5074_);
                        crate::leanh::lean_dec_ref(v_f_5066_);
                        return v___x_5075_;
                    }
                }
                1 => {
                    v_decl_5079_ = crate::leanh::lean_ctor_get(v_a_5067_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5079_);
                    v_k_5080_ = crate::leanh::lean_ctor_get(v_a_5067_, 1);
                    crate::leanh::lean_inc_ref(v_k_5080_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 2);
                    v_value_5081_ = crate::leanh::lean_ctor_get(v_decl_5079_, 4);
                    crate::leanh::lean_inc_ref(v_value_5081_);
                    crate::leanh::lean_dec_ref(v_decl_5079_);
                    crate::leanh::lean_inc_ref(v_f_5066_);
                    v___x_5082_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_5065_, v_f_5066_, v_value_5081_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
                    if crate::leanh::lean_obj_tag(v___x_5082_) == 0 {
                        v_a_5083_ = crate::leanh::lean_ctor_get(v___x_5082_, 0);
                        crate::leanh::lean_inc(v_a_5083_);
                        v___x_5084_ = (crate::leanh::lean_unbox(v_a_5083_) as u8);
                        crate::leanh::lean_dec(v_a_5083_);
                        if v___x_5084_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5082_, 1);
                            v_a_5067_ = v_k_5080_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5080_);
                            crate::leanh::lean_dec_ref(v_f_5066_);
                            return v___x_5082_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5080_);
                        crate::leanh::lean_dec_ref(v_f_5066_);
                        return v___x_5082_;
                    }
                }
                2 => {
                    v_decl_5086_ = crate::leanh::lean_ctor_get(v_a_5067_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5086_);
                    v_k_5087_ = crate::leanh::lean_ctor_get(v_a_5067_, 1);
                    crate::leanh::lean_inc_ref(v_k_5087_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 2);
                    v_value_5088_ = crate::leanh::lean_ctor_get(v_decl_5086_, 4);
                    crate::leanh::lean_inc_ref(v_value_5088_);
                    crate::leanh::lean_dec_ref(v_decl_5086_);
                    crate::leanh::lean_inc_ref(v_f_5066_);
                    v___x_5089_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_5065_, v_f_5066_, v_value_5088_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
                    if crate::leanh::lean_obj_tag(v___x_5089_) == 0 {
                        v_a_5090_ = crate::leanh::lean_ctor_get(v___x_5089_, 0);
                        crate::leanh::lean_inc(v_a_5090_);
                        v___x_5091_ = (crate::leanh::lean_unbox(v_a_5090_) as u8);
                        crate::leanh::lean_dec(v_a_5090_);
                        if v___x_5091_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5089_, 1);
                            v_a_5067_ = v_k_5087_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5087_);
                            crate::leanh::lean_dec_ref(v_f_5066_);
                            return v___x_5089_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5087_);
                        crate::leanh::lean_dec_ref(v_f_5066_);
                        return v___x_5089_;
                    }
                }
                4 => {
                    v_cases_5093_ = crate::leanh::lean_ctor_get(v_a_5067_, 0);
                    v_isSharedCheck_5112_ = (!crate::leanh::lean_is_exclusive(v_a_5067_)) as u8;
                    if v_isSharedCheck_5112_ == 0 {
                        v___x_5095_ = v_a_5067_;
                        v_isShared_5096_ = v_isSharedCheck_5112_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_5093_);
                        crate::leanh::lean_dec(v_a_5067_);
                        v___x_5095_ = crate::leanh::lean_box(0);
                        v_isShared_5096_ = v_isSharedCheck_5112_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_k_5113_ = crate::leanh::lean_ctor_get(v_a_5067_, 3);
                    crate::leanh::lean_inc_ref(v_k_5113_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 4);
                    v_a_5067_ = v_k_5113_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_5115_ = crate::leanh::lean_ctor_get(v_a_5067_, 3);
                    crate::leanh::lean_inc_ref(v_k_5115_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 4);
                    v_a_5067_ = v_k_5115_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_5117_ = crate::leanh::lean_ctor_get(v_a_5067_, 5);
                    crate::leanh::lean_inc_ref(v_k_5117_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 6);
                    v_a_5067_ = v_k_5117_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_5119_ = crate::leanh::lean_ctor_get(v_a_5067_, 2);
                    crate::leanh::lean_inc_ref(v_k_5119_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 3);
                    v_a_5067_ = v_k_5119_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_5121_ = crate::leanh::lean_ctor_get(v_a_5067_, 2);
                    crate::leanh::lean_inc_ref(v_k_5121_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 3);
                    v_a_5067_ = v_k_5121_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_5123_ = crate::leanh::lean_ctor_get(v_a_5067_, 3);
                    crate::leanh::lean_inc_ref(v_k_5123_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 4);
                    v_a_5067_ = v_k_5123_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_5125_ = crate::leanh::lean_ctor_get(v_a_5067_, 1);
                    crate::leanh::lean_inc_ref(v_k_5125_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 2);
                    v_a_5067_ = v_k_5125_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_5067_);
                    crate::leanh::lean_dec_ref(v_f_5066_);
                    v___x_5127_ = 0;
                    v___x_5128_ = crate::leanh::lean_box((v___x_5127_) as usize);
                    v___x_5129_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5129_, 0, v___x_5128_);
                    return v___x_5129_;
                }
            },
            1 => {
                v_alts_5097_ = crate::leanh::lean_ctor_get(v_cases_5093_, 3);
                crate::leanh::lean_inc_ref(v_alts_5097_);
                crate::leanh::lean_dec_ref(v_cases_5093_);
                v___x_5098_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5099_ = lean_array_get_size(v_alts_5097_);
                v___x_5100_ = lean_nat_dec_lt(v___x_5098_, v___x_5099_);
                if v___x_5100_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_5097_);
                    crate::leanh::lean_dec_ref(v_f_5066_);
                    v___x_5101_ = crate::leanh::lean_box((v___x_5100_) as usize);
                    if v_isShared_5096_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5095_, 0);
                        crate::leanh::lean_ctor_set(v___x_5095_, 0, v___x_5101_);
                        v___x_5103_ = v___x_5095_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5104_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5101_);
                        v___x_5103_ = v_reuseFailAlloc_5104_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_5100_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_5097_);
                        crate::leanh::lean_dec_ref(v_f_5066_);
                        v___x_5105_ = crate::leanh::lean_box((v___x_5100_) as usize);
                        if v_isShared_5096_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5095_, 0);
                            crate::leanh::lean_ctor_set(v___x_5095_, 0, v___x_5105_);
                            v___x_5107_ = v___x_5095_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5108_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5105_);
                            v___x_5107_ = v_reuseFailAlloc_5108_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5095_);
                        v___x_5109_ = 0usize;
                        v___x_5110_ = lean_usize_of_nat(v___x_5099_);
                        v___x_5111_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_5065_, v_f_5066_, v_alts_5097_, v___x_5109_, v___x_5110_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
                        crate::leanh::lean_dec_ref(v_alts_5097_);
                        return v___x_5111_;
                    }
                }
            }
            2 => {
                return v___x_5103_;
            }
            3 => {
                return v___x_5107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(
    mut v_pu_5130_: u8,
    mut v_f_5131_: *mut crate::leanh::LeanObject,
    mut v_as_5132_: *mut crate::leanh::LeanObject,
    mut v_i_5133_: usize,
    mut v_stop_5134_: usize,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5140_: u8 = 0;
    let mut v___x_5141_: u8 = 0;
    let mut v___y_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5148_: u8 = 0;
    let mut v___x_5149_: u8 = 0;
    let mut v___x_5150_: usize = 0;
    let mut v___x_5151_: usize = 0;
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5157_: u8 = 0;
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: u8 = 0;
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5140_ = lean_usize_dec_eq(v_i_5133_, v_stop_5134_);
                if v___x_5140_ == 0 {
                    v___x_5141_ = 1;
                    v___x_5158_ = lean_array_uget_borrowed(v_as_5132_, v_i_5133_);
                    match crate::leanh::lean_obj_tag(v___x_5158_) {
                        0 => {
                            v_code_5159_ = crate::leanh::lean_ctor_get(v___x_5158_, 2);
                            crate::leanh::lean_inc_ref(v_code_5159_);
                            v___y_5143_ = v_code_5159_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_5160_ = crate::leanh::lean_ctor_get(v___x_5158_, 1);
                            crate::leanh::lean_inc_ref(v_code_5160_);
                            v___y_5143_ = v_code_5160_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_5161_ = crate::leanh::lean_ctor_get(v___x_5158_, 0);
                            crate::leanh::lean_inc_ref(v_code_5161_);
                            v___y_5143_ = v_code_5161_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5131_);
                    v___x_5162_ = 0;
                    v___x_5163_ = crate::leanh::lean_box((v___x_5162_) as usize);
                    v___x_5164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5164_, 0, v___x_5163_);
                    return v___x_5164_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_5131_);
                v___x_5144_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_5130_, v_f_5131_, v___y_5143_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
                if crate::leanh::lean_obj_tag(v___x_5144_) == 0 {
                    v_a_5145_ = crate::leanh::lean_ctor_get(v___x_5144_, 0);
                    v_isSharedCheck_5157_ = (!crate::leanh::lean_is_exclusive(v___x_5144_)) as u8;
                    if v_isSharedCheck_5157_ == 0 {
                        v___x_5147_ = v___x_5144_;
                        v_isShared_5148_ = v_isSharedCheck_5157_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5145_);
                        crate::leanh::lean_dec(v___x_5144_);
                        v___x_5147_ = crate::leanh::lean_box(0);
                        v_isShared_5148_ = v_isSharedCheck_5157_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5131_);
                    return v___x_5144_;
                }
            }
            2 => {
                v___x_5149_ = (crate::leanh::lean_unbox(v_a_5145_) as u8);
                crate::leanh::lean_dec(v_a_5145_);
                if v___x_5149_ == 0 {
                    crate::leanh::lean_del_object(v___x_5147_);
                    v___x_5150_ = 1usize;
                    v___x_5151_ = lean_usize_add(v_i_5133_, v___x_5150_);
                    v_i_5133_ = v___x_5151_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_5131_);
                    v___x_5153_ = crate::leanh::lean_box((v___x_5141_) as usize);
                    if v_isShared_5148_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5147_, 0, v___x_5153_);
                        v___x_5155_ = v___x_5147_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5153_);
                        v___x_5155_ = v_reuseFailAlloc_5156_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(
    mut v_pu_5165_: *mut crate::leanh::LeanObject,
    mut v_f_5166_: *mut crate::leanh::LeanObject,
    mut v_as_5167_: *mut crate::leanh::LeanObject,
    mut v_i_5168_: *mut crate::leanh::LeanObject,
    mut v_stop_5169_: *mut crate::leanh::LeanObject,
    mut v___y_5170_: *mut crate::leanh::LeanObject,
    mut v___y_5171_: *mut crate::leanh::LeanObject,
    mut v___y_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5175_: u8 = 0;
    let mut v_i_boxed_5176_: usize = 0;
    let mut v_stop_boxed_5177_: usize = 0;
    let mut v_res_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5175_ = (crate::leanh::lean_unbox(v_pu_5165_) as u8);
    v_i_boxed_5176_ = crate::leanh::lean_unbox_usize(v_i_5168_);
    crate::leanh::lean_dec(v_i_5168_);
    v_stop_boxed_5177_ = crate::leanh::lean_unbox_usize(v_stop_5169_);
    crate::leanh::lean_dec(v_stop_5169_);
    v_res_5178_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_boxed_5175_, v_f_5166_, v_as_5167_, v_i_boxed_5176_, v_stop_boxed_5177_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
    crate::leanh::lean_dec(v___y_5173_);
    crate::leanh::lean_dec_ref(v___y_5172_);
    crate::leanh::lean_dec(v___y_5171_);
    crate::leanh::lean_dec_ref(v___y_5170_);
    crate::leanh::lean_dec_ref(v_as_5167_);
    return v_res_5178_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(
    mut v_pu_5179_: *mut crate::leanh::LeanObject,
    mut v_f_5180_: *mut crate::leanh::LeanObject,
    mut v_a_5181_: *mut crate::leanh::LeanObject,
    mut v_a_5182_: *mut crate::leanh::LeanObject,
    mut v_a_5183_: *mut crate::leanh::LeanObject,
    mut v_a_5184_: *mut crate::leanh::LeanObject,
    mut v_a_5185_: *mut crate::leanh::LeanObject,
    mut v_a_5186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5187_: u8 = 0;
    let mut v_res_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5187_ = (crate::leanh::lean_unbox(v_pu_5179_) as u8);
    v_res_5188_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(
        v_pu_boxed_5187_,
        v_f_5180_,
        v_a_5181_,
        v_a_5182_,
        v_a_5183_,
        v_a_5184_,
        v_a_5185_,
    );
    crate::leanh::lean_dec(v_a_5185_);
    crate::leanh::lean_dec_ref(v_a_5184_);
    crate::leanh::lean_dec(v_a_5183_);
    crate::leanh::lean_dec_ref(v_a_5182_);
    return v_res_5188_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(
    mut v_v_5189_: *mut crate::leanh::LeanObject,
    mut v_f_5190_: *mut crate::leanh::LeanObject,
    mut v___y_5191_: *mut crate::leanh::LeanObject,
    mut v___y_5192_: *mut crate::leanh::LeanObject,
    mut v___y_5193_: *mut crate::leanh::LeanObject,
    mut v___y_5194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5200_: u8 = 0;
    let mut v___x_5201_: u8 = 0;
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5206_: u8 = 0;
    let mut v_unused_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_5189_) == 0 {
                    v_code_5196_ = crate::leanh::lean_ctor_get(v_v_5189_, 0);
                    crate::leanh::lean_inc_ref(v_code_5196_);
                    crate::leanh::lean_dec_ref_known(v_v_5189_, 1);
                    crate::leanh::lean_inc(v___y_5194_);
                    crate::leanh::lean_inc_ref(v___y_5193_);
                    crate::leanh::lean_inc(v___y_5192_);
                    crate::leanh::lean_inc_ref(v___y_5191_);
                    v___x_5197_ = crate::leanh::lean_apply_6(
                        v_f_5190_,
                        v_code_5196_,
                        v___y_5191_,
                        v___y_5192_,
                        v___y_5193_,
                        v___y_5194_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5197_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_5190_);
                    v_isSharedCheck_5206_ = (!crate::leanh::lean_is_exclusive(v_v_5189_)) as u8;
                    if v_isSharedCheck_5206_ == 0 {
                        v_unused_5207_ = crate::leanh::lean_ctor_get(v_v_5189_, 0);
                        crate::leanh::lean_dec(v_unused_5207_);
                        v___x_5199_ = v_v_5189_;
                        v_isShared_5200_ = v_isSharedCheck_5206_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_5189_);
                        v___x_5199_ = crate::leanh::lean_box(0);
                        v_isShared_5200_ = v_isSharedCheck_5206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5201_ = 0;
                v___x_5202_ = crate::leanh::lean_box((v___x_5201_) as usize);
                if v_isShared_5200_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5199_, 0);
                    crate::leanh::lean_ctor_set(v___x_5199_, 0, v___x_5202_);
                    v___x_5204_ = v___x_5199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5205_, 0, v___x_5202_);
                    v___x_5204_ = v_reuseFailAlloc_5205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(
    mut v_v_5208_: *mut crate::leanh::LeanObject,
    mut v_f_5209_: *mut crate::leanh::LeanObject,
    mut v___y_5210_: *mut crate::leanh::LeanObject,
    mut v___y_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5215_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_5208_, v_f_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
    crate::leanh::lean_dec(v___y_5213_);
    crate::leanh::lean_dec_ref(v___y_5212_);
    crate::leanh::lean_dec(v___y_5211_);
    crate::leanh::lean_dec_ref(v___y_5210_);
    return v_res_5215_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(
    mut v_pu_5216_: u8,
    mut v_v_5217_: *mut crate::leanh::LeanObject,
    mut v_f_5218_: *mut crate::leanh::LeanObject,
    mut v___y_5219_: *mut crate::leanh::LeanObject,
    mut v___y_5220_: *mut crate::leanh::LeanObject,
    mut v___y_5221_: *mut crate::leanh::LeanObject,
    mut v___y_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5224_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_5217_, v_f_5218_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
    return v___x_5224_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(
    mut v_pu_5225_: *mut crate::leanh::LeanObject,
    mut v_v_5226_: *mut crate::leanh::LeanObject,
    mut v_f_5227_: *mut crate::leanh::LeanObject,
    mut v___y_5228_: *mut crate::leanh::LeanObject,
    mut v___y_5229_: *mut crate::leanh::LeanObject,
    mut v___y_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5233_: u8 = 0;
    let mut v_res_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5233_ = (crate::leanh::lean_unbox(v_pu_5225_) as u8);
    v_res_5234_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_boxed_5233_, v_v_5226_, v_f_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_);
    crate::leanh::lean_dec(v___y_5231_);
    crate::leanh::lean_dec_ref(v___y_5230_);
    crate::leanh::lean_dec(v___y_5229_);
    crate::leanh::lean_dec_ref(v___y_5228_);
    return v_res_5234_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(
    mut v_pu_5235_: u8,
    mut v_f_5236_: *mut crate::leanh::LeanObject,
    mut v_as_5237_: *mut crate::leanh::LeanObject,
    mut v_i_5238_: usize,
    mut v_stop_5239_: usize,
    mut v_b_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
    mut v___y_5243_: *mut crate::leanh::LeanObject,
    mut v___y_5244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5246_: u8 = 0;
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: usize = 0;
    let mut v___x_5256_: usize = 0;
    let mut v___x_5258_: u8 = 0;
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5263_: u8 = 0;
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5246_ = lean_usize_dec_eq(v_i_5238_, v_stop_5239_);
                if v___x_5246_ == 0 {
                    v___x_5247_ = lean_array_uget_borrowed(v_as_5237_, v_i_5238_);
                    v_value_5248_ = crate::leanh::lean_ctor_get(v___x_5247_, 1);
                    v___x_5249_ = crate::leanh::lean_box((v_pu_5235_) as usize);
                    crate::leanh::lean_inc_ref(v_f_5236_);
                    v___x_5250_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_5250_, 0, v___x_5249_);
                    crate::leanh::lean_closure_set(v___x_5250_, 1, v_f_5236_);
                    crate::leanh::lean_inc_ref(v_value_5248_);
                    v___x_5251_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_5248_, v___x_5250_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
                    if crate::leanh::lean_obj_tag(v___x_5251_) == 0 {
                        v_a_5252_ = crate::leanh::lean_ctor_get(v___x_5251_, 0);
                        crate::leanh::lean_inc(v_a_5252_);
                        crate::leanh::lean_dec_ref_known(v___x_5251_, 1);
                        v___x_5258_ = (crate::leanh::lean_unbox(v_a_5252_) as u8);
                        crate::leanh::lean_dec(v_a_5252_);
                        if v___x_5258_ == 0 {
                            v_a_5254_ = v_b_5240_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_5247_);
                            v___x_5259_ = lean_array_push(v_b_5240_, v___x_5247_);
                            v_a_5254_ = v___x_5259_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5240_);
                        crate::leanh::lean_dec_ref(v_f_5236_);
                        v_a_5260_ = crate::leanh::lean_ctor_get(v___x_5251_, 0);
                        v_isSharedCheck_5267_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5251_)) as u8;
                        if v_isSharedCheck_5267_ == 0 {
                            v___x_5262_ = v___x_5251_;
                            v_isShared_5263_ = v_isSharedCheck_5267_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5260_);
                            crate::leanh::lean_dec(v___x_5251_);
                            v___x_5262_ = crate::leanh::lean_box(0);
                            v_isShared_5263_ = v_isSharedCheck_5267_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5236_);
                    v___x_5268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5268_, 0, v_b_5240_);
                    return v___x_5268_;
                }
            }
            1 => {
                v___x_5255_ = 1usize;
                v___x_5256_ = lean_usize_add(v_i_5238_, v___x_5255_);
                v_i_5238_ = v___x_5256_;
                v_b_5240_ = v_a_5254_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5263_ == 0 {
                    v___x_5265_ = v___x_5262_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5266_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
                    v___x_5265_ = v_reuseFailAlloc_5266_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5265_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(
    mut v_pu_5269_: *mut crate::leanh::LeanObject,
    mut v_f_5270_: *mut crate::leanh::LeanObject,
    mut v_as_5271_: *mut crate::leanh::LeanObject,
    mut v_i_5272_: *mut crate::leanh::LeanObject,
    mut v_stop_5273_: *mut crate::leanh::LeanObject,
    mut v_b_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5280_: u8 = 0;
    let mut v_i_boxed_5281_: usize = 0;
    let mut v_stop_boxed_5282_: usize = 0;
    let mut v_res_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5280_ = (crate::leanh::lean_unbox(v_pu_5269_) as u8);
    v_i_boxed_5281_ = crate::leanh::lean_unbox_usize(v_i_5272_);
    crate::leanh::lean_dec(v_i_5272_);
    v_stop_boxed_5282_ = crate::leanh::lean_unbox_usize(v_stop_5273_);
    crate::leanh::lean_dec(v_stop_5273_);
    v_res_5283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_boxed_5280_, v_f_5270_, v_as_5271_, v_i_boxed_5281_, v_stop_boxed_5282_, v_b_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
    crate::leanh::lean_dec(v___y_5278_);
    crate::leanh::lean_dec_ref(v___y_5277_);
    crate::leanh::lean_dec(v___y_5276_);
    crate::leanh::lean_dec_ref(v___y_5275_);
    crate::leanh::lean_dec_ref(v_as_5271_);
    return v_res_5283_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByLet(
    mut v_pu_5286_: u8,
    mut v_f_5287_: *mut crate::leanh::LeanObject,
    mut v_a_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v_a_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
    mut v_a_5292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: u8 = 0;
    v___x_5294_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5295_ = lean_array_get_size(v_a_5288_);
    v___x_5296_ = l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0;
    v___x_5297_ = lean_nat_dec_lt(v___x_5294_, v___x_5295_);
    if v___x_5297_ == 0 {
        let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_5287_);
        v___x_5298_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5298_, 0, v___x_5296_);
        return v___x_5298_;
    } else {
        let mut v___x_5299_: u8 = 0;
        v___x_5299_ = lean_nat_dec_le(v___x_5295_, v___x_5295_);
        if v___x_5299_ == 0 {
            if v___x_5297_ == 0 {
                let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_5287_);
                v___x_5300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5300_, 0, v___x_5296_);
                return v___x_5300_;
            } else {
                let mut v___x_5301_: usize = 0;
                let mut v___x_5302_: usize = 0;
                let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5301_ = 0usize;
                v___x_5302_ = lean_usize_of_nat(v___x_5295_);
                v___x_5303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_5286_, v_f_5287_, v_a_5288_, v___x_5301_, v___x_5302_, v___x_5296_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
                return v___x_5303_;
            }
        } else {
            let mut v___x_5304_: usize = 0;
            let mut v___x_5305_: usize = 0;
            let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5304_ = 0usize;
            v___x_5305_ = lean_usize_of_nat(v___x_5295_);
            v___x_5306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_5286_, v_f_5287_, v_a_5288_, v___x_5304_, v___x_5305_, v___x_5296_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
            return v___x_5306_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(
    mut v_pu_5307_: *mut crate::leanh::LeanObject,
    mut v_f_5308_: *mut crate::leanh::LeanObject,
    mut v_a_5309_: *mut crate::leanh::LeanObject,
    mut v_a_5310_: *mut crate::leanh::LeanObject,
    mut v_a_5311_: *mut crate::leanh::LeanObject,
    mut v_a_5312_: *mut crate::leanh::LeanObject,
    mut v_a_5313_: *mut crate::leanh::LeanObject,
    mut v_a_5314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5315_: u8 = 0;
    let mut v_res_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5315_ = (crate::leanh::lean_unbox(v_pu_5307_) as u8);
    v_res_5316_ = l_Lean_Compiler_LCNF_Probe_filterByLet(
        v_pu_boxed_5315_,
        v_f_5308_,
        v_a_5309_,
        v_a_5310_,
        v_a_5311_,
        v_a_5312_,
        v_a_5313_,
    );
    crate::leanh::lean_dec(v_a_5313_);
    crate::leanh::lean_dec_ref(v_a_5312_);
    crate::leanh::lean_dec(v_a_5311_);
    crate::leanh::lean_dec_ref(v_a_5310_);
    crate::leanh::lean_dec_ref(v_a_5309_);
    return v_res_5316_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(
    mut v_pu_5317_: u8,
    mut v_f_5318_: *mut crate::leanh::LeanObject,
    mut v_a_5319_: *mut crate::leanh::LeanObject,
    mut v_a_5320_: *mut crate::leanh::LeanObject,
    mut v_a_5321_: *mut crate::leanh::LeanObject,
    mut v_a_5322_: *mut crate::leanh::LeanObject,
    mut v_a_5323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: u8 = 0;
    let mut v_value_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: u8 = 0;
    let mut v_k_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v_alts_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: u8 = 0;
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: usize = 0;
    let mut v___x_5356_: usize = 0;
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5358_: u8 = 0;
    let mut v_k_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: u8 = 0;
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_5319_) {
                0 => {
                    v_k_5325_ = crate::leanh::lean_ctor_get(v_a_5319_, 1);
                    crate::leanh::lean_inc_ref(v_k_5325_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 2);
                    v_a_5319_ = v_k_5325_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_5327_ = crate::leanh::lean_ctor_get(v_a_5319_, 0);
                    crate::leanh::lean_inc_ref_n(v_decl_5327_, 2);
                    v_k_5328_ = crate::leanh::lean_ctor_get(v_a_5319_, 1);
                    crate::leanh::lean_inc_ref(v_k_5328_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 2);
                    crate::leanh::lean_inc_ref(v_f_5318_);
                    crate::leanh::lean_inc(v_a_5323_);
                    crate::leanh::lean_inc_ref(v_a_5322_);
                    crate::leanh::lean_inc(v_a_5321_);
                    crate::leanh::lean_inc_ref(v_a_5320_);
                    v___x_5329_ = crate::leanh::lean_apply_6(
                        v_f_5318_,
                        v_decl_5327_,
                        v_a_5320_,
                        v_a_5321_,
                        v_a_5322_,
                        v_a_5323_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5329_) == 0 {
                        v_a_5330_ = crate::leanh::lean_ctor_get(v___x_5329_, 0);
                        crate::leanh::lean_inc(v_a_5330_);
                        v___x_5331_ = (crate::leanh::lean_unbox(v_a_5330_) as u8);
                        crate::leanh::lean_dec(v_a_5330_);
                        if v___x_5331_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5329_, 1);
                            v_value_5332_ = crate::leanh::lean_ctor_get(v_decl_5327_, 4);
                            crate::leanh::lean_inc_ref(v_value_5332_);
                            crate::leanh::lean_dec_ref(v_decl_5327_);
                            crate::leanh::lean_inc_ref(v_f_5318_);
                            v___x_5333_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_5317_, v_f_5318_, v_value_5332_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
                            if crate::leanh::lean_obj_tag(v___x_5333_) == 0 {
                                v_a_5334_ = crate::leanh::lean_ctor_get(v___x_5333_, 0);
                                crate::leanh::lean_inc(v_a_5334_);
                                v___x_5335_ = (crate::leanh::lean_unbox(v_a_5334_) as u8);
                                crate::leanh::lean_dec(v_a_5334_);
                                if v___x_5335_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5333_, 1);
                                    v_a_5319_ = v_k_5328_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_k_5328_);
                                    crate::leanh::lean_dec_ref(v_f_5318_);
                                    return v___x_5333_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_k_5328_);
                                crate::leanh::lean_dec_ref(v_f_5318_);
                                return v___x_5333_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5328_);
                            crate::leanh::lean_dec_ref(v_decl_5327_);
                            crate::leanh::lean_dec_ref(v_f_5318_);
                            return v___x_5329_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5328_);
                        crate::leanh::lean_dec_ref(v_decl_5327_);
                        crate::leanh::lean_dec_ref(v_f_5318_);
                        return v___x_5329_;
                    }
                }
                2 => {
                    v_k_5337_ = crate::leanh::lean_ctor_get(v_a_5319_, 1);
                    crate::leanh::lean_inc_ref(v_k_5337_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 2);
                    v_a_5319_ = v_k_5337_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_cases_5339_ = crate::leanh::lean_ctor_get(v_a_5319_, 0);
                    v_isSharedCheck_5358_ = (!crate::leanh::lean_is_exclusive(v_a_5319_)) as u8;
                    if v_isSharedCheck_5358_ == 0 {
                        v___x_5341_ = v_a_5319_;
                        v_isShared_5342_ = v_isSharedCheck_5358_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_5339_);
                        crate::leanh::lean_dec(v_a_5319_);
                        v___x_5341_ = crate::leanh::lean_box(0);
                        v_isShared_5342_ = v_isSharedCheck_5358_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_k_5359_ = crate::leanh::lean_ctor_get(v_a_5319_, 3);
                    crate::leanh::lean_inc_ref(v_k_5359_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 4);
                    v_a_5319_ = v_k_5359_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_5361_ = crate::leanh::lean_ctor_get(v_a_5319_, 3);
                    crate::leanh::lean_inc_ref(v_k_5361_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 4);
                    v_a_5319_ = v_k_5361_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_5363_ = crate::leanh::lean_ctor_get(v_a_5319_, 5);
                    crate::leanh::lean_inc_ref(v_k_5363_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 6);
                    v_a_5319_ = v_k_5363_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_5365_ = crate::leanh::lean_ctor_get(v_a_5319_, 2);
                    crate::leanh::lean_inc_ref(v_k_5365_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 3);
                    v_a_5319_ = v_k_5365_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_5367_ = crate::leanh::lean_ctor_get(v_a_5319_, 2);
                    crate::leanh::lean_inc_ref(v_k_5367_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 3);
                    v_a_5319_ = v_k_5367_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_5369_ = crate::leanh::lean_ctor_get(v_a_5319_, 3);
                    crate::leanh::lean_inc_ref(v_k_5369_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 4);
                    v_a_5319_ = v_k_5369_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_5371_ = crate::leanh::lean_ctor_get(v_a_5319_, 1);
                    crate::leanh::lean_inc_ref(v_k_5371_);
                    crate::leanh::lean_dec_ref_known(v_a_5319_, 2);
                    v_a_5319_ = v_k_5371_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_5319_);
                    crate::leanh::lean_dec_ref(v_f_5318_);
                    v___x_5373_ = 0;
                    v___x_5374_ = crate::leanh::lean_box((v___x_5373_) as usize);
                    v___x_5375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5375_, 0, v___x_5374_);
                    return v___x_5375_;
                }
            },
            1 => {
                v_alts_5343_ = crate::leanh::lean_ctor_get(v_cases_5339_, 3);
                crate::leanh::lean_inc_ref(v_alts_5343_);
                crate::leanh::lean_dec_ref(v_cases_5339_);
                v___x_5344_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5345_ = lean_array_get_size(v_alts_5343_);
                v___x_5346_ = lean_nat_dec_lt(v___x_5344_, v___x_5345_);
                if v___x_5346_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_5343_);
                    crate::leanh::lean_dec_ref(v_f_5318_);
                    v___x_5347_ = crate::leanh::lean_box((v___x_5346_) as usize);
                    if v_isShared_5342_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5341_, 0);
                        crate::leanh::lean_ctor_set(v___x_5341_, 0, v___x_5347_);
                        v___x_5349_ = v___x_5341_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5350_, 0, v___x_5347_);
                        v___x_5349_ = v_reuseFailAlloc_5350_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_5346_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_5343_);
                        crate::leanh::lean_dec_ref(v_f_5318_);
                        v___x_5351_ = crate::leanh::lean_box((v___x_5346_) as usize);
                        if v_isShared_5342_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5341_, 0);
                            crate::leanh::lean_ctor_set(v___x_5341_, 0, v___x_5351_);
                            v___x_5353_ = v___x_5341_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5354_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5354_, 0, v___x_5351_);
                            v___x_5353_ = v_reuseFailAlloc_5354_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5341_);
                        v___x_5355_ = 0usize;
                        v___x_5356_ = lean_usize_of_nat(v___x_5345_);
                        v___x_5357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_5317_, v_f_5318_, v_alts_5343_, v___x_5355_, v___x_5356_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
                        crate::leanh::lean_dec_ref(v_alts_5343_);
                        return v___x_5357_;
                    }
                }
            }
            2 => {
                return v___x_5349_;
            }
            3 => {
                return v___x_5353_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(
    mut v_pu_5376_: u8,
    mut v_f_5377_: *mut crate::leanh::LeanObject,
    mut v_as_5378_: *mut crate::leanh::LeanObject,
    mut v_i_5379_: usize,
    mut v_stop_5380_: usize,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5386_: u8 = 0;
    let mut v___x_5387_: u8 = 0;
    let mut v___y_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5395_: u8 = 0;
    let mut v___x_5396_: usize = 0;
    let mut v___x_5397_: usize = 0;
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5403_: u8 = 0;
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: u8 = 0;
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5386_ = lean_usize_dec_eq(v_i_5379_, v_stop_5380_);
                if v___x_5386_ == 0 {
                    v___x_5387_ = 1;
                    v___x_5404_ = lean_array_uget_borrowed(v_as_5378_, v_i_5379_);
                    match crate::leanh::lean_obj_tag(v___x_5404_) {
                        0 => {
                            v_code_5405_ = crate::leanh::lean_ctor_get(v___x_5404_, 2);
                            crate::leanh::lean_inc_ref(v_code_5405_);
                            v___y_5389_ = v_code_5405_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_5406_ = crate::leanh::lean_ctor_get(v___x_5404_, 1);
                            crate::leanh::lean_inc_ref(v_code_5406_);
                            v___y_5389_ = v_code_5406_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_5407_ = crate::leanh::lean_ctor_get(v___x_5404_, 0);
                            crate::leanh::lean_inc_ref(v_code_5407_);
                            v___y_5389_ = v_code_5407_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5377_);
                    v___x_5408_ = 0;
                    v___x_5409_ = crate::leanh::lean_box((v___x_5408_) as usize);
                    v___x_5410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5410_, 0, v___x_5409_);
                    return v___x_5410_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_5377_);
                v___x_5390_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_5376_, v_f_5377_, v___y_5389_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
                if crate::leanh::lean_obj_tag(v___x_5390_) == 0 {
                    v_a_5391_ = crate::leanh::lean_ctor_get(v___x_5390_, 0);
                    v_isSharedCheck_5403_ = (!crate::leanh::lean_is_exclusive(v___x_5390_)) as u8;
                    if v_isSharedCheck_5403_ == 0 {
                        v___x_5393_ = v___x_5390_;
                        v_isShared_5394_ = v_isSharedCheck_5403_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5391_);
                        crate::leanh::lean_dec(v___x_5390_);
                        v___x_5393_ = crate::leanh::lean_box(0);
                        v_isShared_5394_ = v_isSharedCheck_5403_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5377_);
                    return v___x_5390_;
                }
            }
            2 => {
                v___x_5395_ = (crate::leanh::lean_unbox(v_a_5391_) as u8);
                crate::leanh::lean_dec(v_a_5391_);
                if v___x_5395_ == 0 {
                    crate::leanh::lean_del_object(v___x_5393_);
                    v___x_5396_ = 1usize;
                    v___x_5397_ = lean_usize_add(v_i_5379_, v___x_5396_);
                    v_i_5379_ = v___x_5397_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_5377_);
                    v___x_5399_ = crate::leanh::lean_box((v___x_5387_) as usize);
                    if v_isShared_5394_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5393_, 0, v___x_5399_);
                        v___x_5401_ = v___x_5393_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5399_);
                        v___x_5401_ = v_reuseFailAlloc_5402_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(
    mut v_pu_5411_: *mut crate::leanh::LeanObject,
    mut v_f_5412_: *mut crate::leanh::LeanObject,
    mut v_as_5413_: *mut crate::leanh::LeanObject,
    mut v_i_5414_: *mut crate::leanh::LeanObject,
    mut v_stop_5415_: *mut crate::leanh::LeanObject,
    mut v___y_5416_: *mut crate::leanh::LeanObject,
    mut v___y_5417_: *mut crate::leanh::LeanObject,
    mut v___y_5418_: *mut crate::leanh::LeanObject,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5421_: u8 = 0;
    let mut v_i_boxed_5422_: usize = 0;
    let mut v_stop_boxed_5423_: usize = 0;
    let mut v_res_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5421_ = (crate::leanh::lean_unbox(v_pu_5411_) as u8);
    v_i_boxed_5422_ = crate::leanh::lean_unbox_usize(v_i_5414_);
    crate::leanh::lean_dec(v_i_5414_);
    v_stop_boxed_5423_ = crate::leanh::lean_unbox_usize(v_stop_5415_);
    crate::leanh::lean_dec(v_stop_5415_);
    v_res_5424_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_boxed_5421_, v_f_5412_, v_as_5413_, v_i_boxed_5422_, v_stop_boxed_5423_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
    crate::leanh::lean_dec(v___y_5419_);
    crate::leanh::lean_dec_ref(v___y_5418_);
    crate::leanh::lean_dec(v___y_5417_);
    crate::leanh::lean_dec_ref(v___y_5416_);
    crate::leanh::lean_dec_ref(v_as_5413_);
    return v_res_5424_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(
    mut v_pu_5425_: *mut crate::leanh::LeanObject,
    mut v_f_5426_: *mut crate::leanh::LeanObject,
    mut v_a_5427_: *mut crate::leanh::LeanObject,
    mut v_a_5428_: *mut crate::leanh::LeanObject,
    mut v_a_5429_: *mut crate::leanh::LeanObject,
    mut v_a_5430_: *mut crate::leanh::LeanObject,
    mut v_a_5431_: *mut crate::leanh::LeanObject,
    mut v_a_5432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5433_: u8 = 0;
    let mut v_res_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5433_ = (crate::leanh::lean_unbox(v_pu_5425_) as u8);
    v_res_5434_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(
        v_pu_boxed_5433_,
        v_f_5426_,
        v_a_5427_,
        v_a_5428_,
        v_a_5429_,
        v_a_5430_,
        v_a_5431_,
    );
    crate::leanh::lean_dec(v_a_5431_);
    crate::leanh::lean_dec_ref(v_a_5430_);
    crate::leanh::lean_dec(v_a_5429_);
    crate::leanh::lean_dec_ref(v_a_5428_);
    return v_res_5434_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(
    mut v_pu_5435_: u8,
    mut v_f_5436_: *mut crate::leanh::LeanObject,
    mut v_as_5437_: *mut crate::leanh::LeanObject,
    mut v_i_5438_: usize,
    mut v_stop_5439_: usize,
    mut v_b_5440_: *mut crate::leanh::LeanObject,
    mut v___y_5441_: *mut crate::leanh::LeanObject,
    mut v___y_5442_: *mut crate::leanh::LeanObject,
    mut v___y_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5446_: u8 = 0;
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: usize = 0;
    let mut v___x_5456_: usize = 0;
    let mut v___x_5458_: u8 = 0;
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5446_ = lean_usize_dec_eq(v_i_5438_, v_stop_5439_);
                if v___x_5446_ == 0 {
                    v___x_5447_ = lean_array_uget_borrowed(v_as_5437_, v_i_5438_);
                    v_value_5448_ = crate::leanh::lean_ctor_get(v___x_5447_, 1);
                    v___x_5449_ = crate::leanh::lean_box((v_pu_5435_) as usize);
                    crate::leanh::lean_inc_ref(v_f_5436_);
                    v___x_5450_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_5450_, 0, v___x_5449_);
                    crate::leanh::lean_closure_set(v___x_5450_, 1, v_f_5436_);
                    crate::leanh::lean_inc_ref(v_value_5448_);
                    v___x_5451_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_5448_, v___x_5450_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_);
                    if crate::leanh::lean_obj_tag(v___x_5451_) == 0 {
                        v_a_5452_ = crate::leanh::lean_ctor_get(v___x_5451_, 0);
                        crate::leanh::lean_inc(v_a_5452_);
                        crate::leanh::lean_dec_ref_known(v___x_5451_, 1);
                        v___x_5458_ = (crate::leanh::lean_unbox(v_a_5452_) as u8);
                        crate::leanh::lean_dec(v_a_5452_);
                        if v___x_5458_ == 0 {
                            v_a_5454_ = v_b_5440_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_5447_);
                            v___x_5459_ = lean_array_push(v_b_5440_, v___x_5447_);
                            v_a_5454_ = v___x_5459_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5440_);
                        crate::leanh::lean_dec_ref(v_f_5436_);
                        v_a_5460_ = crate::leanh::lean_ctor_get(v___x_5451_, 0);
                        v_isSharedCheck_5467_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5451_)) as u8;
                        if v_isSharedCheck_5467_ == 0 {
                            v___x_5462_ = v___x_5451_;
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5460_);
                            crate::leanh::lean_dec(v___x_5451_);
                            v___x_5462_ = crate::leanh::lean_box(0);
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5436_);
                    v___x_5468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5468_, 0, v_b_5440_);
                    return v___x_5468_;
                }
            }
            1 => {
                v___x_5455_ = 1usize;
                v___x_5456_ = lean_usize_add(v_i_5438_, v___x_5455_);
                v_i_5438_ = v___x_5456_;
                v_b_5440_ = v_a_5454_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5463_ == 0 {
                    v___x_5465_ = v___x_5462_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
                    v___x_5465_ = v_reuseFailAlloc_5466_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(
    mut v_pu_5469_: *mut crate::leanh::LeanObject,
    mut v_f_5470_: *mut crate::leanh::LeanObject,
    mut v_as_5471_: *mut crate::leanh::LeanObject,
    mut v_i_5472_: *mut crate::leanh::LeanObject,
    mut v_stop_5473_: *mut crate::leanh::LeanObject,
    mut v_b_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
    mut v___y_5476_: *mut crate::leanh::LeanObject,
    mut v___y_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5480_: u8 = 0;
    let mut v_i_boxed_5481_: usize = 0;
    let mut v_stop_boxed_5482_: usize = 0;
    let mut v_res_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5480_ = (crate::leanh::lean_unbox(v_pu_5469_) as u8);
    v_i_boxed_5481_ = crate::leanh::lean_unbox_usize(v_i_5472_);
    crate::leanh::lean_dec(v_i_5472_);
    v_stop_boxed_5482_ = crate::leanh::lean_unbox_usize(v_stop_5473_);
    crate::leanh::lean_dec(v_stop_5473_);
    v_res_5483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_boxed_5480_, v_f_5470_, v_as_5471_, v_i_boxed_5481_, v_stop_boxed_5482_, v_b_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_);
    crate::leanh::lean_dec(v___y_5478_);
    crate::leanh::lean_dec_ref(v___y_5477_);
    crate::leanh::lean_dec(v___y_5476_);
    crate::leanh::lean_dec_ref(v___y_5475_);
    crate::leanh::lean_dec_ref(v_as_5471_);
    return v_res_5483_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByFun(
    mut v_pu_5484_: u8,
    mut v_f_5485_: *mut crate::leanh::LeanObject,
    mut v_a_5486_: *mut crate::leanh::LeanObject,
    mut v_a_5487_: *mut crate::leanh::LeanObject,
    mut v_a_5488_: *mut crate::leanh::LeanObject,
    mut v_a_5489_: *mut crate::leanh::LeanObject,
    mut v_a_5490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: u8 = 0;
    v___x_5492_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5493_ = lean_array_get_size(v_a_5486_);
    v___x_5494_ = l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0;
    v___x_5495_ = lean_nat_dec_lt(v___x_5492_, v___x_5493_);
    if v___x_5495_ == 0 {
        let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_5485_);
        v___x_5496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5496_, 0, v___x_5494_);
        return v___x_5496_;
    } else {
        let mut v___x_5497_: u8 = 0;
        v___x_5497_ = lean_nat_dec_le(v___x_5493_, v___x_5493_);
        if v___x_5497_ == 0 {
            if v___x_5495_ == 0 {
                let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_5485_);
                v___x_5498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5498_, 0, v___x_5494_);
                return v___x_5498_;
            } else {
                let mut v___x_5499_: usize = 0;
                let mut v___x_5500_: usize = 0;
                let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5499_ = 0usize;
                v___x_5500_ = lean_usize_of_nat(v___x_5493_);
                v___x_5501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_5484_, v_f_5485_, v_a_5486_, v___x_5499_, v___x_5500_, v___x_5494_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_);
                return v___x_5501_;
            }
        } else {
            let mut v___x_5502_: usize = 0;
            let mut v___x_5503_: usize = 0;
            let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5502_ = 0usize;
            v___x_5503_ = lean_usize_of_nat(v___x_5493_);
            v___x_5504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_5484_, v_f_5485_, v_a_5486_, v___x_5502_, v___x_5503_, v___x_5494_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_);
            return v___x_5504_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(
    mut v_pu_5505_: *mut crate::leanh::LeanObject,
    mut v_f_5506_: *mut crate::leanh::LeanObject,
    mut v_a_5507_: *mut crate::leanh::LeanObject,
    mut v_a_5508_: *mut crate::leanh::LeanObject,
    mut v_a_5509_: *mut crate::leanh::LeanObject,
    mut v_a_5510_: *mut crate::leanh::LeanObject,
    mut v_a_5511_: *mut crate::leanh::LeanObject,
    mut v_a_5512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5513_: u8 = 0;
    let mut v_res_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5513_ = (crate::leanh::lean_unbox(v_pu_5505_) as u8);
    v_res_5514_ = l_Lean_Compiler_LCNF_Probe_filterByFun(
        v_pu_boxed_5513_,
        v_f_5506_,
        v_a_5507_,
        v_a_5508_,
        v_a_5509_,
        v_a_5510_,
        v_a_5511_,
    );
    crate::leanh::lean_dec(v_a_5511_);
    crate::leanh::lean_dec_ref(v_a_5510_);
    crate::leanh::lean_dec(v_a_5509_);
    crate::leanh::lean_dec_ref(v_a_5508_);
    crate::leanh::lean_dec_ref(v_a_5507_);
    return v_res_5514_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(
    mut v_pu_5515_: u8,
    mut v_f_5516_: *mut crate::leanh::LeanObject,
    mut v_a_5517_: *mut crate::leanh::LeanObject,
    mut v_a_5518_: *mut crate::leanh::LeanObject,
    mut v_a_5519_: *mut crate::leanh::LeanObject,
    mut v_a_5520_: *mut crate::leanh::LeanObject,
    mut v_a_5521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: u8 = 0;
    let mut v_decl_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: u8 = 0;
    let mut v_value_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: u8 = 0;
    let mut v_cases_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5545_: u8 = 0;
    let mut v_alts_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: u8 = 0;
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: usize = 0;
    let mut v___x_5559_: usize = 0;
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5561_: u8 = 0;
    let mut v_k_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: u8 = 0;
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_5517_) {
                0 => {
                    v_k_5523_ = crate::leanh::lean_ctor_get(v_a_5517_, 1);
                    crate::leanh::lean_inc_ref(v_k_5523_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 2);
                    v_a_5517_ = v_k_5523_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_5525_ = crate::leanh::lean_ctor_get(v_a_5517_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5525_);
                    v_k_5526_ = crate::leanh::lean_ctor_get(v_a_5517_, 1);
                    crate::leanh::lean_inc_ref(v_k_5526_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 2);
                    v_value_5527_ = crate::leanh::lean_ctor_get(v_decl_5525_, 4);
                    crate::leanh::lean_inc_ref(v_value_5527_);
                    crate::leanh::lean_dec_ref(v_decl_5525_);
                    crate::leanh::lean_inc_ref(v_f_5516_);
                    v___x_5528_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_5515_, v_f_5516_, v_value_5527_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_);
                    if crate::leanh::lean_obj_tag(v___x_5528_) == 0 {
                        v_a_5529_ = crate::leanh::lean_ctor_get(v___x_5528_, 0);
                        crate::leanh::lean_inc(v_a_5529_);
                        v___x_5530_ = (crate::leanh::lean_unbox(v_a_5529_) as u8);
                        crate::leanh::lean_dec(v_a_5529_);
                        if v___x_5530_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5528_, 1);
                            v_a_5517_ = v_k_5526_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5526_);
                            crate::leanh::lean_dec_ref(v_f_5516_);
                            return v___x_5528_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5526_);
                        crate::leanh::lean_dec_ref(v_f_5516_);
                        return v___x_5528_;
                    }
                }
                2 => {
                    v_decl_5532_ = crate::leanh::lean_ctor_get(v_a_5517_, 0);
                    crate::leanh::lean_inc_ref_n(v_decl_5532_, 2);
                    v_k_5533_ = crate::leanh::lean_ctor_get(v_a_5517_, 1);
                    crate::leanh::lean_inc_ref(v_k_5533_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 2);
                    crate::leanh::lean_inc_ref(v_f_5516_);
                    crate::leanh::lean_inc(v_a_5521_);
                    crate::leanh::lean_inc_ref(v_a_5520_);
                    crate::leanh::lean_inc(v_a_5519_);
                    crate::leanh::lean_inc_ref(v_a_5518_);
                    v___x_5534_ = crate::leanh::lean_apply_6(
                        v_f_5516_,
                        v_decl_5532_,
                        v_a_5518_,
                        v_a_5519_,
                        v_a_5520_,
                        v_a_5521_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5534_) == 0 {
                        v_a_5535_ = crate::leanh::lean_ctor_get(v___x_5534_, 0);
                        crate::leanh::lean_inc(v_a_5535_);
                        v___x_5536_ = (crate::leanh::lean_unbox(v_a_5535_) as u8);
                        crate::leanh::lean_dec(v_a_5535_);
                        if v___x_5536_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5534_, 1);
                            v_value_5537_ = crate::leanh::lean_ctor_get(v_decl_5532_, 4);
                            crate::leanh::lean_inc_ref(v_value_5537_);
                            crate::leanh::lean_dec_ref(v_decl_5532_);
                            crate::leanh::lean_inc_ref(v_f_5516_);
                            v___x_5538_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_5515_, v_f_5516_, v_value_5537_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_);
                            if crate::leanh::lean_obj_tag(v___x_5538_) == 0 {
                                v_a_5539_ = crate::leanh::lean_ctor_get(v___x_5538_, 0);
                                crate::leanh::lean_inc(v_a_5539_);
                                v___x_5540_ = (crate::leanh::lean_unbox(v_a_5539_) as u8);
                                crate::leanh::lean_dec(v_a_5539_);
                                if v___x_5540_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5538_, 1);
                                    v_a_5517_ = v_k_5533_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_k_5533_);
                                    crate::leanh::lean_dec_ref(v_f_5516_);
                                    return v___x_5538_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_k_5533_);
                                crate::leanh::lean_dec_ref(v_f_5516_);
                                return v___x_5538_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5533_);
                            crate::leanh::lean_dec_ref(v_decl_5532_);
                            crate::leanh::lean_dec_ref(v_f_5516_);
                            return v___x_5534_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5533_);
                        crate::leanh::lean_dec_ref(v_decl_5532_);
                        crate::leanh::lean_dec_ref(v_f_5516_);
                        return v___x_5534_;
                    }
                }
                4 => {
                    v_cases_5542_ = crate::leanh::lean_ctor_get(v_a_5517_, 0);
                    v_isSharedCheck_5561_ = (!crate::leanh::lean_is_exclusive(v_a_5517_)) as u8;
                    if v_isSharedCheck_5561_ == 0 {
                        v___x_5544_ = v_a_5517_;
                        v_isShared_5545_ = v_isSharedCheck_5561_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_5542_);
                        crate::leanh::lean_dec(v_a_5517_);
                        v___x_5544_ = crate::leanh::lean_box(0);
                        v_isShared_5545_ = v_isSharedCheck_5561_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_k_5562_ = crate::leanh::lean_ctor_get(v_a_5517_, 3);
                    crate::leanh::lean_inc_ref(v_k_5562_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 4);
                    v_a_5517_ = v_k_5562_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_5564_ = crate::leanh::lean_ctor_get(v_a_5517_, 3);
                    crate::leanh::lean_inc_ref(v_k_5564_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 4);
                    v_a_5517_ = v_k_5564_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_5566_ = crate::leanh::lean_ctor_get(v_a_5517_, 5);
                    crate::leanh::lean_inc_ref(v_k_5566_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 6);
                    v_a_5517_ = v_k_5566_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_5568_ = crate::leanh::lean_ctor_get(v_a_5517_, 2);
                    crate::leanh::lean_inc_ref(v_k_5568_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 3);
                    v_a_5517_ = v_k_5568_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_5570_ = crate::leanh::lean_ctor_get(v_a_5517_, 2);
                    crate::leanh::lean_inc_ref(v_k_5570_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 3);
                    v_a_5517_ = v_k_5570_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_5572_ = crate::leanh::lean_ctor_get(v_a_5517_, 3);
                    crate::leanh::lean_inc_ref(v_k_5572_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 4);
                    v_a_5517_ = v_k_5572_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_5574_ = crate::leanh::lean_ctor_get(v_a_5517_, 1);
                    crate::leanh::lean_inc_ref(v_k_5574_);
                    crate::leanh::lean_dec_ref_known(v_a_5517_, 2);
                    v_a_5517_ = v_k_5574_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_5517_);
                    crate::leanh::lean_dec_ref(v_f_5516_);
                    v___x_5576_ = 0;
                    v___x_5577_ = crate::leanh::lean_box((v___x_5576_) as usize);
                    v___x_5578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5578_, 0, v___x_5577_);
                    return v___x_5578_;
                }
            },
            1 => {
                v_alts_5546_ = crate::leanh::lean_ctor_get(v_cases_5542_, 3);
                crate::leanh::lean_inc_ref(v_alts_5546_);
                crate::leanh::lean_dec_ref(v_cases_5542_);
                v___x_5547_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5548_ = lean_array_get_size(v_alts_5546_);
                v___x_5549_ = lean_nat_dec_lt(v___x_5547_, v___x_5548_);
                if v___x_5549_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_5546_);
                    crate::leanh::lean_dec_ref(v_f_5516_);
                    v___x_5550_ = crate::leanh::lean_box((v___x_5549_) as usize);
                    if v_isShared_5545_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5544_, 0);
                        crate::leanh::lean_ctor_set(v___x_5544_, 0, v___x_5550_);
                        v___x_5552_ = v___x_5544_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5553_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5550_);
                        v___x_5552_ = v_reuseFailAlloc_5553_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_5549_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_5546_);
                        crate::leanh::lean_dec_ref(v_f_5516_);
                        v___x_5554_ = crate::leanh::lean_box((v___x_5549_) as usize);
                        if v_isShared_5545_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5544_, 0);
                            crate::leanh::lean_ctor_set(v___x_5544_, 0, v___x_5554_);
                            v___x_5556_ = v___x_5544_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5557_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5554_);
                            v___x_5556_ = v_reuseFailAlloc_5557_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5544_);
                        v___x_5558_ = 0usize;
                        v___x_5559_ = lean_usize_of_nat(v___x_5548_);
                        v___x_5560_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_5515_, v_f_5516_, v_alts_5546_, v___x_5558_, v___x_5559_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_);
                        crate::leanh::lean_dec_ref(v_alts_5546_);
                        return v___x_5560_;
                    }
                }
            }
            2 => {
                return v___x_5552_;
            }
            3 => {
                return v___x_5556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(
    mut v_pu_5579_: u8,
    mut v_f_5580_: *mut crate::leanh::LeanObject,
    mut v_as_5581_: *mut crate::leanh::LeanObject,
    mut v_i_5582_: usize,
    mut v_stop_5583_: usize,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
    mut v___y_5586_: *mut crate::leanh::LeanObject,
    mut v___y_5587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5589_: u8 = 0;
    let mut v___x_5590_: u8 = 0;
    let mut v___y_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5597_: u8 = 0;
    let mut v___x_5598_: u8 = 0;
    let mut v___x_5599_: usize = 0;
    let mut v___x_5600_: usize = 0;
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5606_: u8 = 0;
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: u8 = 0;
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5589_ = lean_usize_dec_eq(v_i_5582_, v_stop_5583_);
                if v___x_5589_ == 0 {
                    v___x_5590_ = 1;
                    v___x_5607_ = lean_array_uget_borrowed(v_as_5581_, v_i_5582_);
                    match crate::leanh::lean_obj_tag(v___x_5607_) {
                        0 => {
                            v_code_5608_ = crate::leanh::lean_ctor_get(v___x_5607_, 2);
                            crate::leanh::lean_inc_ref(v_code_5608_);
                            v___y_5592_ = v_code_5608_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_5609_ = crate::leanh::lean_ctor_get(v___x_5607_, 1);
                            crate::leanh::lean_inc_ref(v_code_5609_);
                            v___y_5592_ = v_code_5609_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_5610_ = crate::leanh::lean_ctor_get(v___x_5607_, 0);
                            crate::leanh::lean_inc_ref(v_code_5610_);
                            v___y_5592_ = v_code_5610_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5580_);
                    v___x_5611_ = 0;
                    v___x_5612_ = crate::leanh::lean_box((v___x_5611_) as usize);
                    v___x_5613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5613_, 0, v___x_5612_);
                    return v___x_5613_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_5580_);
                v___x_5593_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_5579_, v_f_5580_, v___y_5592_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_);
                if crate::leanh::lean_obj_tag(v___x_5593_) == 0 {
                    v_a_5594_ = crate::leanh::lean_ctor_get(v___x_5593_, 0);
                    v_isSharedCheck_5606_ = (!crate::leanh::lean_is_exclusive(v___x_5593_)) as u8;
                    if v_isSharedCheck_5606_ == 0 {
                        v___x_5596_ = v___x_5593_;
                        v_isShared_5597_ = v_isSharedCheck_5606_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5594_);
                        crate::leanh::lean_dec(v___x_5593_);
                        v___x_5596_ = crate::leanh::lean_box(0);
                        v_isShared_5597_ = v_isSharedCheck_5606_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5580_);
                    return v___x_5593_;
                }
            }
            2 => {
                v___x_5598_ = (crate::leanh::lean_unbox(v_a_5594_) as u8);
                crate::leanh::lean_dec(v_a_5594_);
                if v___x_5598_ == 0 {
                    crate::leanh::lean_del_object(v___x_5596_);
                    v___x_5599_ = 1usize;
                    v___x_5600_ = lean_usize_add(v_i_5582_, v___x_5599_);
                    v_i_5582_ = v___x_5600_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_5580_);
                    v___x_5602_ = crate::leanh::lean_box((v___x_5590_) as usize);
                    if v_isShared_5597_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5596_, 0, v___x_5602_);
                        v___x_5604_ = v___x_5596_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
                        v___x_5604_ = v_reuseFailAlloc_5605_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(
    mut v_pu_5614_: *mut crate::leanh::LeanObject,
    mut v_f_5615_: *mut crate::leanh::LeanObject,
    mut v_as_5616_: *mut crate::leanh::LeanObject,
    mut v_i_5617_: *mut crate::leanh::LeanObject,
    mut v_stop_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
    mut v___y_5623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5624_: u8 = 0;
    let mut v_i_boxed_5625_: usize = 0;
    let mut v_stop_boxed_5626_: usize = 0;
    let mut v_res_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5624_ = (crate::leanh::lean_unbox(v_pu_5614_) as u8);
    v_i_boxed_5625_ = crate::leanh::lean_unbox_usize(v_i_5617_);
    crate::leanh::lean_dec(v_i_5617_);
    v_stop_boxed_5626_ = crate::leanh::lean_unbox_usize(v_stop_5618_);
    crate::leanh::lean_dec(v_stop_5618_);
    v_res_5627_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_boxed_5624_, v_f_5615_, v_as_5616_, v_i_boxed_5625_, v_stop_boxed_5626_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_);
    crate::leanh::lean_dec(v___y_5622_);
    crate::leanh::lean_dec_ref(v___y_5621_);
    crate::leanh::lean_dec(v___y_5620_);
    crate::leanh::lean_dec_ref(v___y_5619_);
    crate::leanh::lean_dec_ref(v_as_5616_);
    return v_res_5627_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(
    mut v_pu_5628_: *mut crate::leanh::LeanObject,
    mut v_f_5629_: *mut crate::leanh::LeanObject,
    mut v_a_5630_: *mut crate::leanh::LeanObject,
    mut v_a_5631_: *mut crate::leanh::LeanObject,
    mut v_a_5632_: *mut crate::leanh::LeanObject,
    mut v_a_5633_: *mut crate::leanh::LeanObject,
    mut v_a_5634_: *mut crate::leanh::LeanObject,
    mut v_a_5635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5636_: u8 = 0;
    let mut v_res_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5636_ = (crate::leanh::lean_unbox(v_pu_5628_) as u8);
    v_res_5637_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(
        v_pu_boxed_5636_,
        v_f_5629_,
        v_a_5630_,
        v_a_5631_,
        v_a_5632_,
        v_a_5633_,
        v_a_5634_,
    );
    crate::leanh::lean_dec(v_a_5634_);
    crate::leanh::lean_dec_ref(v_a_5633_);
    crate::leanh::lean_dec(v_a_5632_);
    crate::leanh::lean_dec_ref(v_a_5631_);
    return v_res_5637_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(
    mut v_pu_5638_: u8,
    mut v_f_5639_: *mut crate::leanh::LeanObject,
    mut v_as_5640_: *mut crate::leanh::LeanObject,
    mut v_i_5641_: usize,
    mut v_stop_5642_: usize,
    mut v_b_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
    mut v___y_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5649_: u8 = 0;
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: usize = 0;
    let mut v___x_5659_: usize = 0;
    let mut v___x_5661_: u8 = 0;
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5666_: u8 = 0;
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5670_: u8 = 0;
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5649_ = lean_usize_dec_eq(v_i_5641_, v_stop_5642_);
                if v___x_5649_ == 0 {
                    v___x_5650_ = lean_array_uget_borrowed(v_as_5640_, v_i_5641_);
                    v_value_5651_ = crate::leanh::lean_ctor_get(v___x_5650_, 1);
                    v___x_5652_ = crate::leanh::lean_box((v_pu_5638_) as usize);
                    crate::leanh::lean_inc_ref(v_f_5639_);
                    v___x_5653_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_5653_, 0, v___x_5652_);
                    crate::leanh::lean_closure_set(v___x_5653_, 1, v_f_5639_);
                    crate::leanh::lean_inc_ref(v_value_5651_);
                    v___x_5654_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_5651_, v___x_5653_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
                    if crate::leanh::lean_obj_tag(v___x_5654_) == 0 {
                        v_a_5655_ = crate::leanh::lean_ctor_get(v___x_5654_, 0);
                        crate::leanh::lean_inc(v_a_5655_);
                        crate::leanh::lean_dec_ref_known(v___x_5654_, 1);
                        v___x_5661_ = (crate::leanh::lean_unbox(v_a_5655_) as u8);
                        crate::leanh::lean_dec(v_a_5655_);
                        if v___x_5661_ == 0 {
                            v_a_5657_ = v_b_5643_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_5650_);
                            v___x_5662_ = lean_array_push(v_b_5643_, v___x_5650_);
                            v_a_5657_ = v___x_5662_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5643_);
                        crate::leanh::lean_dec_ref(v_f_5639_);
                        v_a_5663_ = crate::leanh::lean_ctor_get(v___x_5654_, 0);
                        v_isSharedCheck_5670_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5654_)) as u8;
                        if v_isSharedCheck_5670_ == 0 {
                            v___x_5665_ = v___x_5654_;
                            v_isShared_5666_ = v_isSharedCheck_5670_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5663_);
                            crate::leanh::lean_dec(v___x_5654_);
                            v___x_5665_ = crate::leanh::lean_box(0);
                            v_isShared_5666_ = v_isSharedCheck_5670_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5639_);
                    v___x_5671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5671_, 0, v_b_5643_);
                    return v___x_5671_;
                }
            }
            1 => {
                v___x_5658_ = 1usize;
                v___x_5659_ = lean_usize_add(v_i_5641_, v___x_5658_);
                v_i_5641_ = v___x_5659_;
                v_b_5643_ = v_a_5657_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5666_ == 0 {
                    v___x_5668_ = v___x_5665_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5663_);
                    v___x_5668_ = v_reuseFailAlloc_5669_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5668_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(
    mut v_pu_5672_: *mut crate::leanh::LeanObject,
    mut v_f_5673_: *mut crate::leanh::LeanObject,
    mut v_as_5674_: *mut crate::leanh::LeanObject,
    mut v_i_5675_: *mut crate::leanh::LeanObject,
    mut v_stop_5676_: *mut crate::leanh::LeanObject,
    mut v_b_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
    mut v___y_5679_: *mut crate::leanh::LeanObject,
    mut v___y_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5683_: u8 = 0;
    let mut v_i_boxed_5684_: usize = 0;
    let mut v_stop_boxed_5685_: usize = 0;
    let mut v_res_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5683_ = (crate::leanh::lean_unbox(v_pu_5672_) as u8);
    v_i_boxed_5684_ = crate::leanh::lean_unbox_usize(v_i_5675_);
    crate::leanh::lean_dec(v_i_5675_);
    v_stop_boxed_5685_ = crate::leanh::lean_unbox_usize(v_stop_5676_);
    crate::leanh::lean_dec(v_stop_5676_);
    v_res_5686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_boxed_5683_, v_f_5673_, v_as_5674_, v_i_boxed_5684_, v_stop_boxed_5685_, v_b_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
    crate::leanh::lean_dec(v___y_5681_);
    crate::leanh::lean_dec_ref(v___y_5680_);
    crate::leanh::lean_dec(v___y_5679_);
    crate::leanh::lean_dec_ref(v___y_5678_);
    crate::leanh::lean_dec_ref(v_as_5674_);
    return v_res_5686_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByJp(
    mut v_pu_5687_: u8,
    mut v_f_5688_: *mut crate::leanh::LeanObject,
    mut v_a_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
    mut v_a_5691_: *mut crate::leanh::LeanObject,
    mut v_a_5692_: *mut crate::leanh::LeanObject,
    mut v_a_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: u8 = 0;
    v___x_5695_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5696_ = lean_array_get_size(v_a_5689_);
    v___x_5697_ = l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0;
    v___x_5698_ = lean_nat_dec_lt(v___x_5695_, v___x_5696_);
    if v___x_5698_ == 0 {
        let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_5688_);
        v___x_5699_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5699_, 0, v___x_5697_);
        return v___x_5699_;
    } else {
        let mut v___x_5700_: u8 = 0;
        v___x_5700_ = lean_nat_dec_le(v___x_5696_, v___x_5696_);
        if v___x_5700_ == 0 {
            if v___x_5698_ == 0 {
                let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_5688_);
                v___x_5701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5701_, 0, v___x_5697_);
                return v___x_5701_;
            } else {
                let mut v___x_5702_: usize = 0;
                let mut v___x_5703_: usize = 0;
                let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5702_ = 0usize;
                v___x_5703_ = lean_usize_of_nat(v___x_5696_);
                v___x_5704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_5687_, v_f_5688_, v_a_5689_, v___x_5702_, v___x_5703_, v___x_5697_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_);
                return v___x_5704_;
            }
        } else {
            let mut v___x_5705_: usize = 0;
            let mut v___x_5706_: usize = 0;
            let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5705_ = 0usize;
            v___x_5706_ = lean_usize_of_nat(v___x_5696_);
            v___x_5707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_5687_, v_f_5688_, v_a_5689_, v___x_5705_, v___x_5706_, v___x_5697_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_);
            return v___x_5707_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(
    mut v_pu_5708_: *mut crate::leanh::LeanObject,
    mut v_f_5709_: *mut crate::leanh::LeanObject,
    mut v_a_5710_: *mut crate::leanh::LeanObject,
    mut v_a_5711_: *mut crate::leanh::LeanObject,
    mut v_a_5712_: *mut crate::leanh::LeanObject,
    mut v_a_5713_: *mut crate::leanh::LeanObject,
    mut v_a_5714_: *mut crate::leanh::LeanObject,
    mut v_a_5715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5716_: u8 = 0;
    let mut v_res_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5716_ = (crate::leanh::lean_unbox(v_pu_5708_) as u8);
    v_res_5717_ = l_Lean_Compiler_LCNF_Probe_filterByJp(
        v_pu_boxed_5716_,
        v_f_5709_,
        v_a_5710_,
        v_a_5711_,
        v_a_5712_,
        v_a_5713_,
        v_a_5714_,
    );
    crate::leanh::lean_dec(v_a_5714_);
    crate::leanh::lean_dec_ref(v_a_5713_);
    crate::leanh::lean_dec(v_a_5712_);
    crate::leanh::lean_dec_ref(v_a_5711_);
    crate::leanh::lean_dec_ref(v_a_5710_);
    return v_res_5717_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(
    mut v_pu_5718_: u8,
    mut v_f_5719_: *mut crate::leanh::LeanObject,
    mut v_a_5720_: *mut crate::leanh::LeanObject,
    mut v_a_5721_: *mut crate::leanh::LeanObject,
    mut v_a_5722_: *mut crate::leanh::LeanObject,
    mut v_a_5723_: *mut crate::leanh::LeanObject,
    mut v_a_5724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: u8 = 0;
    let mut v_value_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: u8 = 0;
    let mut v_decl_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: u8 = 0;
    let mut v_value_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: u8 = 0;
    let mut v_cases_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5751_: u8 = 0;
    let mut v_alts_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: u8 = 0;
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: usize = 0;
    let mut v___x_5765_: usize = 0;
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5767_: u8 = 0;
    let mut v_k_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: u8 = 0;
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_5720_) {
                0 => {
                    v_k_5726_ = crate::leanh::lean_ctor_get(v_a_5720_, 1);
                    crate::leanh::lean_inc_ref(v_k_5726_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 2);
                    v_a_5720_ = v_k_5726_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_5728_ = crate::leanh::lean_ctor_get(v_a_5720_, 0);
                    crate::leanh::lean_inc_ref_n(v_decl_5728_, 2);
                    v_k_5729_ = crate::leanh::lean_ctor_get(v_a_5720_, 1);
                    crate::leanh::lean_inc_ref(v_k_5729_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 2);
                    crate::leanh::lean_inc_ref(v_f_5719_);
                    crate::leanh::lean_inc(v_a_5724_);
                    crate::leanh::lean_inc_ref(v_a_5723_);
                    crate::leanh::lean_inc(v_a_5722_);
                    crate::leanh::lean_inc_ref(v_a_5721_);
                    v___x_5730_ = crate::leanh::lean_apply_6(
                        v_f_5719_,
                        v_decl_5728_,
                        v_a_5721_,
                        v_a_5722_,
                        v_a_5723_,
                        v_a_5724_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5730_) == 0 {
                        v_a_5731_ = crate::leanh::lean_ctor_get(v___x_5730_, 0);
                        crate::leanh::lean_inc(v_a_5731_);
                        v___x_5732_ = (crate::leanh::lean_unbox(v_a_5731_) as u8);
                        crate::leanh::lean_dec(v_a_5731_);
                        if v___x_5732_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5730_, 1);
                            v_value_5733_ = crate::leanh::lean_ctor_get(v_decl_5728_, 4);
                            crate::leanh::lean_inc_ref(v_value_5733_);
                            crate::leanh::lean_dec_ref(v_decl_5728_);
                            crate::leanh::lean_inc_ref(v_f_5719_);
                            v___x_5734_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_5718_, v_f_5719_, v_value_5733_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_);
                            if crate::leanh::lean_obj_tag(v___x_5734_) == 0 {
                                v_a_5735_ = crate::leanh::lean_ctor_get(v___x_5734_, 0);
                                crate::leanh::lean_inc(v_a_5735_);
                                v___x_5736_ = (crate::leanh::lean_unbox(v_a_5735_) as u8);
                                crate::leanh::lean_dec(v_a_5735_);
                                if v___x_5736_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5734_, 1);
                                    v_a_5720_ = v_k_5729_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_k_5729_);
                                    crate::leanh::lean_dec_ref(v_f_5719_);
                                    return v___x_5734_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_k_5729_);
                                crate::leanh::lean_dec_ref(v_f_5719_);
                                return v___x_5734_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5729_);
                            crate::leanh::lean_dec_ref(v_decl_5728_);
                            crate::leanh::lean_dec_ref(v_f_5719_);
                            return v___x_5730_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5729_);
                        crate::leanh::lean_dec_ref(v_decl_5728_);
                        crate::leanh::lean_dec_ref(v_f_5719_);
                        return v___x_5730_;
                    }
                }
                2 => {
                    v_decl_5738_ = crate::leanh::lean_ctor_get(v_a_5720_, 0);
                    crate::leanh::lean_inc_ref_n(v_decl_5738_, 2);
                    v_k_5739_ = crate::leanh::lean_ctor_get(v_a_5720_, 1);
                    crate::leanh::lean_inc_ref(v_k_5739_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 2);
                    crate::leanh::lean_inc_ref(v_f_5719_);
                    crate::leanh::lean_inc(v_a_5724_);
                    crate::leanh::lean_inc_ref(v_a_5723_);
                    crate::leanh::lean_inc(v_a_5722_);
                    crate::leanh::lean_inc_ref(v_a_5721_);
                    v___x_5740_ = crate::leanh::lean_apply_6(
                        v_f_5719_,
                        v_decl_5738_,
                        v_a_5721_,
                        v_a_5722_,
                        v_a_5723_,
                        v_a_5724_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5740_) == 0 {
                        v_a_5741_ = crate::leanh::lean_ctor_get(v___x_5740_, 0);
                        crate::leanh::lean_inc(v_a_5741_);
                        v___x_5742_ = (crate::leanh::lean_unbox(v_a_5741_) as u8);
                        crate::leanh::lean_dec(v_a_5741_);
                        if v___x_5742_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5740_, 1);
                            v_value_5743_ = crate::leanh::lean_ctor_get(v_decl_5738_, 4);
                            crate::leanh::lean_inc_ref(v_value_5743_);
                            crate::leanh::lean_dec_ref(v_decl_5738_);
                            crate::leanh::lean_inc_ref(v_f_5719_);
                            v___x_5744_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_5718_, v_f_5719_, v_value_5743_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_);
                            if crate::leanh::lean_obj_tag(v___x_5744_) == 0 {
                                v_a_5745_ = crate::leanh::lean_ctor_get(v___x_5744_, 0);
                                crate::leanh::lean_inc(v_a_5745_);
                                v___x_5746_ = (crate::leanh::lean_unbox(v_a_5745_) as u8);
                                crate::leanh::lean_dec(v_a_5745_);
                                if v___x_5746_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5744_, 1);
                                    v_a_5720_ = v_k_5739_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_k_5739_);
                                    crate::leanh::lean_dec_ref(v_f_5719_);
                                    return v___x_5744_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_k_5739_);
                                crate::leanh::lean_dec_ref(v_f_5719_);
                                return v___x_5744_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5739_);
                            crate::leanh::lean_dec_ref(v_decl_5738_);
                            crate::leanh::lean_dec_ref(v_f_5719_);
                            return v___x_5740_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5739_);
                        crate::leanh::lean_dec_ref(v_decl_5738_);
                        crate::leanh::lean_dec_ref(v_f_5719_);
                        return v___x_5740_;
                    }
                }
                4 => {
                    v_cases_5748_ = crate::leanh::lean_ctor_get(v_a_5720_, 0);
                    v_isSharedCheck_5767_ = (!crate::leanh::lean_is_exclusive(v_a_5720_)) as u8;
                    if v_isSharedCheck_5767_ == 0 {
                        v___x_5750_ = v_a_5720_;
                        v_isShared_5751_ = v_isSharedCheck_5767_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_5748_);
                        crate::leanh::lean_dec(v_a_5720_);
                        v___x_5750_ = crate::leanh::lean_box(0);
                        v_isShared_5751_ = v_isSharedCheck_5767_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_k_5768_ = crate::leanh::lean_ctor_get(v_a_5720_, 3);
                    crate::leanh::lean_inc_ref(v_k_5768_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 4);
                    v_a_5720_ = v_k_5768_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_5770_ = crate::leanh::lean_ctor_get(v_a_5720_, 3);
                    crate::leanh::lean_inc_ref(v_k_5770_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 4);
                    v_a_5720_ = v_k_5770_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_5772_ = crate::leanh::lean_ctor_get(v_a_5720_, 5);
                    crate::leanh::lean_inc_ref(v_k_5772_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 6);
                    v_a_5720_ = v_k_5772_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_5774_ = crate::leanh::lean_ctor_get(v_a_5720_, 2);
                    crate::leanh::lean_inc_ref(v_k_5774_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 3);
                    v_a_5720_ = v_k_5774_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_5776_ = crate::leanh::lean_ctor_get(v_a_5720_, 2);
                    crate::leanh::lean_inc_ref(v_k_5776_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 3);
                    v_a_5720_ = v_k_5776_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_5778_ = crate::leanh::lean_ctor_get(v_a_5720_, 3);
                    crate::leanh::lean_inc_ref(v_k_5778_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 4);
                    v_a_5720_ = v_k_5778_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_5780_ = crate::leanh::lean_ctor_get(v_a_5720_, 1);
                    crate::leanh::lean_inc_ref(v_k_5780_);
                    crate::leanh::lean_dec_ref_known(v_a_5720_, 2);
                    v_a_5720_ = v_k_5780_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_5720_);
                    crate::leanh::lean_dec_ref(v_f_5719_);
                    v___x_5782_ = 0;
                    v___x_5783_ = crate::leanh::lean_box((v___x_5782_) as usize);
                    v___x_5784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5784_, 0, v___x_5783_);
                    return v___x_5784_;
                }
            },
            1 => {
                v_alts_5752_ = crate::leanh::lean_ctor_get(v_cases_5748_, 3);
                crate::leanh::lean_inc_ref(v_alts_5752_);
                crate::leanh::lean_dec_ref(v_cases_5748_);
                v___x_5753_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5754_ = lean_array_get_size(v_alts_5752_);
                v___x_5755_ = lean_nat_dec_lt(v___x_5753_, v___x_5754_);
                if v___x_5755_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_5752_);
                    crate::leanh::lean_dec_ref(v_f_5719_);
                    v___x_5756_ = crate::leanh::lean_box((v___x_5755_) as usize);
                    if v_isShared_5751_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5750_, 0);
                        crate::leanh::lean_ctor_set(v___x_5750_, 0, v___x_5756_);
                        v___x_5758_ = v___x_5750_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5756_);
                        v___x_5758_ = v_reuseFailAlloc_5759_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_5755_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_5752_);
                        crate::leanh::lean_dec_ref(v_f_5719_);
                        v___x_5760_ = crate::leanh::lean_box((v___x_5755_) as usize);
                        if v_isShared_5751_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5750_, 0);
                            crate::leanh::lean_ctor_set(v___x_5750_, 0, v___x_5760_);
                            v___x_5762_ = v___x_5750_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5763_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5763_, 0, v___x_5760_);
                            v___x_5762_ = v_reuseFailAlloc_5763_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5750_);
                        v___x_5764_ = 0usize;
                        v___x_5765_ = lean_usize_of_nat(v___x_5754_);
                        v___x_5766_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_5718_, v_f_5719_, v_alts_5752_, v___x_5764_, v___x_5765_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_);
                        crate::leanh::lean_dec_ref(v_alts_5752_);
                        return v___x_5766_;
                    }
                }
            }
            2 => {
                return v___x_5758_;
            }
            3 => {
                return v___x_5762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(
    mut v_pu_5785_: u8,
    mut v_f_5786_: *mut crate::leanh::LeanObject,
    mut v_as_5787_: *mut crate::leanh::LeanObject,
    mut v_i_5788_: usize,
    mut v_stop_5789_: usize,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5795_: u8 = 0;
    let mut v___x_5796_: u8 = 0;
    let mut v___y_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5804_: u8 = 0;
    let mut v___x_5805_: usize = 0;
    let mut v___x_5806_: usize = 0;
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5812_: u8 = 0;
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: u8 = 0;
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5795_ = lean_usize_dec_eq(v_i_5788_, v_stop_5789_);
                if v___x_5795_ == 0 {
                    v___x_5796_ = 1;
                    v___x_5813_ = lean_array_uget_borrowed(v_as_5787_, v_i_5788_);
                    match crate::leanh::lean_obj_tag(v___x_5813_) {
                        0 => {
                            v_code_5814_ = crate::leanh::lean_ctor_get(v___x_5813_, 2);
                            crate::leanh::lean_inc_ref(v_code_5814_);
                            v___y_5798_ = v_code_5814_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_5815_ = crate::leanh::lean_ctor_get(v___x_5813_, 1);
                            crate::leanh::lean_inc_ref(v_code_5815_);
                            v___y_5798_ = v_code_5815_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_5816_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
                            crate::leanh::lean_inc_ref(v_code_5816_);
                            v___y_5798_ = v_code_5816_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5786_);
                    v___x_5817_ = 0;
                    v___x_5818_ = crate::leanh::lean_box((v___x_5817_) as usize);
                    v___x_5819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5819_, 0, v___x_5818_);
                    return v___x_5819_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_5786_);
                v___x_5799_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_5785_, v_f_5786_, v___y_5798_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
                if crate::leanh::lean_obj_tag(v___x_5799_) == 0 {
                    v_a_5800_ = crate::leanh::lean_ctor_get(v___x_5799_, 0);
                    v_isSharedCheck_5812_ = (!crate::leanh::lean_is_exclusive(v___x_5799_)) as u8;
                    if v_isSharedCheck_5812_ == 0 {
                        v___x_5802_ = v___x_5799_;
                        v_isShared_5803_ = v_isSharedCheck_5812_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5800_);
                        crate::leanh::lean_dec(v___x_5799_);
                        v___x_5802_ = crate::leanh::lean_box(0);
                        v_isShared_5803_ = v_isSharedCheck_5812_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5786_);
                    return v___x_5799_;
                }
            }
            2 => {
                v___x_5804_ = (crate::leanh::lean_unbox(v_a_5800_) as u8);
                crate::leanh::lean_dec(v_a_5800_);
                if v___x_5804_ == 0 {
                    crate::leanh::lean_del_object(v___x_5802_);
                    v___x_5805_ = 1usize;
                    v___x_5806_ = lean_usize_add(v_i_5788_, v___x_5805_);
                    v_i_5788_ = v___x_5806_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_5786_);
                    v___x_5808_ = crate::leanh::lean_box((v___x_5796_) as usize);
                    if v_isShared_5803_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5802_, 0, v___x_5808_);
                        v___x_5810_ = v___x_5802_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5811_, 0, v___x_5808_);
                        v___x_5810_ = v_reuseFailAlloc_5811_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(
    mut v_pu_5820_: *mut crate::leanh::LeanObject,
    mut v_f_5821_: *mut crate::leanh::LeanObject,
    mut v_as_5822_: *mut crate::leanh::LeanObject,
    mut v_i_5823_: *mut crate::leanh::LeanObject,
    mut v_stop_5824_: *mut crate::leanh::LeanObject,
    mut v___y_5825_: *mut crate::leanh::LeanObject,
    mut v___y_5826_: *mut crate::leanh::LeanObject,
    mut v___y_5827_: *mut crate::leanh::LeanObject,
    mut v___y_5828_: *mut crate::leanh::LeanObject,
    mut v___y_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5830_: u8 = 0;
    let mut v_i_boxed_5831_: usize = 0;
    let mut v_stop_boxed_5832_: usize = 0;
    let mut v_res_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5830_ = (crate::leanh::lean_unbox(v_pu_5820_) as u8);
    v_i_boxed_5831_ = crate::leanh::lean_unbox_usize(v_i_5823_);
    crate::leanh::lean_dec(v_i_5823_);
    v_stop_boxed_5832_ = crate::leanh::lean_unbox_usize(v_stop_5824_);
    crate::leanh::lean_dec(v_stop_5824_);
    v_res_5833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_boxed_5830_, v_f_5821_, v_as_5822_, v_i_boxed_5831_, v_stop_boxed_5832_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_);
    crate::leanh::lean_dec(v___y_5828_);
    crate::leanh::lean_dec_ref(v___y_5827_);
    crate::leanh::lean_dec(v___y_5826_);
    crate::leanh::lean_dec_ref(v___y_5825_);
    crate::leanh::lean_dec_ref(v_as_5822_);
    return v_res_5833_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(
    mut v_pu_5834_: *mut crate::leanh::LeanObject,
    mut v_f_5835_: *mut crate::leanh::LeanObject,
    mut v_a_5836_: *mut crate::leanh::LeanObject,
    mut v_a_5837_: *mut crate::leanh::LeanObject,
    mut v_a_5838_: *mut crate::leanh::LeanObject,
    mut v_a_5839_: *mut crate::leanh::LeanObject,
    mut v_a_5840_: *mut crate::leanh::LeanObject,
    mut v_a_5841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5842_: u8 = 0;
    let mut v_res_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5842_ = (crate::leanh::lean_unbox(v_pu_5834_) as u8);
    v_res_5843_ =
        l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(
            v_pu_boxed_5842_,
            v_f_5835_,
            v_a_5836_,
            v_a_5837_,
            v_a_5838_,
            v_a_5839_,
            v_a_5840_,
        );
    crate::leanh::lean_dec(v_a_5840_);
    crate::leanh::lean_dec_ref(v_a_5839_);
    crate::leanh::lean_dec(v_a_5838_);
    crate::leanh::lean_dec_ref(v_a_5837_);
    return v_res_5843_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(
    mut v_pu_5844_: u8,
    mut v_f_5845_: *mut crate::leanh::LeanObject,
    mut v_as_5846_: *mut crate::leanh::LeanObject,
    mut v_i_5847_: usize,
    mut v_stop_5848_: usize,
    mut v_b_5849_: *mut crate::leanh::LeanObject,
    mut v___y_5850_: *mut crate::leanh::LeanObject,
    mut v___y_5851_: *mut crate::leanh::LeanObject,
    mut v___y_5852_: *mut crate::leanh::LeanObject,
    mut v___y_5853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5855_: u8 = 0;
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: usize = 0;
    let mut v___x_5865_: usize = 0;
    let mut v___x_5867_: u8 = 0;
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5872_: u8 = 0;
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5876_: u8 = 0;
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5855_ = lean_usize_dec_eq(v_i_5847_, v_stop_5848_);
                if v___x_5855_ == 0 {
                    v___x_5856_ = lean_array_uget_borrowed(v_as_5846_, v_i_5847_);
                    v_value_5857_ = crate::leanh::lean_ctor_get(v___x_5856_, 1);
                    v___x_5858_ = crate::leanh::lean_box((v_pu_5844_) as usize);
                    crate::leanh::lean_inc_ref(v_f_5845_);
                    v___x_5859_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_5859_, 0, v___x_5858_);
                    crate::leanh::lean_closure_set(v___x_5859_, 1, v_f_5845_);
                    crate::leanh::lean_inc_ref(v_value_5857_);
                    v___x_5860_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_5857_, v___x_5859_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
                    if crate::leanh::lean_obj_tag(v___x_5860_) == 0 {
                        v_a_5861_ = crate::leanh::lean_ctor_get(v___x_5860_, 0);
                        crate::leanh::lean_inc(v_a_5861_);
                        crate::leanh::lean_dec_ref_known(v___x_5860_, 1);
                        v___x_5867_ = (crate::leanh::lean_unbox(v_a_5861_) as u8);
                        crate::leanh::lean_dec(v_a_5861_);
                        if v___x_5867_ == 0 {
                            v_a_5863_ = v_b_5849_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_5856_);
                            v___x_5868_ = lean_array_push(v_b_5849_, v___x_5856_);
                            v_a_5863_ = v___x_5868_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5849_);
                        crate::leanh::lean_dec_ref(v_f_5845_);
                        v_a_5869_ = crate::leanh::lean_ctor_get(v___x_5860_, 0);
                        v_isSharedCheck_5876_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5860_)) as u8;
                        if v_isSharedCheck_5876_ == 0 {
                            v___x_5871_ = v___x_5860_;
                            v_isShared_5872_ = v_isSharedCheck_5876_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5869_);
                            crate::leanh::lean_dec(v___x_5860_);
                            v___x_5871_ = crate::leanh::lean_box(0);
                            v_isShared_5872_ = v_isSharedCheck_5876_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5845_);
                    v___x_5877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5877_, 0, v_b_5849_);
                    return v___x_5877_;
                }
            }
            1 => {
                v___x_5864_ = 1usize;
                v___x_5865_ = lean_usize_add(v_i_5847_, v___x_5864_);
                v_i_5847_ = v___x_5865_;
                v_b_5849_ = v_a_5863_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5872_ == 0 {
                    v___x_5874_ = v___x_5871_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_a_5869_);
                    v___x_5874_ = v_reuseFailAlloc_5875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(
    mut v_pu_5878_: *mut crate::leanh::LeanObject,
    mut v_f_5879_: *mut crate::leanh::LeanObject,
    mut v_as_5880_: *mut crate::leanh::LeanObject,
    mut v_i_5881_: *mut crate::leanh::LeanObject,
    mut v_stop_5882_: *mut crate::leanh::LeanObject,
    mut v_b_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5889_: u8 = 0;
    let mut v_i_boxed_5890_: usize = 0;
    let mut v_stop_boxed_5891_: usize = 0;
    let mut v_res_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5889_ = (crate::leanh::lean_unbox(v_pu_5878_) as u8);
    v_i_boxed_5890_ = crate::leanh::lean_unbox_usize(v_i_5881_);
    crate::leanh::lean_dec(v_i_5881_);
    v_stop_boxed_5891_ = crate::leanh::lean_unbox_usize(v_stop_5882_);
    crate::leanh::lean_dec(v_stop_5882_);
    v_res_5892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_boxed_5889_, v_f_5879_, v_as_5880_, v_i_boxed_5890_, v_stop_boxed_5891_, v_b_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_);
    crate::leanh::lean_dec(v___y_5887_);
    crate::leanh::lean_dec_ref(v___y_5886_);
    crate::leanh::lean_dec(v___y_5885_);
    crate::leanh::lean_dec_ref(v___y_5884_);
    crate::leanh::lean_dec_ref(v_as_5880_);
    return v_res_5892_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByFunDecl(
    mut v_pu_5893_: u8,
    mut v_f_5894_: *mut crate::leanh::LeanObject,
    mut v_a_5895_: *mut crate::leanh::LeanObject,
    mut v_a_5896_: *mut crate::leanh::LeanObject,
    mut v_a_5897_: *mut crate::leanh::LeanObject,
    mut v_a_5898_: *mut crate::leanh::LeanObject,
    mut v_a_5899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: u8 = 0;
    v___x_5901_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5902_ = lean_array_get_size(v_a_5895_);
    v___x_5903_ = l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0;
    v___x_5904_ = lean_nat_dec_lt(v___x_5901_, v___x_5902_);
    if v___x_5904_ == 0 {
        let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_5894_);
        v___x_5905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5905_, 0, v___x_5903_);
        return v___x_5905_;
    } else {
        let mut v___x_5906_: u8 = 0;
        v___x_5906_ = lean_nat_dec_le(v___x_5902_, v___x_5902_);
        if v___x_5906_ == 0 {
            if v___x_5904_ == 0 {
                let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_5894_);
                v___x_5907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5907_, 0, v___x_5903_);
                return v___x_5907_;
            } else {
                let mut v___x_5908_: usize = 0;
                let mut v___x_5909_: usize = 0;
                let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5908_ = 0usize;
                v___x_5909_ = lean_usize_of_nat(v___x_5902_);
                v___x_5910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_5893_, v_f_5894_, v_a_5895_, v___x_5908_, v___x_5909_, v___x_5903_, v_a_5896_, v_a_5897_, v_a_5898_, v_a_5899_);
                return v___x_5910_;
            }
        } else {
            let mut v___x_5911_: usize = 0;
            let mut v___x_5912_: usize = 0;
            let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5911_ = 0usize;
            v___x_5912_ = lean_usize_of_nat(v___x_5902_);
            v___x_5913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_5893_, v_f_5894_, v_a_5895_, v___x_5911_, v___x_5912_, v___x_5903_, v_a_5896_, v_a_5897_, v_a_5898_, v_a_5899_);
            return v___x_5913_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(
    mut v_pu_5914_: *mut crate::leanh::LeanObject,
    mut v_f_5915_: *mut crate::leanh::LeanObject,
    mut v_a_5916_: *mut crate::leanh::LeanObject,
    mut v_a_5917_: *mut crate::leanh::LeanObject,
    mut v_a_5918_: *mut crate::leanh::LeanObject,
    mut v_a_5919_: *mut crate::leanh::LeanObject,
    mut v_a_5920_: *mut crate::leanh::LeanObject,
    mut v_a_5921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5922_: u8 = 0;
    let mut v_res_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5922_ = (crate::leanh::lean_unbox(v_pu_5914_) as u8);
    v_res_5923_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(
        v_pu_boxed_5922_,
        v_f_5915_,
        v_a_5916_,
        v_a_5917_,
        v_a_5918_,
        v_a_5919_,
        v_a_5920_,
    );
    crate::leanh::lean_dec(v_a_5920_);
    crate::leanh::lean_dec_ref(v_a_5919_);
    crate::leanh::lean_dec(v_a_5918_);
    crate::leanh::lean_dec_ref(v_a_5917_);
    crate::leanh::lean_dec_ref(v_a_5916_);
    return v_res_5923_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(
    mut v_pu_5924_: u8,
    mut v_f_5925_: *mut crate::leanh::LeanObject,
    mut v_a_5926_: *mut crate::leanh::LeanObject,
    mut v_a_5927_: *mut crate::leanh::LeanObject,
    mut v_a_5928_: *mut crate::leanh::LeanObject,
    mut v_a_5929_: *mut crate::leanh::LeanObject,
    mut v_a_5930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: u8 = 0;
    let mut v_decl_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: u8 = 0;
    let mut v_cases_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: u8 = 0;
    let mut v_alts_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u8 = 0;
    let mut v___x_5956_: usize = 0;
    let mut v___x_5957_: usize = 0;
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: u8 = 0;
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_5926_) {
                0 => {
                    v_k_5932_ = crate::leanh::lean_ctor_get(v_a_5926_, 1);
                    crate::leanh::lean_inc_ref(v_k_5932_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 2);
                    v_a_5926_ = v_k_5932_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_5934_ = crate::leanh::lean_ctor_get(v_a_5926_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5934_);
                    v_k_5935_ = crate::leanh::lean_ctor_get(v_a_5926_, 1);
                    crate::leanh::lean_inc_ref(v_k_5935_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 2);
                    v_value_5936_ = crate::leanh::lean_ctor_get(v_decl_5934_, 4);
                    crate::leanh::lean_inc_ref(v_value_5936_);
                    crate::leanh::lean_dec_ref(v_decl_5934_);
                    crate::leanh::lean_inc_ref(v_f_5925_);
                    v___x_5937_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_5924_, v_f_5925_, v_value_5936_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_);
                    if crate::leanh::lean_obj_tag(v___x_5937_) == 0 {
                        v_a_5938_ = crate::leanh::lean_ctor_get(v___x_5937_, 0);
                        crate::leanh::lean_inc(v_a_5938_);
                        v___x_5939_ = (crate::leanh::lean_unbox(v_a_5938_) as u8);
                        crate::leanh::lean_dec(v_a_5938_);
                        if v___x_5939_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5937_, 1);
                            v_a_5926_ = v_k_5935_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5935_);
                            crate::leanh::lean_dec_ref(v_f_5925_);
                            return v___x_5937_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5935_);
                        crate::leanh::lean_dec_ref(v_f_5925_);
                        return v___x_5937_;
                    }
                }
                2 => {
                    v_decl_5941_ = crate::leanh::lean_ctor_get(v_a_5926_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5941_);
                    v_k_5942_ = crate::leanh::lean_ctor_get(v_a_5926_, 1);
                    crate::leanh::lean_inc_ref(v_k_5942_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 2);
                    v_value_5943_ = crate::leanh::lean_ctor_get(v_decl_5941_, 4);
                    crate::leanh::lean_inc_ref(v_value_5943_);
                    crate::leanh::lean_dec_ref(v_decl_5941_);
                    crate::leanh::lean_inc_ref(v_f_5925_);
                    v___x_5944_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_5924_, v_f_5925_, v_value_5943_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_);
                    if crate::leanh::lean_obj_tag(v___x_5944_) == 0 {
                        v_a_5945_ = crate::leanh::lean_ctor_get(v___x_5944_, 0);
                        crate::leanh::lean_inc(v_a_5945_);
                        v___x_5946_ = (crate::leanh::lean_unbox(v_a_5945_) as u8);
                        crate::leanh::lean_dec(v_a_5945_);
                        if v___x_5946_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5944_, 1);
                            v_a_5926_ = v_k_5942_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5942_);
                            crate::leanh::lean_dec_ref(v_f_5925_);
                            return v___x_5944_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5942_);
                        crate::leanh::lean_dec_ref(v_f_5925_);
                        return v___x_5944_;
                    }
                }
                4 => {
                    v_cases_5948_ = crate::leanh::lean_ctor_get(v_a_5926_, 0);
                    crate::leanh::lean_inc_ref_n(v_cases_5948_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 1);
                    crate::leanh::lean_inc_ref(v_f_5925_);
                    crate::leanh::lean_inc(v_a_5930_);
                    crate::leanh::lean_inc_ref(v_a_5929_);
                    crate::leanh::lean_inc(v_a_5928_);
                    crate::leanh::lean_inc_ref(v_a_5927_);
                    v___x_5949_ = crate::leanh::lean_apply_6(
                        v_f_5925_,
                        v_cases_5948_,
                        v_a_5927_,
                        v_a_5928_,
                        v_a_5929_,
                        v_a_5930_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5949_) == 0 {
                        v_a_5950_ = crate::leanh::lean_ctor_get(v___x_5949_, 0);
                        crate::leanh::lean_inc(v_a_5950_);
                        v___x_5951_ = (crate::leanh::lean_unbox(v_a_5950_) as u8);
                        crate::leanh::lean_dec(v_a_5950_);
                        if v___x_5951_ == 0 {
                            v_alts_5952_ = crate::leanh::lean_ctor_get(v_cases_5948_, 3);
                            crate::leanh::lean_inc_ref(v_alts_5952_);
                            crate::leanh::lean_dec_ref(v_cases_5948_);
                            v___x_5953_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_5954_ = lean_array_get_size(v_alts_5952_);
                            v___x_5955_ = lean_nat_dec_lt(v___x_5953_, v___x_5954_);
                            if v___x_5955_ == 0 {
                                crate::leanh::lean_dec_ref(v_alts_5952_);
                                crate::leanh::lean_dec_ref(v_f_5925_);
                                return v___x_5949_;
                            } else {
                                if v___x_5955_ == 0 {
                                    crate::leanh::lean_dec_ref(v_alts_5952_);
                                    crate::leanh::lean_dec_ref(v_f_5925_);
                                    return v___x_5949_;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_5949_, 1);
                                    v___x_5956_ = 0usize;
                                    v___x_5957_ = lean_usize_of_nat(v___x_5954_);
                                    v___x_5958_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_5924_, v_f_5925_, v_alts_5952_, v___x_5956_, v___x_5957_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_);
                                    crate::leanh::lean_dec_ref(v_alts_5952_);
                                    return v___x_5958_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_cases_5948_);
                            crate::leanh::lean_dec_ref(v_f_5925_);
                            return v___x_5949_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_cases_5948_);
                        crate::leanh::lean_dec_ref(v_f_5925_);
                        return v___x_5949_;
                    }
                }
                7 => {
                    v_k_5959_ = crate::leanh::lean_ctor_get(v_a_5926_, 3);
                    crate::leanh::lean_inc_ref(v_k_5959_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 4);
                    v_a_5926_ = v_k_5959_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_5961_ = crate::leanh::lean_ctor_get(v_a_5926_, 3);
                    crate::leanh::lean_inc_ref(v_k_5961_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 4);
                    v_a_5926_ = v_k_5961_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_5963_ = crate::leanh::lean_ctor_get(v_a_5926_, 5);
                    crate::leanh::lean_inc_ref(v_k_5963_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 6);
                    v_a_5926_ = v_k_5963_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_5965_ = crate::leanh::lean_ctor_get(v_a_5926_, 2);
                    crate::leanh::lean_inc_ref(v_k_5965_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 3);
                    v_a_5926_ = v_k_5965_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_5967_ = crate::leanh::lean_ctor_get(v_a_5926_, 2);
                    crate::leanh::lean_inc_ref(v_k_5967_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 3);
                    v_a_5926_ = v_k_5967_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_5969_ = crate::leanh::lean_ctor_get(v_a_5926_, 3);
                    crate::leanh::lean_inc_ref(v_k_5969_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 4);
                    v_a_5926_ = v_k_5969_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_5971_ = crate::leanh::lean_ctor_get(v_a_5926_, 1);
                    crate::leanh::lean_inc_ref(v_k_5971_);
                    crate::leanh::lean_dec_ref_known(v_a_5926_, 2);
                    v_a_5926_ = v_k_5971_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_5926_);
                    crate::leanh::lean_dec_ref(v_f_5925_);
                    v___x_5973_ = 0;
                    v___x_5974_ = crate::leanh::lean_box((v___x_5973_) as usize);
                    v___x_5975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5975_, 0, v___x_5974_);
                    return v___x_5975_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(
    mut v_pu_5976_: u8,
    mut v_f_5977_: *mut crate::leanh::LeanObject,
    mut v_as_5978_: *mut crate::leanh::LeanObject,
    mut v_i_5979_: usize,
    mut v_stop_5980_: usize,
    mut v___y_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
    mut v___y_5984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5986_: u8 = 0;
    let mut v___x_5987_: u8 = 0;
    let mut v___y_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5994_: u8 = 0;
    let mut v___x_5995_: u8 = 0;
    let mut v___x_5996_: usize = 0;
    let mut v___x_5997_: usize = 0;
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6003_: u8 = 0;
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: u8 = 0;
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5986_ = lean_usize_dec_eq(v_i_5979_, v_stop_5980_);
                if v___x_5986_ == 0 {
                    v___x_5987_ = 1;
                    v___x_6004_ = lean_array_uget_borrowed(v_as_5978_, v_i_5979_);
                    match crate::leanh::lean_obj_tag(v___x_6004_) {
                        0 => {
                            v_code_6005_ = crate::leanh::lean_ctor_get(v___x_6004_, 2);
                            crate::leanh::lean_inc_ref(v_code_6005_);
                            v___y_5989_ = v_code_6005_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_6006_ = crate::leanh::lean_ctor_get(v___x_6004_, 1);
                            crate::leanh::lean_inc_ref(v_code_6006_);
                            v___y_5989_ = v_code_6006_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_6007_ = crate::leanh::lean_ctor_get(v___x_6004_, 0);
                            crate::leanh::lean_inc_ref(v_code_6007_);
                            v___y_5989_ = v_code_6007_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5977_);
                    v___x_6008_ = 0;
                    v___x_6009_ = crate::leanh::lean_box((v___x_6008_) as usize);
                    v___x_6010_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6010_, 0, v___x_6009_);
                    return v___x_6010_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_5977_);
                v___x_5990_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_5976_, v_f_5977_, v___y_5989_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
                if crate::leanh::lean_obj_tag(v___x_5990_) == 0 {
                    v_a_5991_ = crate::leanh::lean_ctor_get(v___x_5990_, 0);
                    v_isSharedCheck_6003_ = (!crate::leanh::lean_is_exclusive(v___x_5990_)) as u8;
                    if v_isSharedCheck_6003_ == 0 {
                        v___x_5993_ = v___x_5990_;
                        v_isShared_5994_ = v_isSharedCheck_6003_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5991_);
                        crate::leanh::lean_dec(v___x_5990_);
                        v___x_5993_ = crate::leanh::lean_box(0);
                        v_isShared_5994_ = v_isSharedCheck_6003_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5977_);
                    return v___x_5990_;
                }
            }
            2 => {
                v___x_5995_ = (crate::leanh::lean_unbox(v_a_5991_) as u8);
                crate::leanh::lean_dec(v_a_5991_);
                if v___x_5995_ == 0 {
                    crate::leanh::lean_del_object(v___x_5993_);
                    v___x_5996_ = 1usize;
                    v___x_5997_ = lean_usize_add(v_i_5979_, v___x_5996_);
                    v_i_5979_ = v___x_5997_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_5977_);
                    v___x_5999_ = crate::leanh::lean_box((v___x_5987_) as usize);
                    if v_isShared_5994_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5993_, 0, v___x_5999_);
                        v___x_6001_ = v___x_5993_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6002_, 0, v___x_5999_);
                        v___x_6001_ = v_reuseFailAlloc_6002_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(
    mut v_pu_6011_: *mut crate::leanh::LeanObject,
    mut v_f_6012_: *mut crate::leanh::LeanObject,
    mut v_as_6013_: *mut crate::leanh::LeanObject,
    mut v_i_6014_: *mut crate::leanh::LeanObject,
    mut v_stop_6015_: *mut crate::leanh::LeanObject,
    mut v___y_6016_: *mut crate::leanh::LeanObject,
    mut v___y_6017_: *mut crate::leanh::LeanObject,
    mut v___y_6018_: *mut crate::leanh::LeanObject,
    mut v___y_6019_: *mut crate::leanh::LeanObject,
    mut v___y_6020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6021_: u8 = 0;
    let mut v_i_boxed_6022_: usize = 0;
    let mut v_stop_boxed_6023_: usize = 0;
    let mut v_res_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6021_ = (crate::leanh::lean_unbox(v_pu_6011_) as u8);
    v_i_boxed_6022_ = crate::leanh::lean_unbox_usize(v_i_6014_);
    crate::leanh::lean_dec(v_i_6014_);
    v_stop_boxed_6023_ = crate::leanh::lean_unbox_usize(v_stop_6015_);
    crate::leanh::lean_dec(v_stop_6015_);
    v_res_6024_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_boxed_6021_, v_f_6012_, v_as_6013_, v_i_boxed_6022_, v_stop_boxed_6023_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_);
    crate::leanh::lean_dec(v___y_6019_);
    crate::leanh::lean_dec_ref(v___y_6018_);
    crate::leanh::lean_dec(v___y_6017_);
    crate::leanh::lean_dec_ref(v___y_6016_);
    crate::leanh::lean_dec_ref(v_as_6013_);
    return v_res_6024_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(
    mut v_pu_6025_: *mut crate::leanh::LeanObject,
    mut v_f_6026_: *mut crate::leanh::LeanObject,
    mut v_a_6027_: *mut crate::leanh::LeanObject,
    mut v_a_6028_: *mut crate::leanh::LeanObject,
    mut v_a_6029_: *mut crate::leanh::LeanObject,
    mut v_a_6030_: *mut crate::leanh::LeanObject,
    mut v_a_6031_: *mut crate::leanh::LeanObject,
    mut v_a_6032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6033_: u8 = 0;
    let mut v_res_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6033_ = (crate::leanh::lean_unbox(v_pu_6025_) as u8);
    v_res_6034_ =
        l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(
            v_pu_boxed_6033_,
            v_f_6026_,
            v_a_6027_,
            v_a_6028_,
            v_a_6029_,
            v_a_6030_,
            v_a_6031_,
        );
    crate::leanh::lean_dec(v_a_6031_);
    crate::leanh::lean_dec_ref(v_a_6030_);
    crate::leanh::lean_dec(v_a_6029_);
    crate::leanh::lean_dec_ref(v_a_6028_);
    return v_res_6034_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(
    mut v_pu_6035_: u8,
    mut v_f_6036_: *mut crate::leanh::LeanObject,
    mut v_as_6037_: *mut crate::leanh::LeanObject,
    mut v_i_6038_: usize,
    mut v_stop_6039_: usize,
    mut v_b_6040_: *mut crate::leanh::LeanObject,
    mut v___y_6041_: *mut crate::leanh::LeanObject,
    mut v___y_6042_: *mut crate::leanh::LeanObject,
    mut v___y_6043_: *mut crate::leanh::LeanObject,
    mut v___y_6044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: usize = 0;
    let mut v___x_6056_: usize = 0;
    let mut v___x_6058_: u8 = 0;
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6063_: u8 = 0;
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6067_: u8 = 0;
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6046_ = lean_usize_dec_eq(v_i_6038_, v_stop_6039_);
                if v___x_6046_ == 0 {
                    v___x_6047_ = lean_array_uget_borrowed(v_as_6037_, v_i_6038_);
                    v_value_6048_ = crate::leanh::lean_ctor_get(v___x_6047_, 1);
                    v___x_6049_ = crate::leanh::lean_box((v_pu_6035_) as usize);
                    crate::leanh::lean_inc_ref(v_f_6036_);
                    v___x_6050_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_6050_, 0, v___x_6049_);
                    crate::leanh::lean_closure_set(v___x_6050_, 1, v_f_6036_);
                    crate::leanh::lean_inc_ref(v_value_6048_);
                    v___x_6051_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_6048_, v___x_6050_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_);
                    if crate::leanh::lean_obj_tag(v___x_6051_) == 0 {
                        v_a_6052_ = crate::leanh::lean_ctor_get(v___x_6051_, 0);
                        crate::leanh::lean_inc(v_a_6052_);
                        crate::leanh::lean_dec_ref_known(v___x_6051_, 1);
                        v___x_6058_ = (crate::leanh::lean_unbox(v_a_6052_) as u8);
                        crate::leanh::lean_dec(v_a_6052_);
                        if v___x_6058_ == 0 {
                            v_a_6054_ = v_b_6040_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_6047_);
                            v___x_6059_ = lean_array_push(v_b_6040_, v___x_6047_);
                            v_a_6054_ = v___x_6059_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_6040_);
                        crate::leanh::lean_dec_ref(v_f_6036_);
                        v_a_6060_ = crate::leanh::lean_ctor_get(v___x_6051_, 0);
                        v_isSharedCheck_6067_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6051_)) as u8;
                        if v_isSharedCheck_6067_ == 0 {
                            v___x_6062_ = v___x_6051_;
                            v_isShared_6063_ = v_isSharedCheck_6067_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6060_);
                            crate::leanh::lean_dec(v___x_6051_);
                            v___x_6062_ = crate::leanh::lean_box(0);
                            v_isShared_6063_ = v_isSharedCheck_6067_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6036_);
                    v___x_6068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6068_, 0, v_b_6040_);
                    return v___x_6068_;
                }
            }
            1 => {
                v___x_6055_ = 1usize;
                v___x_6056_ = lean_usize_add(v_i_6038_, v___x_6055_);
                v_i_6038_ = v___x_6056_;
                v_b_6040_ = v_a_6054_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_6063_ == 0 {
                    v___x_6065_ = v___x_6062_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6060_);
                    v___x_6065_ = v_reuseFailAlloc_6066_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(
    mut v_pu_6069_: *mut crate::leanh::LeanObject,
    mut v_f_6070_: *mut crate::leanh::LeanObject,
    mut v_as_6071_: *mut crate::leanh::LeanObject,
    mut v_i_6072_: *mut crate::leanh::LeanObject,
    mut v_stop_6073_: *mut crate::leanh::LeanObject,
    mut v_b_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
    mut v___y_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6080_: u8 = 0;
    let mut v_i_boxed_6081_: usize = 0;
    let mut v_stop_boxed_6082_: usize = 0;
    let mut v_res_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6080_ = (crate::leanh::lean_unbox(v_pu_6069_) as u8);
    v_i_boxed_6081_ = crate::leanh::lean_unbox_usize(v_i_6072_);
    crate::leanh::lean_dec(v_i_6072_);
    v_stop_boxed_6082_ = crate::leanh::lean_unbox_usize(v_stop_6073_);
    crate::leanh::lean_dec(v_stop_6073_);
    v_res_6083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_boxed_6080_, v_f_6070_, v_as_6071_, v_i_boxed_6081_, v_stop_boxed_6082_, v_b_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_);
    crate::leanh::lean_dec(v___y_6078_);
    crate::leanh::lean_dec_ref(v___y_6077_);
    crate::leanh::lean_dec(v___y_6076_);
    crate::leanh::lean_dec_ref(v___y_6075_);
    crate::leanh::lean_dec_ref(v_as_6071_);
    return v_res_6083_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByCases(
    mut v_pu_6084_: u8,
    mut v_f_6085_: *mut crate::leanh::LeanObject,
    mut v_a_6086_: *mut crate::leanh::LeanObject,
    mut v_a_6087_: *mut crate::leanh::LeanObject,
    mut v_a_6088_: *mut crate::leanh::LeanObject,
    mut v_a_6089_: *mut crate::leanh::LeanObject,
    mut v_a_6090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: u8 = 0;
    v___x_6092_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6093_ = lean_array_get_size(v_a_6086_);
    v___x_6094_ = l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0;
    v___x_6095_ = lean_nat_dec_lt(v___x_6092_, v___x_6093_);
    if v___x_6095_ == 0 {
        let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_6085_);
        v___x_6096_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6096_, 0, v___x_6094_);
        return v___x_6096_;
    } else {
        let mut v___x_6097_: u8 = 0;
        v___x_6097_ = lean_nat_dec_le(v___x_6093_, v___x_6093_);
        if v___x_6097_ == 0 {
            if v___x_6095_ == 0 {
                let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_6085_);
                v___x_6098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6098_, 0, v___x_6094_);
                return v___x_6098_;
            } else {
                let mut v___x_6099_: usize = 0;
                let mut v___x_6100_: usize = 0;
                let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6099_ = 0usize;
                v___x_6100_ = lean_usize_of_nat(v___x_6093_);
                v___x_6101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_6084_, v_f_6085_, v_a_6086_, v___x_6099_, v___x_6100_, v___x_6094_, v_a_6087_, v_a_6088_, v_a_6089_, v_a_6090_);
                return v___x_6101_;
            }
        } else {
            let mut v___x_6102_: usize = 0;
            let mut v___x_6103_: usize = 0;
            let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6102_ = 0usize;
            v___x_6103_ = lean_usize_of_nat(v___x_6093_);
            v___x_6104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_6084_, v_f_6085_, v_a_6086_, v___x_6102_, v___x_6103_, v___x_6094_, v_a_6087_, v_a_6088_, v_a_6089_, v_a_6090_);
            return v___x_6104_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(
    mut v_pu_6105_: *mut crate::leanh::LeanObject,
    mut v_f_6106_: *mut crate::leanh::LeanObject,
    mut v_a_6107_: *mut crate::leanh::LeanObject,
    mut v_a_6108_: *mut crate::leanh::LeanObject,
    mut v_a_6109_: *mut crate::leanh::LeanObject,
    mut v_a_6110_: *mut crate::leanh::LeanObject,
    mut v_a_6111_: *mut crate::leanh::LeanObject,
    mut v_a_6112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6113_: u8 = 0;
    let mut v_res_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6113_ = (crate::leanh::lean_unbox(v_pu_6105_) as u8);
    v_res_6114_ = l_Lean_Compiler_LCNF_Probe_filterByCases(
        v_pu_boxed_6113_,
        v_f_6106_,
        v_a_6107_,
        v_a_6108_,
        v_a_6109_,
        v_a_6110_,
        v_a_6111_,
    );
    crate::leanh::lean_dec(v_a_6111_);
    crate::leanh::lean_dec_ref(v_a_6110_);
    crate::leanh::lean_dec(v_a_6109_);
    crate::leanh::lean_dec_ref(v_a_6108_);
    crate::leanh::lean_dec_ref(v_a_6107_);
    return v_res_6114_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(
    mut v_pu_6115_: u8,
    mut v_f_6116_: *mut crate::leanh::LeanObject,
    mut v_a_6117_: *mut crate::leanh::LeanObject,
    mut v_a_6118_: *mut crate::leanh::LeanObject,
    mut v_a_6119_: *mut crate::leanh::LeanObject,
    mut v_a_6120_: *mut crate::leanh::LeanObject,
    mut v_a_6121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: u8 = 0;
    let mut v_decl_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: u8 = 0;
    let mut v_fvarId_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6145_: u8 = 0;
    let mut v_alts_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: u8 = 0;
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: usize = 0;
    let mut v___x_6159_: usize = 0;
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6161_: u8 = 0;
    let mut v_k_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: u8 = 0;
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_6117_) {
                0 => {
                    v_k_6123_ = crate::leanh::lean_ctor_get(v_a_6117_, 1);
                    crate::leanh::lean_inc_ref(v_k_6123_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 2);
                    v_a_6117_ = v_k_6123_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_6125_ = crate::leanh::lean_ctor_get(v_a_6117_, 0);
                    crate::leanh::lean_inc_ref(v_decl_6125_);
                    v_k_6126_ = crate::leanh::lean_ctor_get(v_a_6117_, 1);
                    crate::leanh::lean_inc_ref(v_k_6126_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 2);
                    v_value_6127_ = crate::leanh::lean_ctor_get(v_decl_6125_, 4);
                    crate::leanh::lean_inc_ref(v_value_6127_);
                    crate::leanh::lean_dec_ref(v_decl_6125_);
                    crate::leanh::lean_inc_ref(v_f_6116_);
                    v___x_6128_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_6115_, v_f_6116_, v_value_6127_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_);
                    if crate::leanh::lean_obj_tag(v___x_6128_) == 0 {
                        v_a_6129_ = crate::leanh::lean_ctor_get(v___x_6128_, 0);
                        crate::leanh::lean_inc(v_a_6129_);
                        v___x_6130_ = (crate::leanh::lean_unbox(v_a_6129_) as u8);
                        crate::leanh::lean_dec(v_a_6129_);
                        if v___x_6130_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6128_, 1);
                            v_a_6117_ = v_k_6126_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_6126_);
                            crate::leanh::lean_dec_ref(v_f_6116_);
                            return v___x_6128_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_6126_);
                        crate::leanh::lean_dec_ref(v_f_6116_);
                        return v___x_6128_;
                    }
                }
                2 => {
                    v_decl_6132_ = crate::leanh::lean_ctor_get(v_a_6117_, 0);
                    crate::leanh::lean_inc_ref(v_decl_6132_);
                    v_k_6133_ = crate::leanh::lean_ctor_get(v_a_6117_, 1);
                    crate::leanh::lean_inc_ref(v_k_6133_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 2);
                    v_value_6134_ = crate::leanh::lean_ctor_get(v_decl_6132_, 4);
                    crate::leanh::lean_inc_ref(v_value_6134_);
                    crate::leanh::lean_dec_ref(v_decl_6132_);
                    crate::leanh::lean_inc_ref(v_f_6116_);
                    v___x_6135_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_6115_, v_f_6116_, v_value_6134_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_);
                    if crate::leanh::lean_obj_tag(v___x_6135_) == 0 {
                        v_a_6136_ = crate::leanh::lean_ctor_get(v___x_6135_, 0);
                        crate::leanh::lean_inc(v_a_6136_);
                        v___x_6137_ = (crate::leanh::lean_unbox(v_a_6136_) as u8);
                        crate::leanh::lean_dec(v_a_6136_);
                        if v___x_6137_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6135_, 1);
                            v_a_6117_ = v_k_6133_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_6133_);
                            crate::leanh::lean_dec_ref(v_f_6116_);
                            return v___x_6135_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_6133_);
                        crate::leanh::lean_dec_ref(v_f_6116_);
                        return v___x_6135_;
                    }
                }
                3 => {
                    v_fvarId_6139_ = crate::leanh::lean_ctor_get(v_a_6117_, 0);
                    crate::leanh::lean_inc(v_fvarId_6139_);
                    v_args_6140_ = crate::leanh::lean_ctor_get(v_a_6117_, 1);
                    crate::leanh::lean_inc_ref(v_args_6140_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 2);
                    crate::leanh::lean_inc(v_a_6121_);
                    crate::leanh::lean_inc_ref(v_a_6120_);
                    crate::leanh::lean_inc(v_a_6119_);
                    crate::leanh::lean_inc_ref(v_a_6118_);
                    v___x_6141_ = crate::leanh::lean_apply_7(
                        v_f_6116_,
                        v_fvarId_6139_,
                        v_args_6140_,
                        v_a_6118_,
                        v_a_6119_,
                        v_a_6120_,
                        v_a_6121_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6141_;
                }
                4 => {
                    v_cases_6142_ = crate::leanh::lean_ctor_get(v_a_6117_, 0);
                    v_isSharedCheck_6161_ = (!crate::leanh::lean_is_exclusive(v_a_6117_)) as u8;
                    if v_isSharedCheck_6161_ == 0 {
                        v___x_6144_ = v_a_6117_;
                        v_isShared_6145_ = v_isSharedCheck_6161_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_6142_);
                        crate::leanh::lean_dec(v_a_6117_);
                        v___x_6144_ = crate::leanh::lean_box(0);
                        v_isShared_6145_ = v_isSharedCheck_6161_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_k_6162_ = crate::leanh::lean_ctor_get(v_a_6117_, 3);
                    crate::leanh::lean_inc_ref(v_k_6162_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 4);
                    v_a_6117_ = v_k_6162_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_6164_ = crate::leanh::lean_ctor_get(v_a_6117_, 3);
                    crate::leanh::lean_inc_ref(v_k_6164_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 4);
                    v_a_6117_ = v_k_6164_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_6166_ = crate::leanh::lean_ctor_get(v_a_6117_, 5);
                    crate::leanh::lean_inc_ref(v_k_6166_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 6);
                    v_a_6117_ = v_k_6166_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_6168_ = crate::leanh::lean_ctor_get(v_a_6117_, 2);
                    crate::leanh::lean_inc_ref(v_k_6168_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 3);
                    v_a_6117_ = v_k_6168_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_6170_ = crate::leanh::lean_ctor_get(v_a_6117_, 2);
                    crate::leanh::lean_inc_ref(v_k_6170_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 3);
                    v_a_6117_ = v_k_6170_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_6172_ = crate::leanh::lean_ctor_get(v_a_6117_, 3);
                    crate::leanh::lean_inc_ref(v_k_6172_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 4);
                    v_a_6117_ = v_k_6172_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_6174_ = crate::leanh::lean_ctor_get(v_a_6117_, 1);
                    crate::leanh::lean_inc_ref(v_k_6174_);
                    crate::leanh::lean_dec_ref_known(v_a_6117_, 2);
                    v_a_6117_ = v_k_6174_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_6117_);
                    crate::leanh::lean_dec_ref(v_f_6116_);
                    v___x_6176_ = 0;
                    v___x_6177_ = crate::leanh::lean_box((v___x_6176_) as usize);
                    v___x_6178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6178_, 0, v___x_6177_);
                    return v___x_6178_;
                }
            },
            1 => {
                v_alts_6146_ = crate::leanh::lean_ctor_get(v_cases_6142_, 3);
                crate::leanh::lean_inc_ref(v_alts_6146_);
                crate::leanh::lean_dec_ref(v_cases_6142_);
                v___x_6147_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6148_ = lean_array_get_size(v_alts_6146_);
                v___x_6149_ = lean_nat_dec_lt(v___x_6147_, v___x_6148_);
                if v___x_6149_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_6146_);
                    crate::leanh::lean_dec_ref(v_f_6116_);
                    v___x_6150_ = crate::leanh::lean_box((v___x_6149_) as usize);
                    if v_isShared_6145_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6144_, 0);
                        crate::leanh::lean_ctor_set(v___x_6144_, 0, v___x_6150_);
                        v___x_6152_ = v___x_6144_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6153_, 0, v___x_6150_);
                        v___x_6152_ = v_reuseFailAlloc_6153_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_6149_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_6146_);
                        crate::leanh::lean_dec_ref(v_f_6116_);
                        v___x_6154_ = crate::leanh::lean_box((v___x_6149_) as usize);
                        if v_isShared_6145_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6144_, 0);
                            crate::leanh::lean_ctor_set(v___x_6144_, 0, v___x_6154_);
                            v___x_6156_ = v___x_6144_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6157_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6157_, 0, v___x_6154_);
                            v___x_6156_ = v_reuseFailAlloc_6157_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6144_);
                        v___x_6158_ = 0usize;
                        v___x_6159_ = lean_usize_of_nat(v___x_6148_);
                        v___x_6160_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_6115_, v_f_6116_, v_alts_6146_, v___x_6158_, v___x_6159_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_);
                        crate::leanh::lean_dec_ref(v_alts_6146_);
                        return v___x_6160_;
                    }
                }
            }
            2 => {
                return v___x_6152_;
            }
            3 => {
                return v___x_6156_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(
    mut v_pu_6179_: u8,
    mut v_f_6180_: *mut crate::leanh::LeanObject,
    mut v_as_6181_: *mut crate::leanh::LeanObject,
    mut v_i_6182_: usize,
    mut v_stop_6183_: usize,
    mut v___y_6184_: *mut crate::leanh::LeanObject,
    mut v___y_6185_: *mut crate::leanh::LeanObject,
    mut v___y_6186_: *mut crate::leanh::LeanObject,
    mut v___y_6187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6189_: u8 = 0;
    let mut v___x_6190_: u8 = 0;
    let mut v___y_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6197_: u8 = 0;
    let mut v___x_6198_: u8 = 0;
    let mut v___x_6199_: usize = 0;
    let mut v___x_6200_: usize = 0;
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6206_: u8 = 0;
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: u8 = 0;
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6189_ = lean_usize_dec_eq(v_i_6182_, v_stop_6183_);
                if v___x_6189_ == 0 {
                    v___x_6190_ = 1;
                    v___x_6207_ = lean_array_uget_borrowed(v_as_6181_, v_i_6182_);
                    match crate::leanh::lean_obj_tag(v___x_6207_) {
                        0 => {
                            v_code_6208_ = crate::leanh::lean_ctor_get(v___x_6207_, 2);
                            crate::leanh::lean_inc_ref(v_code_6208_);
                            v___y_6192_ = v_code_6208_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_6209_ = crate::leanh::lean_ctor_get(v___x_6207_, 1);
                            crate::leanh::lean_inc_ref(v_code_6209_);
                            v___y_6192_ = v_code_6209_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_6210_ = crate::leanh::lean_ctor_get(v___x_6207_, 0);
                            crate::leanh::lean_inc_ref(v_code_6210_);
                            v___y_6192_ = v_code_6210_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6180_);
                    v___x_6211_ = 0;
                    v___x_6212_ = crate::leanh::lean_box((v___x_6211_) as usize);
                    v___x_6213_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6213_, 0, v___x_6212_);
                    return v___x_6213_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_6180_);
                v___x_6193_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_6179_, v_f_6180_, v___y_6192_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_);
                if crate::leanh::lean_obj_tag(v___x_6193_) == 0 {
                    v_a_6194_ = crate::leanh::lean_ctor_get(v___x_6193_, 0);
                    v_isSharedCheck_6206_ = (!crate::leanh::lean_is_exclusive(v___x_6193_)) as u8;
                    if v_isSharedCheck_6206_ == 0 {
                        v___x_6196_ = v___x_6193_;
                        v_isShared_6197_ = v_isSharedCheck_6206_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6194_);
                        crate::leanh::lean_dec(v___x_6193_);
                        v___x_6196_ = crate::leanh::lean_box(0);
                        v_isShared_6197_ = v_isSharedCheck_6206_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6180_);
                    return v___x_6193_;
                }
            }
            2 => {
                v___x_6198_ = (crate::leanh::lean_unbox(v_a_6194_) as u8);
                crate::leanh::lean_dec(v_a_6194_);
                if v___x_6198_ == 0 {
                    crate::leanh::lean_del_object(v___x_6196_);
                    v___x_6199_ = 1usize;
                    v___x_6200_ = lean_usize_add(v_i_6182_, v___x_6199_);
                    v_i_6182_ = v___x_6200_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_6180_);
                    v___x_6202_ = crate::leanh::lean_box((v___x_6190_) as usize);
                    if v_isShared_6197_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6196_, 0, v___x_6202_);
                        v___x_6204_ = v___x_6196_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6205_, 0, v___x_6202_);
                        v___x_6204_ = v_reuseFailAlloc_6205_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(
    mut v_pu_6214_: *mut crate::leanh::LeanObject,
    mut v_f_6215_: *mut crate::leanh::LeanObject,
    mut v_as_6216_: *mut crate::leanh::LeanObject,
    mut v_i_6217_: *mut crate::leanh::LeanObject,
    mut v_stop_6218_: *mut crate::leanh::LeanObject,
    mut v___y_6219_: *mut crate::leanh::LeanObject,
    mut v___y_6220_: *mut crate::leanh::LeanObject,
    mut v___y_6221_: *mut crate::leanh::LeanObject,
    mut v___y_6222_: *mut crate::leanh::LeanObject,
    mut v___y_6223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6224_: u8 = 0;
    let mut v_i_boxed_6225_: usize = 0;
    let mut v_stop_boxed_6226_: usize = 0;
    let mut v_res_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6224_ = (crate::leanh::lean_unbox(v_pu_6214_) as u8);
    v_i_boxed_6225_ = crate::leanh::lean_unbox_usize(v_i_6217_);
    crate::leanh::lean_dec(v_i_6217_);
    v_stop_boxed_6226_ = crate::leanh::lean_unbox_usize(v_stop_6218_);
    crate::leanh::lean_dec(v_stop_6218_);
    v_res_6227_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_boxed_6224_, v_f_6215_, v_as_6216_, v_i_boxed_6225_, v_stop_boxed_6226_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
    crate::leanh::lean_dec(v___y_6222_);
    crate::leanh::lean_dec_ref(v___y_6221_);
    crate::leanh::lean_dec(v___y_6220_);
    crate::leanh::lean_dec_ref(v___y_6219_);
    crate::leanh::lean_dec_ref(v_as_6216_);
    return v_res_6227_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(
    mut v_pu_6228_: *mut crate::leanh::LeanObject,
    mut v_f_6229_: *mut crate::leanh::LeanObject,
    mut v_a_6230_: *mut crate::leanh::LeanObject,
    mut v_a_6231_: *mut crate::leanh::LeanObject,
    mut v_a_6232_: *mut crate::leanh::LeanObject,
    mut v_a_6233_: *mut crate::leanh::LeanObject,
    mut v_a_6234_: *mut crate::leanh::LeanObject,
    mut v_a_6235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6236_: u8 = 0;
    let mut v_res_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6236_ = (crate::leanh::lean_unbox(v_pu_6228_) as u8);
    v_res_6237_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(
        v_pu_boxed_6236_,
        v_f_6229_,
        v_a_6230_,
        v_a_6231_,
        v_a_6232_,
        v_a_6233_,
        v_a_6234_,
    );
    crate::leanh::lean_dec(v_a_6234_);
    crate::leanh::lean_dec_ref(v_a_6233_);
    crate::leanh::lean_dec(v_a_6232_);
    crate::leanh::lean_dec_ref(v_a_6231_);
    return v_res_6237_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(
    mut v_pu_6238_: u8,
    mut v_f_6239_: *mut crate::leanh::LeanObject,
    mut v_as_6240_: *mut crate::leanh::LeanObject,
    mut v_i_6241_: usize,
    mut v_stop_6242_: usize,
    mut v_b_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
    mut v___y_6247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6249_: u8 = 0;
    let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: usize = 0;
    let mut v___x_6259_: usize = 0;
    let mut v___x_6261_: u8 = 0;
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6266_: u8 = 0;
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6270_: u8 = 0;
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6249_ = lean_usize_dec_eq(v_i_6241_, v_stop_6242_);
                if v___x_6249_ == 0 {
                    v___x_6250_ = lean_array_uget_borrowed(v_as_6240_, v_i_6241_);
                    v_value_6251_ = crate::leanh::lean_ctor_get(v___x_6250_, 1);
                    v___x_6252_ = crate::leanh::lean_box((v_pu_6238_) as usize);
                    crate::leanh::lean_inc_ref(v_f_6239_);
                    v___x_6253_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_6253_, 0, v___x_6252_);
                    crate::leanh::lean_closure_set(v___x_6253_, 1, v_f_6239_);
                    crate::leanh::lean_inc_ref(v_value_6251_);
                    v___x_6254_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_6251_, v___x_6253_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_);
                    if crate::leanh::lean_obj_tag(v___x_6254_) == 0 {
                        v_a_6255_ = crate::leanh::lean_ctor_get(v___x_6254_, 0);
                        crate::leanh::lean_inc(v_a_6255_);
                        crate::leanh::lean_dec_ref_known(v___x_6254_, 1);
                        v___x_6261_ = (crate::leanh::lean_unbox(v_a_6255_) as u8);
                        crate::leanh::lean_dec(v_a_6255_);
                        if v___x_6261_ == 0 {
                            v_a_6257_ = v_b_6243_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_6250_);
                            v___x_6262_ = lean_array_push(v_b_6243_, v___x_6250_);
                            v_a_6257_ = v___x_6262_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_6243_);
                        crate::leanh::lean_dec_ref(v_f_6239_);
                        v_a_6263_ = crate::leanh::lean_ctor_get(v___x_6254_, 0);
                        v_isSharedCheck_6270_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6254_)) as u8;
                        if v_isSharedCheck_6270_ == 0 {
                            v___x_6265_ = v___x_6254_;
                            v_isShared_6266_ = v_isSharedCheck_6270_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6263_);
                            crate::leanh::lean_dec(v___x_6254_);
                            v___x_6265_ = crate::leanh::lean_box(0);
                            v_isShared_6266_ = v_isSharedCheck_6270_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6239_);
                    v___x_6271_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6271_, 0, v_b_6243_);
                    return v___x_6271_;
                }
            }
            1 => {
                v___x_6258_ = 1usize;
                v___x_6259_ = lean_usize_add(v_i_6241_, v___x_6258_);
                v_i_6241_ = v___x_6259_;
                v_b_6243_ = v_a_6257_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_6266_ == 0 {
                    v___x_6268_ = v___x_6265_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_a_6263_);
                    v___x_6268_ = v_reuseFailAlloc_6269_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(
    mut v_pu_6272_: *mut crate::leanh::LeanObject,
    mut v_f_6273_: *mut crate::leanh::LeanObject,
    mut v_as_6274_: *mut crate::leanh::LeanObject,
    mut v_i_6275_: *mut crate::leanh::LeanObject,
    mut v_stop_6276_: *mut crate::leanh::LeanObject,
    mut v_b_6277_: *mut crate::leanh::LeanObject,
    mut v___y_6278_: *mut crate::leanh::LeanObject,
    mut v___y_6279_: *mut crate::leanh::LeanObject,
    mut v___y_6280_: *mut crate::leanh::LeanObject,
    mut v___y_6281_: *mut crate::leanh::LeanObject,
    mut v___y_6282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6283_: u8 = 0;
    let mut v_i_boxed_6284_: usize = 0;
    let mut v_stop_boxed_6285_: usize = 0;
    let mut v_res_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6283_ = (crate::leanh::lean_unbox(v_pu_6272_) as u8);
    v_i_boxed_6284_ = crate::leanh::lean_unbox_usize(v_i_6275_);
    crate::leanh::lean_dec(v_i_6275_);
    v_stop_boxed_6285_ = crate::leanh::lean_unbox_usize(v_stop_6276_);
    crate::leanh::lean_dec(v_stop_6276_);
    v_res_6286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_boxed_6283_, v_f_6273_, v_as_6274_, v_i_boxed_6284_, v_stop_boxed_6285_, v_b_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_);
    crate::leanh::lean_dec(v___y_6281_);
    crate::leanh::lean_dec_ref(v___y_6280_);
    crate::leanh::lean_dec(v___y_6279_);
    crate::leanh::lean_dec_ref(v___y_6278_);
    crate::leanh::lean_dec_ref(v_as_6274_);
    return v_res_6286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByJmp(
    mut v_pu_6287_: u8,
    mut v_f_6288_: *mut crate::leanh::LeanObject,
    mut v_a_6289_: *mut crate::leanh::LeanObject,
    mut v_a_6290_: *mut crate::leanh::LeanObject,
    mut v_a_6291_: *mut crate::leanh::LeanObject,
    mut v_a_6292_: *mut crate::leanh::LeanObject,
    mut v_a_6293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: u8 = 0;
    v___x_6295_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6296_ = lean_array_get_size(v_a_6289_);
    v___x_6297_ = l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0;
    v___x_6298_ = lean_nat_dec_lt(v___x_6295_, v___x_6296_);
    if v___x_6298_ == 0 {
        let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_6288_);
        v___x_6299_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6299_, 0, v___x_6297_);
        return v___x_6299_;
    } else {
        let mut v___x_6300_: u8 = 0;
        v___x_6300_ = lean_nat_dec_le(v___x_6296_, v___x_6296_);
        if v___x_6300_ == 0 {
            if v___x_6298_ == 0 {
                let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_6288_);
                v___x_6301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6301_, 0, v___x_6297_);
                return v___x_6301_;
            } else {
                let mut v___x_6302_: usize = 0;
                let mut v___x_6303_: usize = 0;
                let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6302_ = 0usize;
                v___x_6303_ = lean_usize_of_nat(v___x_6296_);
                v___x_6304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_6287_, v_f_6288_, v_a_6289_, v___x_6302_, v___x_6303_, v___x_6297_, v_a_6290_, v_a_6291_, v_a_6292_, v_a_6293_);
                return v___x_6304_;
            }
        } else {
            let mut v___x_6305_: usize = 0;
            let mut v___x_6306_: usize = 0;
            let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6305_ = 0usize;
            v___x_6306_ = lean_usize_of_nat(v___x_6296_);
            v___x_6307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_6287_, v_f_6288_, v_a_6289_, v___x_6305_, v___x_6306_, v___x_6297_, v_a_6290_, v_a_6291_, v_a_6292_, v_a_6293_);
            return v___x_6307_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(
    mut v_pu_6308_: *mut crate::leanh::LeanObject,
    mut v_f_6309_: *mut crate::leanh::LeanObject,
    mut v_a_6310_: *mut crate::leanh::LeanObject,
    mut v_a_6311_: *mut crate::leanh::LeanObject,
    mut v_a_6312_: *mut crate::leanh::LeanObject,
    mut v_a_6313_: *mut crate::leanh::LeanObject,
    mut v_a_6314_: *mut crate::leanh::LeanObject,
    mut v_a_6315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6316_: u8 = 0;
    let mut v_res_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6316_ = (crate::leanh::lean_unbox(v_pu_6308_) as u8);
    v_res_6317_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(
        v_pu_boxed_6316_,
        v_f_6309_,
        v_a_6310_,
        v_a_6311_,
        v_a_6312_,
        v_a_6313_,
        v_a_6314_,
    );
    crate::leanh::lean_dec(v_a_6314_);
    crate::leanh::lean_dec_ref(v_a_6313_);
    crate::leanh::lean_dec(v_a_6312_);
    crate::leanh::lean_dec_ref(v_a_6311_);
    crate::leanh::lean_dec_ref(v_a_6310_);
    return v_res_6317_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(
    mut v_pu_6318_: u8,
    mut v_f_6319_: *mut crate::leanh::LeanObject,
    mut v_a_6320_: *mut crate::leanh::LeanObject,
    mut v_a_6321_: *mut crate::leanh::LeanObject,
    mut v_a_6322_: *mut crate::leanh::LeanObject,
    mut v_a_6323_: *mut crate::leanh::LeanObject,
    mut v_a_6324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: u8 = 0;
    let mut v_decl_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: u8 = 0;
    let mut v_cases_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6345_: u8 = 0;
    let mut v_alts_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: u8 = 0;
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: usize = 0;
    let mut v___x_6359_: usize = 0;
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6361_: u8 = 0;
    let mut v_fvarId_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: u8 = 0;
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_6320_) {
                0 => {
                    v_k_6326_ = crate::leanh::lean_ctor_get(v_a_6320_, 1);
                    crate::leanh::lean_inc_ref(v_k_6326_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 2);
                    v_a_6320_ = v_k_6326_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_6328_ = crate::leanh::lean_ctor_get(v_a_6320_, 0);
                    crate::leanh::lean_inc_ref(v_decl_6328_);
                    v_k_6329_ = crate::leanh::lean_ctor_get(v_a_6320_, 1);
                    crate::leanh::lean_inc_ref(v_k_6329_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 2);
                    v_value_6330_ = crate::leanh::lean_ctor_get(v_decl_6328_, 4);
                    crate::leanh::lean_inc_ref(v_value_6330_);
                    crate::leanh::lean_dec_ref(v_decl_6328_);
                    crate::leanh::lean_inc_ref(v_f_6319_);
                    v___x_6331_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_6318_, v_f_6319_, v_value_6330_, v_a_6321_, v_a_6322_, v_a_6323_, v_a_6324_);
                    if crate::leanh::lean_obj_tag(v___x_6331_) == 0 {
                        v_a_6332_ = crate::leanh::lean_ctor_get(v___x_6331_, 0);
                        crate::leanh::lean_inc(v_a_6332_);
                        v___x_6333_ = (crate::leanh::lean_unbox(v_a_6332_) as u8);
                        crate::leanh::lean_dec(v_a_6332_);
                        if v___x_6333_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6331_, 1);
                            v_a_6320_ = v_k_6329_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_6329_);
                            crate::leanh::lean_dec_ref(v_f_6319_);
                            return v___x_6331_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_6329_);
                        crate::leanh::lean_dec_ref(v_f_6319_);
                        return v___x_6331_;
                    }
                }
                2 => {
                    v_decl_6335_ = crate::leanh::lean_ctor_get(v_a_6320_, 0);
                    crate::leanh::lean_inc_ref(v_decl_6335_);
                    v_k_6336_ = crate::leanh::lean_ctor_get(v_a_6320_, 1);
                    crate::leanh::lean_inc_ref(v_k_6336_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 2);
                    v_value_6337_ = crate::leanh::lean_ctor_get(v_decl_6335_, 4);
                    crate::leanh::lean_inc_ref(v_value_6337_);
                    crate::leanh::lean_dec_ref(v_decl_6335_);
                    crate::leanh::lean_inc_ref(v_f_6319_);
                    v___x_6338_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_6318_, v_f_6319_, v_value_6337_, v_a_6321_, v_a_6322_, v_a_6323_, v_a_6324_);
                    if crate::leanh::lean_obj_tag(v___x_6338_) == 0 {
                        v_a_6339_ = crate::leanh::lean_ctor_get(v___x_6338_, 0);
                        crate::leanh::lean_inc(v_a_6339_);
                        v___x_6340_ = (crate::leanh::lean_unbox(v_a_6339_) as u8);
                        crate::leanh::lean_dec(v_a_6339_);
                        if v___x_6340_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6338_, 1);
                            v_a_6320_ = v_k_6336_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_6336_);
                            crate::leanh::lean_dec_ref(v_f_6319_);
                            return v___x_6338_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_6336_);
                        crate::leanh::lean_dec_ref(v_f_6319_);
                        return v___x_6338_;
                    }
                }
                4 => {
                    v_cases_6342_ = crate::leanh::lean_ctor_get(v_a_6320_, 0);
                    v_isSharedCheck_6361_ = (!crate::leanh::lean_is_exclusive(v_a_6320_)) as u8;
                    if v_isSharedCheck_6361_ == 0 {
                        v___x_6344_ = v_a_6320_;
                        v_isShared_6345_ = v_isSharedCheck_6361_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_6342_);
                        crate::leanh::lean_dec(v_a_6320_);
                        v___x_6344_ = crate::leanh::lean_box(0);
                        v_isShared_6345_ = v_isSharedCheck_6361_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_6362_ = crate::leanh::lean_ctor_get(v_a_6320_, 0);
                    crate::leanh::lean_inc(v_fvarId_6362_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 1);
                    crate::leanh::lean_inc(v_a_6324_);
                    crate::leanh::lean_inc_ref(v_a_6323_);
                    crate::leanh::lean_inc(v_a_6322_);
                    crate::leanh::lean_inc_ref(v_a_6321_);
                    v___x_6363_ = crate::leanh::lean_apply_6(
                        v_f_6319_,
                        v_fvarId_6362_,
                        v_a_6321_,
                        v_a_6322_,
                        v_a_6323_,
                        v_a_6324_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6363_;
                }
                7 => {
                    v_k_6364_ = crate::leanh::lean_ctor_get(v_a_6320_, 3);
                    crate::leanh::lean_inc_ref(v_k_6364_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 4);
                    v_a_6320_ = v_k_6364_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_6366_ = crate::leanh::lean_ctor_get(v_a_6320_, 3);
                    crate::leanh::lean_inc_ref(v_k_6366_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 4);
                    v_a_6320_ = v_k_6366_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_6368_ = crate::leanh::lean_ctor_get(v_a_6320_, 5);
                    crate::leanh::lean_inc_ref(v_k_6368_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 6);
                    v_a_6320_ = v_k_6368_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_6370_ = crate::leanh::lean_ctor_get(v_a_6320_, 2);
                    crate::leanh::lean_inc_ref(v_k_6370_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 3);
                    v_a_6320_ = v_k_6370_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_6372_ = crate::leanh::lean_ctor_get(v_a_6320_, 2);
                    crate::leanh::lean_inc_ref(v_k_6372_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 3);
                    v_a_6320_ = v_k_6372_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_6374_ = crate::leanh::lean_ctor_get(v_a_6320_, 3);
                    crate::leanh::lean_inc_ref(v_k_6374_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 4);
                    v_a_6320_ = v_k_6374_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_6376_ = crate::leanh::lean_ctor_get(v_a_6320_, 1);
                    crate::leanh::lean_inc_ref(v_k_6376_);
                    crate::leanh::lean_dec_ref_known(v_a_6320_, 2);
                    v_a_6320_ = v_k_6376_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_6320_);
                    crate::leanh::lean_dec_ref(v_f_6319_);
                    v___x_6378_ = 0;
                    v___x_6379_ = crate::leanh::lean_box((v___x_6378_) as usize);
                    v___x_6380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6380_, 0, v___x_6379_);
                    return v___x_6380_;
                }
            },
            1 => {
                v_alts_6346_ = crate::leanh::lean_ctor_get(v_cases_6342_, 3);
                crate::leanh::lean_inc_ref(v_alts_6346_);
                crate::leanh::lean_dec_ref(v_cases_6342_);
                v___x_6347_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6348_ = lean_array_get_size(v_alts_6346_);
                v___x_6349_ = lean_nat_dec_lt(v___x_6347_, v___x_6348_);
                if v___x_6349_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_6346_);
                    crate::leanh::lean_dec_ref(v_f_6319_);
                    v___x_6350_ = crate::leanh::lean_box((v___x_6349_) as usize);
                    if v_isShared_6345_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6344_, 0);
                        crate::leanh::lean_ctor_set(v___x_6344_, 0, v___x_6350_);
                        v___x_6352_ = v___x_6344_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6353_, 0, v___x_6350_);
                        v___x_6352_ = v_reuseFailAlloc_6353_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_6349_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_6346_);
                        crate::leanh::lean_dec_ref(v_f_6319_);
                        v___x_6354_ = crate::leanh::lean_box((v___x_6349_) as usize);
                        if v_isShared_6345_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6344_, 0);
                            crate::leanh::lean_ctor_set(v___x_6344_, 0, v___x_6354_);
                            v___x_6356_ = v___x_6344_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6357_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6357_, 0, v___x_6354_);
                            v___x_6356_ = v_reuseFailAlloc_6357_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6344_);
                        v___x_6358_ = 0usize;
                        v___x_6359_ = lean_usize_of_nat(v___x_6348_);
                        v___x_6360_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_6318_, v_f_6319_, v_alts_6346_, v___x_6358_, v___x_6359_, v_a_6321_, v_a_6322_, v_a_6323_, v_a_6324_);
                        crate::leanh::lean_dec_ref(v_alts_6346_);
                        return v___x_6360_;
                    }
                }
            }
            2 => {
                return v___x_6352_;
            }
            3 => {
                return v___x_6356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(
    mut v_pu_6381_: u8,
    mut v_f_6382_: *mut crate::leanh::LeanObject,
    mut v_as_6383_: *mut crate::leanh::LeanObject,
    mut v_i_6384_: usize,
    mut v_stop_6385_: usize,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6391_: u8 = 0;
    let mut v___x_6392_: u8 = 0;
    let mut v___y_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6399_: u8 = 0;
    let mut v___x_6400_: u8 = 0;
    let mut v___x_6401_: usize = 0;
    let mut v___x_6402_: usize = 0;
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6408_: u8 = 0;
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: u8 = 0;
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6391_ = lean_usize_dec_eq(v_i_6384_, v_stop_6385_);
                if v___x_6391_ == 0 {
                    v___x_6392_ = 1;
                    v___x_6409_ = lean_array_uget_borrowed(v_as_6383_, v_i_6384_);
                    match crate::leanh::lean_obj_tag(v___x_6409_) {
                        0 => {
                            v_code_6410_ = crate::leanh::lean_ctor_get(v___x_6409_, 2);
                            crate::leanh::lean_inc_ref(v_code_6410_);
                            v___y_6394_ = v_code_6410_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_6411_ = crate::leanh::lean_ctor_get(v___x_6409_, 1);
                            crate::leanh::lean_inc_ref(v_code_6411_);
                            v___y_6394_ = v_code_6411_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_6412_ = crate::leanh::lean_ctor_get(v___x_6409_, 0);
                            crate::leanh::lean_inc_ref(v_code_6412_);
                            v___y_6394_ = v_code_6412_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6382_);
                    v___x_6413_ = 0;
                    v___x_6414_ = crate::leanh::lean_box((v___x_6413_) as usize);
                    v___x_6415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6415_, 0, v___x_6414_);
                    return v___x_6415_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_6382_);
                v___x_6395_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_6381_, v_f_6382_, v___y_6394_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_);
                if crate::leanh::lean_obj_tag(v___x_6395_) == 0 {
                    v_a_6396_ = crate::leanh::lean_ctor_get(v___x_6395_, 0);
                    v_isSharedCheck_6408_ = (!crate::leanh::lean_is_exclusive(v___x_6395_)) as u8;
                    if v_isSharedCheck_6408_ == 0 {
                        v___x_6398_ = v___x_6395_;
                        v_isShared_6399_ = v_isSharedCheck_6408_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6396_);
                        crate::leanh::lean_dec(v___x_6395_);
                        v___x_6398_ = crate::leanh::lean_box(0);
                        v_isShared_6399_ = v_isSharedCheck_6408_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6382_);
                    return v___x_6395_;
                }
            }
            2 => {
                v___x_6400_ = (crate::leanh::lean_unbox(v_a_6396_) as u8);
                crate::leanh::lean_dec(v_a_6396_);
                if v___x_6400_ == 0 {
                    crate::leanh::lean_del_object(v___x_6398_);
                    v___x_6401_ = 1usize;
                    v___x_6402_ = lean_usize_add(v_i_6384_, v___x_6401_);
                    v_i_6384_ = v___x_6402_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_6382_);
                    v___x_6404_ = crate::leanh::lean_box((v___x_6392_) as usize);
                    if v_isShared_6399_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6398_, 0, v___x_6404_);
                        v___x_6406_ = v___x_6398_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6407_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6407_, 0, v___x_6404_);
                        v___x_6406_ = v_reuseFailAlloc_6407_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(
    mut v_pu_6416_: *mut crate::leanh::LeanObject,
    mut v_f_6417_: *mut crate::leanh::LeanObject,
    mut v_as_6418_: *mut crate::leanh::LeanObject,
    mut v_i_6419_: *mut crate::leanh::LeanObject,
    mut v_stop_6420_: *mut crate::leanh::LeanObject,
    mut v___y_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
    mut v___y_6423_: *mut crate::leanh::LeanObject,
    mut v___y_6424_: *mut crate::leanh::LeanObject,
    mut v___y_6425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6426_: u8 = 0;
    let mut v_i_boxed_6427_: usize = 0;
    let mut v_stop_boxed_6428_: usize = 0;
    let mut v_res_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6426_ = (crate::leanh::lean_unbox(v_pu_6416_) as u8);
    v_i_boxed_6427_ = crate::leanh::lean_unbox_usize(v_i_6419_);
    crate::leanh::lean_dec(v_i_6419_);
    v_stop_boxed_6428_ = crate::leanh::lean_unbox_usize(v_stop_6420_);
    crate::leanh::lean_dec(v_stop_6420_);
    v_res_6429_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_boxed_6426_, v_f_6417_, v_as_6418_, v_i_boxed_6427_, v_stop_boxed_6428_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_);
    crate::leanh::lean_dec(v___y_6424_);
    crate::leanh::lean_dec_ref(v___y_6423_);
    crate::leanh::lean_dec(v___y_6422_);
    crate::leanh::lean_dec_ref(v___y_6421_);
    crate::leanh::lean_dec_ref(v_as_6418_);
    return v_res_6429_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(
    mut v_pu_6430_: *mut crate::leanh::LeanObject,
    mut v_f_6431_: *mut crate::leanh::LeanObject,
    mut v_a_6432_: *mut crate::leanh::LeanObject,
    mut v_a_6433_: *mut crate::leanh::LeanObject,
    mut v_a_6434_: *mut crate::leanh::LeanObject,
    mut v_a_6435_: *mut crate::leanh::LeanObject,
    mut v_a_6436_: *mut crate::leanh::LeanObject,
    mut v_a_6437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6438_: u8 = 0;
    let mut v_res_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6438_ = (crate::leanh::lean_unbox(v_pu_6430_) as u8);
    v_res_6439_ =
        l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(
            v_pu_boxed_6438_,
            v_f_6431_,
            v_a_6432_,
            v_a_6433_,
            v_a_6434_,
            v_a_6435_,
            v_a_6436_,
        );
    crate::leanh::lean_dec(v_a_6436_);
    crate::leanh::lean_dec_ref(v_a_6435_);
    crate::leanh::lean_dec(v_a_6434_);
    crate::leanh::lean_dec_ref(v_a_6433_);
    return v_res_6439_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(
    mut v_pu_6440_: u8,
    mut v_f_6441_: *mut crate::leanh::LeanObject,
    mut v_as_6442_: *mut crate::leanh::LeanObject,
    mut v_i_6443_: usize,
    mut v_stop_6444_: usize,
    mut v_b_6445_: *mut crate::leanh::LeanObject,
    mut v___y_6446_: *mut crate::leanh::LeanObject,
    mut v___y_6447_: *mut crate::leanh::LeanObject,
    mut v___y_6448_: *mut crate::leanh::LeanObject,
    mut v___y_6449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6451_: u8 = 0;
    let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: usize = 0;
    let mut v___x_6461_: usize = 0;
    let mut v___x_6463_: u8 = 0;
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6468_: u8 = 0;
    let mut v___x_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6472_: u8 = 0;
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6451_ = lean_usize_dec_eq(v_i_6443_, v_stop_6444_);
                if v___x_6451_ == 0 {
                    v___x_6452_ = lean_array_uget_borrowed(v_as_6442_, v_i_6443_);
                    v_value_6453_ = crate::leanh::lean_ctor_get(v___x_6452_, 1);
                    v___x_6454_ = crate::leanh::lean_box((v_pu_6440_) as usize);
                    crate::leanh::lean_inc_ref(v_f_6441_);
                    v___x_6455_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_6455_, 0, v___x_6454_);
                    crate::leanh::lean_closure_set(v___x_6455_, 1, v_f_6441_);
                    crate::leanh::lean_inc_ref(v_value_6453_);
                    v___x_6456_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_6453_, v___x_6455_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_);
                    if crate::leanh::lean_obj_tag(v___x_6456_) == 0 {
                        v_a_6457_ = crate::leanh::lean_ctor_get(v___x_6456_, 0);
                        crate::leanh::lean_inc(v_a_6457_);
                        crate::leanh::lean_dec_ref_known(v___x_6456_, 1);
                        v___x_6463_ = (crate::leanh::lean_unbox(v_a_6457_) as u8);
                        crate::leanh::lean_dec(v_a_6457_);
                        if v___x_6463_ == 0 {
                            v_a_6459_ = v_b_6445_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_6452_);
                            v___x_6464_ = lean_array_push(v_b_6445_, v___x_6452_);
                            v_a_6459_ = v___x_6464_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_6445_);
                        crate::leanh::lean_dec_ref(v_f_6441_);
                        v_a_6465_ = crate::leanh::lean_ctor_get(v___x_6456_, 0);
                        v_isSharedCheck_6472_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6456_)) as u8;
                        if v_isSharedCheck_6472_ == 0 {
                            v___x_6467_ = v___x_6456_;
                            v_isShared_6468_ = v_isSharedCheck_6472_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6465_);
                            crate::leanh::lean_dec(v___x_6456_);
                            v___x_6467_ = crate::leanh::lean_box(0);
                            v_isShared_6468_ = v_isSharedCheck_6472_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6441_);
                    v___x_6473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6473_, 0, v_b_6445_);
                    return v___x_6473_;
                }
            }
            1 => {
                v___x_6460_ = 1usize;
                v___x_6461_ = lean_usize_add(v_i_6443_, v___x_6460_);
                v_i_6443_ = v___x_6461_;
                v_b_6445_ = v_a_6459_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_6468_ == 0 {
                    v___x_6470_ = v___x_6467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6471_, 0, v_a_6465_);
                    v___x_6470_ = v_reuseFailAlloc_6471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(
    mut v_pu_6474_: *mut crate::leanh::LeanObject,
    mut v_f_6475_: *mut crate::leanh::LeanObject,
    mut v_as_6476_: *mut crate::leanh::LeanObject,
    mut v_i_6477_: *mut crate::leanh::LeanObject,
    mut v_stop_6478_: *mut crate::leanh::LeanObject,
    mut v_b_6479_: *mut crate::leanh::LeanObject,
    mut v___y_6480_: *mut crate::leanh::LeanObject,
    mut v___y_6481_: *mut crate::leanh::LeanObject,
    mut v___y_6482_: *mut crate::leanh::LeanObject,
    mut v___y_6483_: *mut crate::leanh::LeanObject,
    mut v___y_6484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6485_: u8 = 0;
    let mut v_i_boxed_6486_: usize = 0;
    let mut v_stop_boxed_6487_: usize = 0;
    let mut v_res_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6485_ = (crate::leanh::lean_unbox(v_pu_6474_) as u8);
    v_i_boxed_6486_ = crate::leanh::lean_unbox_usize(v_i_6477_);
    crate::leanh::lean_dec(v_i_6477_);
    v_stop_boxed_6487_ = crate::leanh::lean_unbox_usize(v_stop_6478_);
    crate::leanh::lean_dec(v_stop_6478_);
    v_res_6488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_boxed_6485_, v_f_6475_, v_as_6476_, v_i_boxed_6486_, v_stop_boxed_6487_, v_b_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_);
    crate::leanh::lean_dec(v___y_6483_);
    crate::leanh::lean_dec_ref(v___y_6482_);
    crate::leanh::lean_dec(v___y_6481_);
    crate::leanh::lean_dec_ref(v___y_6480_);
    crate::leanh::lean_dec_ref(v_as_6476_);
    return v_res_6488_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByReturn(
    mut v_pu_6489_: u8,
    mut v_f_6490_: *mut crate::leanh::LeanObject,
    mut v_a_6491_: *mut crate::leanh::LeanObject,
    mut v_a_6492_: *mut crate::leanh::LeanObject,
    mut v_a_6493_: *mut crate::leanh::LeanObject,
    mut v_a_6494_: *mut crate::leanh::LeanObject,
    mut v_a_6495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: u8 = 0;
    v___x_6497_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6498_ = lean_array_get_size(v_a_6491_);
    v___x_6499_ = l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0;
    v___x_6500_ = lean_nat_dec_lt(v___x_6497_, v___x_6498_);
    if v___x_6500_ == 0 {
        let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_6490_);
        v___x_6501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6501_, 0, v___x_6499_);
        return v___x_6501_;
    } else {
        let mut v___x_6502_: u8 = 0;
        v___x_6502_ = lean_nat_dec_le(v___x_6498_, v___x_6498_);
        if v___x_6502_ == 0 {
            if v___x_6500_ == 0 {
                let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_6490_);
                v___x_6503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6503_, 0, v___x_6499_);
                return v___x_6503_;
            } else {
                let mut v___x_6504_: usize = 0;
                let mut v___x_6505_: usize = 0;
                let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6504_ = 0usize;
                v___x_6505_ = lean_usize_of_nat(v___x_6498_);
                v___x_6506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_6489_, v_f_6490_, v_a_6491_, v___x_6504_, v___x_6505_, v___x_6499_, v_a_6492_, v_a_6493_, v_a_6494_, v_a_6495_);
                return v___x_6506_;
            }
        } else {
            let mut v___x_6507_: usize = 0;
            let mut v___x_6508_: usize = 0;
            let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6507_ = 0usize;
            v___x_6508_ = lean_usize_of_nat(v___x_6498_);
            v___x_6509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_6489_, v_f_6490_, v_a_6491_, v___x_6507_, v___x_6508_, v___x_6499_, v_a_6492_, v_a_6493_, v_a_6494_, v_a_6495_);
            return v___x_6509_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(
    mut v_pu_6510_: *mut crate::leanh::LeanObject,
    mut v_f_6511_: *mut crate::leanh::LeanObject,
    mut v_a_6512_: *mut crate::leanh::LeanObject,
    mut v_a_6513_: *mut crate::leanh::LeanObject,
    mut v_a_6514_: *mut crate::leanh::LeanObject,
    mut v_a_6515_: *mut crate::leanh::LeanObject,
    mut v_a_6516_: *mut crate::leanh::LeanObject,
    mut v_a_6517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6518_: u8 = 0;
    let mut v_res_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6518_ = (crate::leanh::lean_unbox(v_pu_6510_) as u8);
    v_res_6519_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(
        v_pu_boxed_6518_,
        v_f_6511_,
        v_a_6512_,
        v_a_6513_,
        v_a_6514_,
        v_a_6515_,
        v_a_6516_,
    );
    crate::leanh::lean_dec(v_a_6516_);
    crate::leanh::lean_dec_ref(v_a_6515_);
    crate::leanh::lean_dec(v_a_6514_);
    crate::leanh::lean_dec_ref(v_a_6513_);
    crate::leanh::lean_dec_ref(v_a_6512_);
    return v_res_6519_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(
    mut v_pu_6520_: u8,
    mut v_f_6521_: *mut crate::leanh::LeanObject,
    mut v_a_6522_: *mut crate::leanh::LeanObject,
    mut v_a_6523_: *mut crate::leanh::LeanObject,
    mut v_a_6524_: *mut crate::leanh::LeanObject,
    mut v_a_6525_: *mut crate::leanh::LeanObject,
    mut v_a_6526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: u8 = 0;
    let mut v_decl_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: u8 = 0;
    let mut v_cases_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6547_: u8 = 0;
    let mut v_alts_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: u8 = 0;
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: usize = 0;
    let mut v___x_6561_: usize = 0;
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6563_: u8 = 0;
    let mut v_type_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: u8 = 0;
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_6522_) {
                0 => {
                    v_k_6528_ = crate::leanh::lean_ctor_get(v_a_6522_, 1);
                    crate::leanh::lean_inc_ref(v_k_6528_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 2);
                    v_a_6522_ = v_k_6528_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_6530_ = crate::leanh::lean_ctor_get(v_a_6522_, 0);
                    crate::leanh::lean_inc_ref(v_decl_6530_);
                    v_k_6531_ = crate::leanh::lean_ctor_get(v_a_6522_, 1);
                    crate::leanh::lean_inc_ref(v_k_6531_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 2);
                    v_value_6532_ = crate::leanh::lean_ctor_get(v_decl_6530_, 4);
                    crate::leanh::lean_inc_ref(v_value_6532_);
                    crate::leanh::lean_dec_ref(v_decl_6530_);
                    crate::leanh::lean_inc_ref(v_f_6521_);
                    v___x_6533_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_6520_, v_f_6521_, v_value_6532_, v_a_6523_, v_a_6524_, v_a_6525_, v_a_6526_);
                    if crate::leanh::lean_obj_tag(v___x_6533_) == 0 {
                        v_a_6534_ = crate::leanh::lean_ctor_get(v___x_6533_, 0);
                        crate::leanh::lean_inc(v_a_6534_);
                        v___x_6535_ = (crate::leanh::lean_unbox(v_a_6534_) as u8);
                        crate::leanh::lean_dec(v_a_6534_);
                        if v___x_6535_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6533_, 1);
                            v_a_6522_ = v_k_6531_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_6531_);
                            crate::leanh::lean_dec_ref(v_f_6521_);
                            return v___x_6533_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_6531_);
                        crate::leanh::lean_dec_ref(v_f_6521_);
                        return v___x_6533_;
                    }
                }
                2 => {
                    v_decl_6537_ = crate::leanh::lean_ctor_get(v_a_6522_, 0);
                    crate::leanh::lean_inc_ref(v_decl_6537_);
                    v_k_6538_ = crate::leanh::lean_ctor_get(v_a_6522_, 1);
                    crate::leanh::lean_inc_ref(v_k_6538_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 2);
                    v_value_6539_ = crate::leanh::lean_ctor_get(v_decl_6537_, 4);
                    crate::leanh::lean_inc_ref(v_value_6539_);
                    crate::leanh::lean_dec_ref(v_decl_6537_);
                    crate::leanh::lean_inc_ref(v_f_6521_);
                    v___x_6540_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_6520_, v_f_6521_, v_value_6539_, v_a_6523_, v_a_6524_, v_a_6525_, v_a_6526_);
                    if crate::leanh::lean_obj_tag(v___x_6540_) == 0 {
                        v_a_6541_ = crate::leanh::lean_ctor_get(v___x_6540_, 0);
                        crate::leanh::lean_inc(v_a_6541_);
                        v___x_6542_ = (crate::leanh::lean_unbox(v_a_6541_) as u8);
                        crate::leanh::lean_dec(v_a_6541_);
                        if v___x_6542_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6540_, 1);
                            v_a_6522_ = v_k_6538_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_6538_);
                            crate::leanh::lean_dec_ref(v_f_6521_);
                            return v___x_6540_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_6538_);
                        crate::leanh::lean_dec_ref(v_f_6521_);
                        return v___x_6540_;
                    }
                }
                4 => {
                    v_cases_6544_ = crate::leanh::lean_ctor_get(v_a_6522_, 0);
                    v_isSharedCheck_6563_ = (!crate::leanh::lean_is_exclusive(v_a_6522_)) as u8;
                    if v_isSharedCheck_6563_ == 0 {
                        v___x_6546_ = v_a_6522_;
                        v_isShared_6547_ = v_isSharedCheck_6563_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_6544_);
                        crate::leanh::lean_dec(v_a_6522_);
                        v___x_6546_ = crate::leanh::lean_box(0);
                        v_isShared_6547_ = v_isSharedCheck_6563_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_type_6564_ = crate::leanh::lean_ctor_get(v_a_6522_, 0);
                    crate::leanh::lean_inc_ref(v_type_6564_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 1);
                    crate::leanh::lean_inc(v_a_6526_);
                    crate::leanh::lean_inc_ref(v_a_6525_);
                    crate::leanh::lean_inc(v_a_6524_);
                    crate::leanh::lean_inc_ref(v_a_6523_);
                    v___x_6565_ = crate::leanh::lean_apply_6(
                        v_f_6521_,
                        v_type_6564_,
                        v_a_6523_,
                        v_a_6524_,
                        v_a_6525_,
                        v_a_6526_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6565_;
                }
                7 => {
                    v_k_6566_ = crate::leanh::lean_ctor_get(v_a_6522_, 3);
                    crate::leanh::lean_inc_ref(v_k_6566_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 4);
                    v_a_6522_ = v_k_6566_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_6568_ = crate::leanh::lean_ctor_get(v_a_6522_, 3);
                    crate::leanh::lean_inc_ref(v_k_6568_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 4);
                    v_a_6522_ = v_k_6568_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_6570_ = crate::leanh::lean_ctor_get(v_a_6522_, 5);
                    crate::leanh::lean_inc_ref(v_k_6570_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 6);
                    v_a_6522_ = v_k_6570_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_6572_ = crate::leanh::lean_ctor_get(v_a_6522_, 2);
                    crate::leanh::lean_inc_ref(v_k_6572_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 3);
                    v_a_6522_ = v_k_6572_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_6574_ = crate::leanh::lean_ctor_get(v_a_6522_, 2);
                    crate::leanh::lean_inc_ref(v_k_6574_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 3);
                    v_a_6522_ = v_k_6574_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_6576_ = crate::leanh::lean_ctor_get(v_a_6522_, 3);
                    crate::leanh::lean_inc_ref(v_k_6576_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 4);
                    v_a_6522_ = v_k_6576_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_6578_ = crate::leanh::lean_ctor_get(v_a_6522_, 1);
                    crate::leanh::lean_inc_ref(v_k_6578_);
                    crate::leanh::lean_dec_ref_known(v_a_6522_, 2);
                    v_a_6522_ = v_k_6578_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_6522_);
                    crate::leanh::lean_dec_ref(v_f_6521_);
                    v___x_6580_ = 0;
                    v___x_6581_ = crate::leanh::lean_box((v___x_6580_) as usize);
                    v___x_6582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6582_, 0, v___x_6581_);
                    return v___x_6582_;
                }
            },
            1 => {
                v_alts_6548_ = crate::leanh::lean_ctor_get(v_cases_6544_, 3);
                crate::leanh::lean_inc_ref(v_alts_6548_);
                crate::leanh::lean_dec_ref(v_cases_6544_);
                v___x_6549_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6550_ = lean_array_get_size(v_alts_6548_);
                v___x_6551_ = lean_nat_dec_lt(v___x_6549_, v___x_6550_);
                if v___x_6551_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_6548_);
                    crate::leanh::lean_dec_ref(v_f_6521_);
                    v___x_6552_ = crate::leanh::lean_box((v___x_6551_) as usize);
                    if v_isShared_6547_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6546_, 0);
                        crate::leanh::lean_ctor_set(v___x_6546_, 0, v___x_6552_);
                        v___x_6554_ = v___x_6546_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6555_, 0, v___x_6552_);
                        v___x_6554_ = v_reuseFailAlloc_6555_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_6551_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_6548_);
                        crate::leanh::lean_dec_ref(v_f_6521_);
                        v___x_6556_ = crate::leanh::lean_box((v___x_6551_) as usize);
                        if v_isShared_6547_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6546_, 0);
                            crate::leanh::lean_ctor_set(v___x_6546_, 0, v___x_6556_);
                            v___x_6558_ = v___x_6546_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6559_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6559_, 0, v___x_6556_);
                            v___x_6558_ = v_reuseFailAlloc_6559_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6546_);
                        v___x_6560_ = 0usize;
                        v___x_6561_ = lean_usize_of_nat(v___x_6550_);
                        v___x_6562_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_6520_, v_f_6521_, v_alts_6548_, v___x_6560_, v___x_6561_, v_a_6523_, v_a_6524_, v_a_6525_, v_a_6526_);
                        crate::leanh::lean_dec_ref(v_alts_6548_);
                        return v___x_6562_;
                    }
                }
            }
            2 => {
                return v___x_6554_;
            }
            3 => {
                return v___x_6558_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(
    mut v_pu_6583_: u8,
    mut v_f_6584_: *mut crate::leanh::LeanObject,
    mut v_as_6585_: *mut crate::leanh::LeanObject,
    mut v_i_6586_: usize,
    mut v_stop_6587_: usize,
    mut v___y_6588_: *mut crate::leanh::LeanObject,
    mut v___y_6589_: *mut crate::leanh::LeanObject,
    mut v___y_6590_: *mut crate::leanh::LeanObject,
    mut v___y_6591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6593_: u8 = 0;
    let mut v___x_6594_: u8 = 0;
    let mut v___y_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6601_: u8 = 0;
    let mut v___x_6602_: u8 = 0;
    let mut v___x_6603_: usize = 0;
    let mut v___x_6604_: usize = 0;
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6610_: u8 = 0;
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: u8 = 0;
    let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6593_ = lean_usize_dec_eq(v_i_6586_, v_stop_6587_);
                if v___x_6593_ == 0 {
                    v___x_6594_ = 1;
                    v___x_6611_ = lean_array_uget_borrowed(v_as_6585_, v_i_6586_);
                    match crate::leanh::lean_obj_tag(v___x_6611_) {
                        0 => {
                            v_code_6612_ = crate::leanh::lean_ctor_get(v___x_6611_, 2);
                            crate::leanh::lean_inc_ref(v_code_6612_);
                            v___y_6596_ = v_code_6612_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_6613_ = crate::leanh::lean_ctor_get(v___x_6611_, 1);
                            crate::leanh::lean_inc_ref(v_code_6613_);
                            v___y_6596_ = v_code_6613_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_6614_ = crate::leanh::lean_ctor_get(v___x_6611_, 0);
                            crate::leanh::lean_inc_ref(v_code_6614_);
                            v___y_6596_ = v_code_6614_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6584_);
                    v___x_6615_ = 0;
                    v___x_6616_ = crate::leanh::lean_box((v___x_6615_) as usize);
                    v___x_6617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6617_, 0, v___x_6616_);
                    return v___x_6617_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_6584_);
                v___x_6597_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_6583_, v_f_6584_, v___y_6596_, v___y_6588_, v___y_6589_, v___y_6590_, v___y_6591_);
                if crate::leanh::lean_obj_tag(v___x_6597_) == 0 {
                    v_a_6598_ = crate::leanh::lean_ctor_get(v___x_6597_, 0);
                    v_isSharedCheck_6610_ = (!crate::leanh::lean_is_exclusive(v___x_6597_)) as u8;
                    if v_isSharedCheck_6610_ == 0 {
                        v___x_6600_ = v___x_6597_;
                        v_isShared_6601_ = v_isSharedCheck_6610_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6598_);
                        crate::leanh::lean_dec(v___x_6597_);
                        v___x_6600_ = crate::leanh::lean_box(0);
                        v_isShared_6601_ = v_isSharedCheck_6610_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6584_);
                    return v___x_6597_;
                }
            }
            2 => {
                v___x_6602_ = (crate::leanh::lean_unbox(v_a_6598_) as u8);
                crate::leanh::lean_dec(v_a_6598_);
                if v___x_6602_ == 0 {
                    crate::leanh::lean_del_object(v___x_6600_);
                    v___x_6603_ = 1usize;
                    v___x_6604_ = lean_usize_add(v_i_6586_, v___x_6603_);
                    v_i_6586_ = v___x_6604_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_6584_);
                    v___x_6606_ = crate::leanh::lean_box((v___x_6594_) as usize);
                    if v_isShared_6601_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6600_, 0, v___x_6606_);
                        v___x_6608_ = v___x_6600_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6609_, 0, v___x_6606_);
                        v___x_6608_ = v_reuseFailAlloc_6609_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(
    mut v_pu_6618_: *mut crate::leanh::LeanObject,
    mut v_f_6619_: *mut crate::leanh::LeanObject,
    mut v_as_6620_: *mut crate::leanh::LeanObject,
    mut v_i_6621_: *mut crate::leanh::LeanObject,
    mut v_stop_6622_: *mut crate::leanh::LeanObject,
    mut v___y_6623_: *mut crate::leanh::LeanObject,
    mut v___y_6624_: *mut crate::leanh::LeanObject,
    mut v___y_6625_: *mut crate::leanh::LeanObject,
    mut v___y_6626_: *mut crate::leanh::LeanObject,
    mut v___y_6627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6628_: u8 = 0;
    let mut v_i_boxed_6629_: usize = 0;
    let mut v_stop_boxed_6630_: usize = 0;
    let mut v_res_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6628_ = (crate::leanh::lean_unbox(v_pu_6618_) as u8);
    v_i_boxed_6629_ = crate::leanh::lean_unbox_usize(v_i_6621_);
    crate::leanh::lean_dec(v_i_6621_);
    v_stop_boxed_6630_ = crate::leanh::lean_unbox_usize(v_stop_6622_);
    crate::leanh::lean_dec(v_stop_6622_);
    v_res_6631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_boxed_6628_, v_f_6619_, v_as_6620_, v_i_boxed_6629_, v_stop_boxed_6630_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
    crate::leanh::lean_dec(v___y_6626_);
    crate::leanh::lean_dec_ref(v___y_6625_);
    crate::leanh::lean_dec(v___y_6624_);
    crate::leanh::lean_dec_ref(v___y_6623_);
    crate::leanh::lean_dec_ref(v_as_6620_);
    return v_res_6631_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(
    mut v_pu_6632_: *mut crate::leanh::LeanObject,
    mut v_f_6633_: *mut crate::leanh::LeanObject,
    mut v_a_6634_: *mut crate::leanh::LeanObject,
    mut v_a_6635_: *mut crate::leanh::LeanObject,
    mut v_a_6636_: *mut crate::leanh::LeanObject,
    mut v_a_6637_: *mut crate::leanh::LeanObject,
    mut v_a_6638_: *mut crate::leanh::LeanObject,
    mut v_a_6639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6640_: u8 = 0;
    let mut v_res_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6640_ = (crate::leanh::lean_unbox(v_pu_6632_) as u8);
    v_res_6641_ =
        l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(
            v_pu_boxed_6640_,
            v_f_6633_,
            v_a_6634_,
            v_a_6635_,
            v_a_6636_,
            v_a_6637_,
            v_a_6638_,
        );
    crate::leanh::lean_dec(v_a_6638_);
    crate::leanh::lean_dec_ref(v_a_6637_);
    crate::leanh::lean_dec(v_a_6636_);
    crate::leanh::lean_dec_ref(v_a_6635_);
    return v_res_6641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(
    mut v_pu_6642_: u8,
    mut v_f_6643_: *mut crate::leanh::LeanObject,
    mut v_as_6644_: *mut crate::leanh::LeanObject,
    mut v_i_6645_: usize,
    mut v_stop_6646_: usize,
    mut v_b_6647_: *mut crate::leanh::LeanObject,
    mut v___y_6648_: *mut crate::leanh::LeanObject,
    mut v___y_6649_: *mut crate::leanh::LeanObject,
    mut v___y_6650_: *mut crate::leanh::LeanObject,
    mut v___y_6651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6653_: u8 = 0;
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: usize = 0;
    let mut v___x_6663_: usize = 0;
    let mut v___x_6665_: u8 = 0;
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6670_: u8 = 0;
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6674_: u8 = 0;
    let mut v___x_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6653_ = lean_usize_dec_eq(v_i_6645_, v_stop_6646_);
                if v___x_6653_ == 0 {
                    v___x_6654_ = lean_array_uget_borrowed(v_as_6644_, v_i_6645_);
                    v_value_6655_ = crate::leanh::lean_ctor_get(v___x_6654_, 1);
                    v___x_6656_ = crate::leanh::lean_box((v_pu_6642_) as usize);
                    crate::leanh::lean_inc_ref(v_f_6643_);
                    v___x_6657_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_6657_, 0, v___x_6656_);
                    crate::leanh::lean_closure_set(v___x_6657_, 1, v_f_6643_);
                    crate::leanh::lean_inc_ref(v_value_6655_);
                    v___x_6658_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_6655_, v___x_6657_, v___y_6648_, v___y_6649_, v___y_6650_, v___y_6651_);
                    if crate::leanh::lean_obj_tag(v___x_6658_) == 0 {
                        v_a_6659_ = crate::leanh::lean_ctor_get(v___x_6658_, 0);
                        crate::leanh::lean_inc(v_a_6659_);
                        crate::leanh::lean_dec_ref_known(v___x_6658_, 1);
                        v___x_6665_ = (crate::leanh::lean_unbox(v_a_6659_) as u8);
                        crate::leanh::lean_dec(v_a_6659_);
                        if v___x_6665_ == 0 {
                            v_a_6661_ = v_b_6647_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_6654_);
                            v___x_6666_ = lean_array_push(v_b_6647_, v___x_6654_);
                            v_a_6661_ = v___x_6666_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_6647_);
                        crate::leanh::lean_dec_ref(v_f_6643_);
                        v_a_6667_ = crate::leanh::lean_ctor_get(v___x_6658_, 0);
                        v_isSharedCheck_6674_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6658_)) as u8;
                        if v_isSharedCheck_6674_ == 0 {
                            v___x_6669_ = v___x_6658_;
                            v_isShared_6670_ = v_isSharedCheck_6674_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6667_);
                            crate::leanh::lean_dec(v___x_6658_);
                            v___x_6669_ = crate::leanh::lean_box(0);
                            v_isShared_6670_ = v_isSharedCheck_6674_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6643_);
                    v___x_6675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6675_, 0, v_b_6647_);
                    return v___x_6675_;
                }
            }
            1 => {
                v___x_6662_ = 1usize;
                v___x_6663_ = lean_usize_add(v_i_6645_, v___x_6662_);
                v_i_6645_ = v___x_6663_;
                v_b_6647_ = v_a_6661_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_6670_ == 0 {
                    v___x_6672_ = v___x_6669_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6673_, 0, v_a_6667_);
                    v___x_6672_ = v_reuseFailAlloc_6673_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(
    mut v_pu_6676_: *mut crate::leanh::LeanObject,
    mut v_f_6677_: *mut crate::leanh::LeanObject,
    mut v_as_6678_: *mut crate::leanh::LeanObject,
    mut v_i_6679_: *mut crate::leanh::LeanObject,
    mut v_stop_6680_: *mut crate::leanh::LeanObject,
    mut v_b_6681_: *mut crate::leanh::LeanObject,
    mut v___y_6682_: *mut crate::leanh::LeanObject,
    mut v___y_6683_: *mut crate::leanh::LeanObject,
    mut v___y_6684_: *mut crate::leanh::LeanObject,
    mut v___y_6685_: *mut crate::leanh::LeanObject,
    mut v___y_6686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6687_: u8 = 0;
    let mut v_i_boxed_6688_: usize = 0;
    let mut v_stop_boxed_6689_: usize = 0;
    let mut v_res_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6687_ = (crate::leanh::lean_unbox(v_pu_6676_) as u8);
    v_i_boxed_6688_ = crate::leanh::lean_unbox_usize(v_i_6679_);
    crate::leanh::lean_dec(v_i_6679_);
    v_stop_boxed_6689_ = crate::leanh::lean_unbox_usize(v_stop_6680_);
    crate::leanh::lean_dec(v_stop_6680_);
    v_res_6690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_boxed_6687_, v_f_6677_, v_as_6678_, v_i_boxed_6688_, v_stop_boxed_6689_, v_b_6681_, v___y_6682_, v___y_6683_, v___y_6684_, v___y_6685_);
    crate::leanh::lean_dec(v___y_6685_);
    crate::leanh::lean_dec_ref(v___y_6684_);
    crate::leanh::lean_dec(v___y_6683_);
    crate::leanh::lean_dec_ref(v___y_6682_);
    crate::leanh::lean_dec_ref(v_as_6678_);
    return v_res_6690_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByUnreach(
    mut v_pu_6691_: u8,
    mut v_f_6692_: *mut crate::leanh::LeanObject,
    mut v_a_6693_: *mut crate::leanh::LeanObject,
    mut v_a_6694_: *mut crate::leanh::LeanObject,
    mut v_a_6695_: *mut crate::leanh::LeanObject,
    mut v_a_6696_: *mut crate::leanh::LeanObject,
    mut v_a_6697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: u8 = 0;
    v___x_6699_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6700_ = lean_array_get_size(v_a_6693_);
    v___x_6701_ = l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0;
    v___x_6702_ = lean_nat_dec_lt(v___x_6699_, v___x_6700_);
    if v___x_6702_ == 0 {
        let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_6692_);
        v___x_6703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6703_, 0, v___x_6701_);
        return v___x_6703_;
    } else {
        let mut v___x_6704_: u8 = 0;
        v___x_6704_ = lean_nat_dec_le(v___x_6700_, v___x_6700_);
        if v___x_6704_ == 0 {
            if v___x_6702_ == 0 {
                let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_6692_);
                v___x_6705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6705_, 0, v___x_6701_);
                return v___x_6705_;
            } else {
                let mut v___x_6706_: usize = 0;
                let mut v___x_6707_: usize = 0;
                let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6706_ = 0usize;
                v___x_6707_ = lean_usize_of_nat(v___x_6700_);
                v___x_6708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_6691_, v_f_6692_, v_a_6693_, v___x_6706_, v___x_6707_, v___x_6701_, v_a_6694_, v_a_6695_, v_a_6696_, v_a_6697_);
                return v___x_6708_;
            }
        } else {
            let mut v___x_6709_: usize = 0;
            let mut v___x_6710_: usize = 0;
            let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6709_ = 0usize;
            v___x_6710_ = lean_usize_of_nat(v___x_6700_);
            v___x_6711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_6691_, v_f_6692_, v_a_6693_, v___x_6709_, v___x_6710_, v___x_6701_, v_a_6694_, v_a_6695_, v_a_6696_, v_a_6697_);
            return v___x_6711_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(
    mut v_pu_6712_: *mut crate::leanh::LeanObject,
    mut v_f_6713_: *mut crate::leanh::LeanObject,
    mut v_a_6714_: *mut crate::leanh::LeanObject,
    mut v_a_6715_: *mut crate::leanh::LeanObject,
    mut v_a_6716_: *mut crate::leanh::LeanObject,
    mut v_a_6717_: *mut crate::leanh::LeanObject,
    mut v_a_6718_: *mut crate::leanh::LeanObject,
    mut v_a_6719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6720_: u8 = 0;
    let mut v_res_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6720_ = (crate::leanh::lean_unbox(v_pu_6712_) as u8);
    v_res_6721_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(
        v_pu_boxed_6720_,
        v_f_6713_,
        v_a_6714_,
        v_a_6715_,
        v_a_6716_,
        v_a_6717_,
        v_a_6718_,
    );
    crate::leanh::lean_dec(v_a_6718_);
    crate::leanh::lean_dec_ref(v_a_6717_);
    crate::leanh::lean_dec(v_a_6716_);
    crate::leanh::lean_dec_ref(v_a_6715_);
    crate::leanh::lean_dec_ref(v_a_6714_);
    return v_res_6721_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(
    mut v_decl_6722_: *mut crate::leanh::LeanObject,
    mut v___y_6723_: *mut crate::leanh::LeanObject,
    mut v___y_6724_: *mut crate::leanh::LeanObject,
    mut v___y_6725_: *mut crate::leanh::LeanObject,
    mut v___y_6726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSignature_6728_ = crate::leanh::lean_ctor_get(v_decl_6722_, 0);
    v_name_6729_ = crate::leanh::lean_ctor_get(v_toSignature_6728_, 0);
    crate::leanh::lean_inc(v_name_6729_);
    v___x_6730_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6730_, 0, v_name_6729_);
    return v___x_6730_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(
    mut v_decl_6731_: *mut crate::leanh::LeanObject,
    mut v___y_6732_: *mut crate::leanh::LeanObject,
    mut v___y_6733_: *mut crate::leanh::LeanObject,
    mut v___y_6734_: *mut crate::leanh::LeanObject,
    mut v___y_6735_: *mut crate::leanh::LeanObject,
    mut v___y_6736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6737_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(
        v_decl_6731_,
        v___y_6732_,
        v___y_6733_,
        v___y_6734_,
        v___y_6735_,
    );
    crate::leanh::lean_dec(v___y_6735_);
    crate::leanh::lean_dec_ref(v___y_6734_);
    crate::leanh::lean_dec(v___y_6733_);
    crate::leanh::lean_dec_ref(v___y_6732_);
    crate::leanh::lean_dec_ref(v_decl_6731_);
    return v_res_6737_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_declNames___redArg(
    mut v_a_6739_: *mut crate::leanh::LeanObject,
    mut v_a_6740_: *mut crate::leanh::LeanObject,
    mut v_a_6741_: *mut crate::leanh::LeanObject,
    mut v_a_6742_: *mut crate::leanh::LeanObject,
    mut v_a_6743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6765_: u8 = 0;
    let mut v_toFunctor_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6772_: u8 = 0;
    let mut v___f_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6786_: usize = 0;
    let mut v___x_6787_: usize = 0;
    let mut v___x_127__overap_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6792_: u8 = 0;
    let mut v_unused_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6794_: u8 = 0;
    let mut v_unused_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6745_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_6746_ = crate::leanh::lean_ctor_get(v___x_6745_, 0);
                v_toFunctor_6747_ = crate::leanh::lean_ctor_get(v_toApplicative_6746_, 0);
                v_toSeq_6748_ = crate::leanh::lean_ctor_get(v_toApplicative_6746_, 2);
                v_toSeqLeft_6749_ = crate::leanh::lean_ctor_get(v_toApplicative_6746_, 3);
                v_toSeqRight_6750_ = crate::leanh::lean_ctor_get(v_toApplicative_6746_, 4);
                v___f_6751_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_6752_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_6747_, 2);
                v___f_6753_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6753_, 0, v_toFunctor_6747_);
                v___f_6754_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6754_, 0, v_toFunctor_6747_);
                v___x_6755_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6755_, 0, v___f_6753_);
                crate::leanh::lean_ctor_set(v___x_6755_, 1, v___f_6754_);
                crate::leanh::lean_inc(v_toSeqRight_6750_);
                v___f_6756_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6756_, 0, v_toSeqRight_6750_);
                crate::leanh::lean_inc(v_toSeqLeft_6749_);
                v___f_6757_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6757_, 0, v_toSeqLeft_6749_);
                crate::leanh::lean_inc(v_toSeq_6748_);
                v___f_6758_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6758_, 0, v_toSeq_6748_);
                v___x_6759_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6759_, 0, v___x_6755_);
                crate::leanh::lean_ctor_set(v___x_6759_, 1, v___f_6751_);
                crate::leanh::lean_ctor_set(v___x_6759_, 2, v___f_6758_);
                crate::leanh::lean_ctor_set(v___x_6759_, 3, v___f_6757_);
                crate::leanh::lean_ctor_set(v___x_6759_, 4, v___f_6756_);
                v___x_6760_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6760_, 0, v___x_6759_);
                crate::leanh::lean_ctor_set(v___x_6760_, 1, v___f_6752_);
                v___x_6761_ = l_StateRefT_x27_instMonad___redArg(v___x_6760_);
                v_toApplicative_6762_ = crate::leanh::lean_ctor_get(v___x_6761_, 0);
                v_isSharedCheck_6794_ = (!crate::leanh::lean_is_exclusive(v___x_6761_)) as u8;
                if v_isSharedCheck_6794_ == 0 {
                    v_unused_6795_ = crate::leanh::lean_ctor_get(v___x_6761_, 1);
                    crate::leanh::lean_dec(v_unused_6795_);
                    v___x_6764_ = v___x_6761_;
                    v_isShared_6765_ = v_isSharedCheck_6794_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_6762_);
                    crate::leanh::lean_dec(v___x_6761_);
                    v___x_6764_ = crate::leanh::lean_box(0);
                    v_isShared_6765_ = v_isSharedCheck_6794_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_6766_ = crate::leanh::lean_ctor_get(v_toApplicative_6762_, 0);
                v_toSeq_6767_ = crate::leanh::lean_ctor_get(v_toApplicative_6762_, 2);
                v_toSeqLeft_6768_ = crate::leanh::lean_ctor_get(v_toApplicative_6762_, 3);
                v_toSeqRight_6769_ = crate::leanh::lean_ctor_get(v_toApplicative_6762_, 4);
                v_isSharedCheck_6792_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_6762_)) as u8;
                if v_isSharedCheck_6792_ == 0 {
                    v_unused_6793_ = crate::leanh::lean_ctor_get(v_toApplicative_6762_, 1);
                    crate::leanh::lean_dec(v_unused_6793_);
                    v___x_6771_ = v_toApplicative_6762_;
                    v_isShared_6772_ = v_isSharedCheck_6792_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_6769_);
                    crate::leanh::lean_inc(v_toSeqLeft_6768_);
                    crate::leanh::lean_inc(v_toSeq_6767_);
                    crate::leanh::lean_inc(v_toFunctor_6766_);
                    crate::leanh::lean_dec(v_toApplicative_6762_);
                    v___x_6771_ = crate::leanh::lean_box(0);
                    v_isShared_6772_ = v_isSharedCheck_6792_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_6773_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0;
                v___f_6774_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_6775_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_6766_);
                v___f_6776_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6776_, 0, v_toFunctor_6766_);
                v___f_6777_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6777_, 0, v_toFunctor_6766_);
                v___x_6778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6778_, 0, v___f_6776_);
                crate::leanh::lean_ctor_set(v___x_6778_, 1, v___f_6777_);
                v___f_6779_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6779_, 0, v_toSeqRight_6769_);
                v___f_6780_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6780_, 0, v_toSeqLeft_6768_);
                v___f_6781_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6781_, 0, v_toSeq_6767_);
                if v_isShared_6772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6771_, 4, v___f_6779_);
                    crate::leanh::lean_ctor_set(v___x_6771_, 3, v___f_6780_);
                    crate::leanh::lean_ctor_set(v___x_6771_, 2, v___f_6781_);
                    crate::leanh::lean_ctor_set(v___x_6771_, 1, v___f_6774_);
                    crate::leanh::lean_ctor_set(v___x_6771_, 0, v___x_6778_);
                    v___x_6783_ = v___x_6771_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6791_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6791_, 0, v___x_6778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6791_, 1, v___f_6774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6791_, 2, v___f_6781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6791_, 3, v___f_6780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6791_, 4, v___f_6779_);
                    v___x_6783_ = v_reuseFailAlloc_6791_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6764_, 1, v___f_6775_);
                    crate::leanh::lean_ctor_set(v___x_6764_, 0, v___x_6783_);
                    v___x_6785_ = v___x_6764_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6790_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6790_, 0, v___x_6783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6790_, 1, v___f_6775_);
                    v___x_6785_ = v_reuseFailAlloc_6790_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_6786_ = lean_array_size(v_a_6739_);
                v___x_6787_ = 0usize;
                v___x_127__overap_6788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6785_,
                    v___f_6773_,
                    v_sz_6786_,
                    v___x_6787_,
                    v_a_6739_,
                );
                crate::leanh::lean_inc(v_a_6743_);
                crate::leanh::lean_inc_ref(v_a_6742_);
                crate::leanh::lean_inc(v_a_6741_);
                crate::leanh::lean_inc_ref(v_a_6740_);
                v___x_6789_ = crate::leanh::lean_apply_5(
                    v___x_127__overap_6788_,
                    v_a_6740_,
                    v_a_6741_,
                    v_a_6742_,
                    v_a_6743_,
                    crate::leanh::lean_box(0),
                );
                return v___x_6789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(
    mut v_a_6796_: *mut crate::leanh::LeanObject,
    mut v_a_6797_: *mut crate::leanh::LeanObject,
    mut v_a_6798_: *mut crate::leanh::LeanObject,
    mut v_a_6799_: *mut crate::leanh::LeanObject,
    mut v_a_6800_: *mut crate::leanh::LeanObject,
    mut v_a_6801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6802_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(
        v_a_6796_, v_a_6797_, v_a_6798_, v_a_6799_, v_a_6800_,
    );
    crate::leanh::lean_dec(v_a_6800_);
    crate::leanh::lean_dec_ref(v_a_6799_);
    crate::leanh::lean_dec(v_a_6798_);
    crate::leanh::lean_dec_ref(v_a_6797_);
    return v_res_6802_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_declNames(
    mut v_pu_6803_: u8,
    mut v_a_6804_: *mut crate::leanh::LeanObject,
    mut v_a_6805_: *mut crate::leanh::LeanObject,
    mut v_a_6806_: *mut crate::leanh::LeanObject,
    mut v_a_6807_: *mut crate::leanh::LeanObject,
    mut v_a_6808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6830_: u8 = 0;
    let mut v_toFunctor_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6837_: u8 = 0;
    let mut v___f_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6851_: usize = 0;
    let mut v___x_6852_: usize = 0;
    let mut v___x_185__overap_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6857_: u8 = 0;
    let mut v_unused_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6859_: u8 = 0;
    let mut v_unused_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6810_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_6811_ = crate::leanh::lean_ctor_get(v___x_6810_, 0);
                v_toFunctor_6812_ = crate::leanh::lean_ctor_get(v_toApplicative_6811_, 0);
                v_toSeq_6813_ = crate::leanh::lean_ctor_get(v_toApplicative_6811_, 2);
                v_toSeqLeft_6814_ = crate::leanh::lean_ctor_get(v_toApplicative_6811_, 3);
                v_toSeqRight_6815_ = crate::leanh::lean_ctor_get(v_toApplicative_6811_, 4);
                v___f_6816_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_6817_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_6812_, 2);
                v___f_6818_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6818_, 0, v_toFunctor_6812_);
                v___f_6819_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6819_, 0, v_toFunctor_6812_);
                v___x_6820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6820_, 0, v___f_6818_);
                crate::leanh::lean_ctor_set(v___x_6820_, 1, v___f_6819_);
                crate::leanh::lean_inc(v_toSeqRight_6815_);
                v___f_6821_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6821_, 0, v_toSeqRight_6815_);
                crate::leanh::lean_inc(v_toSeqLeft_6814_);
                v___f_6822_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6822_, 0, v_toSeqLeft_6814_);
                crate::leanh::lean_inc(v_toSeq_6813_);
                v___f_6823_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6823_, 0, v_toSeq_6813_);
                v___x_6824_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6824_, 0, v___x_6820_);
                crate::leanh::lean_ctor_set(v___x_6824_, 1, v___f_6816_);
                crate::leanh::lean_ctor_set(v___x_6824_, 2, v___f_6823_);
                crate::leanh::lean_ctor_set(v___x_6824_, 3, v___f_6822_);
                crate::leanh::lean_ctor_set(v___x_6824_, 4, v___f_6821_);
                v___x_6825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6825_, 0, v___x_6824_);
                crate::leanh::lean_ctor_set(v___x_6825_, 1, v___f_6817_);
                v___x_6826_ = l_StateRefT_x27_instMonad___redArg(v___x_6825_);
                v_toApplicative_6827_ = crate::leanh::lean_ctor_get(v___x_6826_, 0);
                v_isSharedCheck_6859_ = (!crate::leanh::lean_is_exclusive(v___x_6826_)) as u8;
                if v_isSharedCheck_6859_ == 0 {
                    v_unused_6860_ = crate::leanh::lean_ctor_get(v___x_6826_, 1);
                    crate::leanh::lean_dec(v_unused_6860_);
                    v___x_6829_ = v___x_6826_;
                    v_isShared_6830_ = v_isSharedCheck_6859_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_6827_);
                    crate::leanh::lean_dec(v___x_6826_);
                    v___x_6829_ = crate::leanh::lean_box(0);
                    v_isShared_6830_ = v_isSharedCheck_6859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_6831_ = crate::leanh::lean_ctor_get(v_toApplicative_6827_, 0);
                v_toSeq_6832_ = crate::leanh::lean_ctor_get(v_toApplicative_6827_, 2);
                v_toSeqLeft_6833_ = crate::leanh::lean_ctor_get(v_toApplicative_6827_, 3);
                v_toSeqRight_6834_ = crate::leanh::lean_ctor_get(v_toApplicative_6827_, 4);
                v_isSharedCheck_6857_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_6827_)) as u8;
                if v_isSharedCheck_6857_ == 0 {
                    v_unused_6858_ = crate::leanh::lean_ctor_get(v_toApplicative_6827_, 1);
                    crate::leanh::lean_dec(v_unused_6858_);
                    v___x_6836_ = v_toApplicative_6827_;
                    v_isShared_6837_ = v_isSharedCheck_6857_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_6834_);
                    crate::leanh::lean_inc(v_toSeqLeft_6833_);
                    crate::leanh::lean_inc(v_toSeq_6832_);
                    crate::leanh::lean_inc(v_toFunctor_6831_);
                    crate::leanh::lean_dec(v_toApplicative_6827_);
                    v___x_6836_ = crate::leanh::lean_box(0);
                    v_isShared_6837_ = v_isSharedCheck_6857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_6838_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0;
                v___f_6839_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_6840_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_6831_);
                v___f_6841_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6841_, 0, v_toFunctor_6831_);
                v___f_6842_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6842_, 0, v_toFunctor_6831_);
                v___x_6843_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6843_, 0, v___f_6841_);
                crate::leanh::lean_ctor_set(v___x_6843_, 1, v___f_6842_);
                v___f_6844_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6844_, 0, v_toSeqRight_6834_);
                v___f_6845_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6845_, 0, v_toSeqLeft_6833_);
                v___f_6846_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6846_, 0, v_toSeq_6832_);
                if v_isShared_6837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6836_, 4, v___f_6844_);
                    crate::leanh::lean_ctor_set(v___x_6836_, 3, v___f_6845_);
                    crate::leanh::lean_ctor_set(v___x_6836_, 2, v___f_6846_);
                    crate::leanh::lean_ctor_set(v___x_6836_, 1, v___f_6839_);
                    crate::leanh::lean_ctor_set(v___x_6836_, 0, v___x_6843_);
                    v___x_6848_ = v___x_6836_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6856_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6856_, 0, v___x_6843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6856_, 1, v___f_6839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6856_, 2, v___f_6846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6856_, 3, v___f_6845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6856_, 4, v___f_6844_);
                    v___x_6848_ = v_reuseFailAlloc_6856_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6829_, 1, v___f_6840_);
                    crate::leanh::lean_ctor_set(v___x_6829_, 0, v___x_6848_);
                    v___x_6850_ = v___x_6829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6855_, 0, v___x_6848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6855_, 1, v___f_6840_);
                    v___x_6850_ = v_reuseFailAlloc_6855_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_6851_ = lean_array_size(v_a_6804_);
                v___x_6852_ = 0usize;
                v___x_185__overap_6853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6850_,
                    v___f_6838_,
                    v_sz_6851_,
                    v___x_6852_,
                    v_a_6804_,
                );
                crate::leanh::lean_inc(v_a_6808_);
                crate::leanh::lean_inc_ref(v_a_6807_);
                crate::leanh::lean_inc(v_a_6806_);
                crate::leanh::lean_inc_ref(v_a_6805_);
                v___x_6854_ = crate::leanh::lean_apply_5(
                    v___x_185__overap_6853_,
                    v_a_6805_,
                    v_a_6806_,
                    v_a_6807_,
                    v_a_6808_,
                    crate::leanh::lean_box(0),
                );
                return v___x_6854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_declNames___boxed(
    mut v_pu_6861_: *mut crate::leanh::LeanObject,
    mut v_a_6862_: *mut crate::leanh::LeanObject,
    mut v_a_6863_: *mut crate::leanh::LeanObject,
    mut v_a_6864_: *mut crate::leanh::LeanObject,
    mut v_a_6865_: *mut crate::leanh::LeanObject,
    mut v_a_6866_: *mut crate::leanh::LeanObject,
    mut v_a_6867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6868_: u8 = 0;
    let mut v_res_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6868_ = (crate::leanh::lean_unbox(v_pu_6861_) as u8);
    v_res_6869_ = l_Lean_Compiler_LCNF_Probe_declNames(
        v_pu_boxed_6868_,
        v_a_6862_,
        v_a_6863_,
        v_a_6864_,
        v_a_6865_,
        v_a_6866_,
    );
    crate::leanh::lean_dec(v_a_6866_);
    crate::leanh::lean_dec_ref(v_a_6865_);
    crate::leanh::lean_dec(v_a_6864_);
    crate::leanh::lean_dec_ref(v_a_6863_);
    return v_res_6869_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(
    mut v_inst_6870_: *mut crate::leanh::LeanObject,
    mut v_x_6871_: *mut crate::leanh::LeanObject,
    mut v___y_6872_: *mut crate::leanh::LeanObject,
    mut v___y_6873_: *mut crate::leanh::LeanObject,
    mut v___y_6874_: *mut crate::leanh::LeanObject,
    mut v___y_6875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6877_ = crate::leanh::lean_apply_1(v_inst_6870_, v_x_6871_);
    v___x_6878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6878_, 0, v___x_6877_);
    return v___x_6878_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(
    mut v_inst_6879_: *mut crate::leanh::LeanObject,
    mut v_x_6880_: *mut crate::leanh::LeanObject,
    mut v___y_6881_: *mut crate::leanh::LeanObject,
    mut v___y_6882_: *mut crate::leanh::LeanObject,
    mut v___y_6883_: *mut crate::leanh::LeanObject,
    mut v___y_6884_: *mut crate::leanh::LeanObject,
    mut v___y_6885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6886_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(
        v_inst_6879_,
        v_x_6880_,
        v___y_6881_,
        v___y_6882_,
        v___y_6883_,
        v___y_6884_,
    );
    crate::leanh::lean_dec(v___y_6884_);
    crate::leanh::lean_dec_ref(v___y_6883_);
    crate::leanh::lean_dec(v___y_6882_);
    crate::leanh::lean_dec_ref(v___y_6881_);
    return v_res_6886_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toString___redArg(
    mut v_inst_6887_: *mut crate::leanh::LeanObject,
    mut v_a_6888_: *mut crate::leanh::LeanObject,
    mut v_a_6889_: *mut crate::leanh::LeanObject,
    mut v_a_6890_: *mut crate::leanh::LeanObject,
    mut v_a_6891_: *mut crate::leanh::LeanObject,
    mut v_a_6892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6914_: u8 = 0;
    let mut v_toFunctor_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6921_: u8 = 0;
    let mut v___f_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6935_: usize = 0;
    let mut v___x_6936_: usize = 0;
    let mut v___x_129__overap_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6941_: u8 = 0;
    let mut v_unused_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6943_: u8 = 0;
    let mut v_unused_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6894_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_6895_ = crate::leanh::lean_ctor_get(v___x_6894_, 0);
                v_toFunctor_6896_ = crate::leanh::lean_ctor_get(v_toApplicative_6895_, 0);
                v_toSeq_6897_ = crate::leanh::lean_ctor_get(v_toApplicative_6895_, 2);
                v_toSeqLeft_6898_ = crate::leanh::lean_ctor_get(v_toApplicative_6895_, 3);
                v_toSeqRight_6899_ = crate::leanh::lean_ctor_get(v_toApplicative_6895_, 4);
                v___f_6900_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_6901_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_6896_, 2);
                v___f_6902_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6902_, 0, v_toFunctor_6896_);
                v___f_6903_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6903_, 0, v_toFunctor_6896_);
                v___x_6904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6904_, 0, v___f_6902_);
                crate::leanh::lean_ctor_set(v___x_6904_, 1, v___f_6903_);
                crate::leanh::lean_inc(v_toSeqRight_6899_);
                v___f_6905_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6905_, 0, v_toSeqRight_6899_);
                crate::leanh::lean_inc(v_toSeqLeft_6898_);
                v___f_6906_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6906_, 0, v_toSeqLeft_6898_);
                crate::leanh::lean_inc(v_toSeq_6897_);
                v___f_6907_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6907_, 0, v_toSeq_6897_);
                v___x_6908_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6908_, 0, v___x_6904_);
                crate::leanh::lean_ctor_set(v___x_6908_, 1, v___f_6900_);
                crate::leanh::lean_ctor_set(v___x_6908_, 2, v___f_6907_);
                crate::leanh::lean_ctor_set(v___x_6908_, 3, v___f_6906_);
                crate::leanh::lean_ctor_set(v___x_6908_, 4, v___f_6905_);
                v___x_6909_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6909_, 0, v___x_6908_);
                crate::leanh::lean_ctor_set(v___x_6909_, 1, v___f_6901_);
                v___x_6910_ = l_StateRefT_x27_instMonad___redArg(v___x_6909_);
                v_toApplicative_6911_ = crate::leanh::lean_ctor_get(v___x_6910_, 0);
                v_isSharedCheck_6943_ = (!crate::leanh::lean_is_exclusive(v___x_6910_)) as u8;
                if v_isSharedCheck_6943_ == 0 {
                    v_unused_6944_ = crate::leanh::lean_ctor_get(v___x_6910_, 1);
                    crate::leanh::lean_dec(v_unused_6944_);
                    v___x_6913_ = v___x_6910_;
                    v_isShared_6914_ = v_isSharedCheck_6943_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_6911_);
                    crate::leanh::lean_dec(v___x_6910_);
                    v___x_6913_ = crate::leanh::lean_box(0);
                    v_isShared_6914_ = v_isSharedCheck_6943_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_6915_ = crate::leanh::lean_ctor_get(v_toApplicative_6911_, 0);
                v_toSeq_6916_ = crate::leanh::lean_ctor_get(v_toApplicative_6911_, 2);
                v_toSeqLeft_6917_ = crate::leanh::lean_ctor_get(v_toApplicative_6911_, 3);
                v_toSeqRight_6918_ = crate::leanh::lean_ctor_get(v_toApplicative_6911_, 4);
                v_isSharedCheck_6941_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_6911_)) as u8;
                if v_isSharedCheck_6941_ == 0 {
                    v_unused_6942_ = crate::leanh::lean_ctor_get(v_toApplicative_6911_, 1);
                    crate::leanh::lean_dec(v_unused_6942_);
                    v___x_6920_ = v_toApplicative_6911_;
                    v_isShared_6921_ = v_isSharedCheck_6941_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_6918_);
                    crate::leanh::lean_inc(v_toSeqLeft_6917_);
                    crate::leanh::lean_inc(v_toSeq_6916_);
                    crate::leanh::lean_inc(v_toFunctor_6915_);
                    crate::leanh::lean_dec(v_toApplicative_6911_);
                    v___x_6920_ = crate::leanh::lean_box(0);
                    v_isShared_6921_ = v_isSharedCheck_6941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_6922_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6922_, 0, v_inst_6887_);
                v___f_6923_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_6924_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_6915_);
                v___f_6925_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6925_, 0, v_toFunctor_6915_);
                v___f_6926_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6926_, 0, v_toFunctor_6915_);
                v___x_6927_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6927_, 0, v___f_6925_);
                crate::leanh::lean_ctor_set(v___x_6927_, 1, v___f_6926_);
                v___f_6928_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6928_, 0, v_toSeqRight_6918_);
                v___f_6929_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6929_, 0, v_toSeqLeft_6917_);
                v___f_6930_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6930_, 0, v_toSeq_6916_);
                if v_isShared_6921_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6920_, 4, v___f_6928_);
                    crate::leanh::lean_ctor_set(v___x_6920_, 3, v___f_6929_);
                    crate::leanh::lean_ctor_set(v___x_6920_, 2, v___f_6930_);
                    crate::leanh::lean_ctor_set(v___x_6920_, 1, v___f_6923_);
                    crate::leanh::lean_ctor_set(v___x_6920_, 0, v___x_6927_);
                    v___x_6932_ = v___x_6920_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6940_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6940_, 0, v___x_6927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6940_, 1, v___f_6923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6940_, 2, v___f_6930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6940_, 3, v___f_6929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6940_, 4, v___f_6928_);
                    v___x_6932_ = v_reuseFailAlloc_6940_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6913_, 1, v___f_6924_);
                    crate::leanh::lean_ctor_set(v___x_6913_, 0, v___x_6932_);
                    v___x_6934_ = v___x_6913_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6939_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6939_, 0, v___x_6932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6939_, 1, v___f_6924_);
                    v___x_6934_ = v_reuseFailAlloc_6939_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_6935_ = lean_array_size(v_a_6888_);
                v___x_6936_ = 0usize;
                v___x_129__overap_6937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6934_,
                    v___f_6922_,
                    v_sz_6935_,
                    v___x_6936_,
                    v_a_6888_,
                );
                crate::leanh::lean_inc(v_a_6892_);
                crate::leanh::lean_inc_ref(v_a_6891_);
                crate::leanh::lean_inc(v_a_6890_);
                crate::leanh::lean_inc_ref(v_a_6889_);
                v___x_6938_ = crate::leanh::lean_apply_5(
                    v___x_129__overap_6937_,
                    v_a_6889_,
                    v_a_6890_,
                    v_a_6891_,
                    v_a_6892_,
                    crate::leanh::lean_box(0),
                );
                return v___x_6938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(
    mut v_inst_6945_: *mut crate::leanh::LeanObject,
    mut v_a_6946_: *mut crate::leanh::LeanObject,
    mut v_a_6947_: *mut crate::leanh::LeanObject,
    mut v_a_6948_: *mut crate::leanh::LeanObject,
    mut v_a_6949_: *mut crate::leanh::LeanObject,
    mut v_a_6950_: *mut crate::leanh::LeanObject,
    mut v_a_6951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6952_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(
        v_inst_6945_,
        v_a_6946_,
        v_a_6947_,
        v_a_6948_,
        v_a_6949_,
        v_a_6950_,
    );
    crate::leanh::lean_dec(v_a_6950_);
    crate::leanh::lean_dec_ref(v_a_6949_);
    crate::leanh::lean_dec(v_a_6948_);
    crate::leanh::lean_dec_ref(v_a_6947_);
    return v_res_6952_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toString(
    mut v_00_u03b1_6953_: *mut crate::leanh::LeanObject,
    mut v_inst_6954_: *mut crate::leanh::LeanObject,
    mut v_a_6955_: *mut crate::leanh::LeanObject,
    mut v_a_6956_: *mut crate::leanh::LeanObject,
    mut v_a_6957_: *mut crate::leanh::LeanObject,
    mut v_a_6958_: *mut crate::leanh::LeanObject,
    mut v_a_6959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6981_: u8 = 0;
    let mut v_toFunctor_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6988_: u8 = 0;
    let mut v___f_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7002_: usize = 0;
    let mut v___x_7003_: usize = 0;
    let mut v___x_190__overap_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7008_: u8 = 0;
    let mut v_unused_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut v_unused_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6961_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_6962_ = crate::leanh::lean_ctor_get(v___x_6961_, 0);
                v_toFunctor_6963_ = crate::leanh::lean_ctor_get(v_toApplicative_6962_, 0);
                v_toSeq_6964_ = crate::leanh::lean_ctor_get(v_toApplicative_6962_, 2);
                v_toSeqLeft_6965_ = crate::leanh::lean_ctor_get(v_toApplicative_6962_, 3);
                v_toSeqRight_6966_ = crate::leanh::lean_ctor_get(v_toApplicative_6962_, 4);
                v___f_6967_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_6968_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_6963_, 2);
                v___f_6969_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6969_, 0, v_toFunctor_6963_);
                v___f_6970_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6970_, 0, v_toFunctor_6963_);
                v___x_6971_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6971_, 0, v___f_6969_);
                crate::leanh::lean_ctor_set(v___x_6971_, 1, v___f_6970_);
                crate::leanh::lean_inc(v_toSeqRight_6966_);
                v___f_6972_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6972_, 0, v_toSeqRight_6966_);
                crate::leanh::lean_inc(v_toSeqLeft_6965_);
                v___f_6973_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6973_, 0, v_toSeqLeft_6965_);
                crate::leanh::lean_inc(v_toSeq_6964_);
                v___f_6974_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6974_, 0, v_toSeq_6964_);
                v___x_6975_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6975_, 0, v___x_6971_);
                crate::leanh::lean_ctor_set(v___x_6975_, 1, v___f_6967_);
                crate::leanh::lean_ctor_set(v___x_6975_, 2, v___f_6974_);
                crate::leanh::lean_ctor_set(v___x_6975_, 3, v___f_6973_);
                crate::leanh::lean_ctor_set(v___x_6975_, 4, v___f_6972_);
                v___x_6976_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6976_, 0, v___x_6975_);
                crate::leanh::lean_ctor_set(v___x_6976_, 1, v___f_6968_);
                v___x_6977_ = l_StateRefT_x27_instMonad___redArg(v___x_6976_);
                v_toApplicative_6978_ = crate::leanh::lean_ctor_get(v___x_6977_, 0);
                v_isSharedCheck_7010_ = (!crate::leanh::lean_is_exclusive(v___x_6977_)) as u8;
                if v_isSharedCheck_7010_ == 0 {
                    v_unused_7011_ = crate::leanh::lean_ctor_get(v___x_6977_, 1);
                    crate::leanh::lean_dec(v_unused_7011_);
                    v___x_6980_ = v___x_6977_;
                    v_isShared_6981_ = v_isSharedCheck_7010_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_6978_);
                    crate::leanh::lean_dec(v___x_6977_);
                    v___x_6980_ = crate::leanh::lean_box(0);
                    v_isShared_6981_ = v_isSharedCheck_7010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_6982_ = crate::leanh::lean_ctor_get(v_toApplicative_6978_, 0);
                v_toSeq_6983_ = crate::leanh::lean_ctor_get(v_toApplicative_6978_, 2);
                v_toSeqLeft_6984_ = crate::leanh::lean_ctor_get(v_toApplicative_6978_, 3);
                v_toSeqRight_6985_ = crate::leanh::lean_ctor_get(v_toApplicative_6978_, 4);
                v_isSharedCheck_7008_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_6978_)) as u8;
                if v_isSharedCheck_7008_ == 0 {
                    v_unused_7009_ = crate::leanh::lean_ctor_get(v_toApplicative_6978_, 1);
                    crate::leanh::lean_dec(v_unused_7009_);
                    v___x_6987_ = v_toApplicative_6978_;
                    v_isShared_6988_ = v_isSharedCheck_7008_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_6985_);
                    crate::leanh::lean_inc(v_toSeqLeft_6984_);
                    crate::leanh::lean_inc(v_toSeq_6983_);
                    crate::leanh::lean_inc(v_toFunctor_6982_);
                    crate::leanh::lean_dec(v_toApplicative_6978_);
                    v___x_6987_ = crate::leanh::lean_box(0);
                    v_isShared_6988_ = v_isSharedCheck_7008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_6989_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6989_, 0, v_inst_6954_);
                v___f_6990_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_6991_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_6982_);
                v___f_6992_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6992_, 0, v_toFunctor_6982_);
                v___f_6993_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6993_, 0, v_toFunctor_6982_);
                v___x_6994_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6994_, 0, v___f_6992_);
                crate::leanh::lean_ctor_set(v___x_6994_, 1, v___f_6993_);
                v___f_6995_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6995_, 0, v_toSeqRight_6985_);
                v___f_6996_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6996_, 0, v_toSeqLeft_6984_);
                v___f_6997_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6997_, 0, v_toSeq_6983_);
                if v_isShared_6988_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6987_, 4, v___f_6995_);
                    crate::leanh::lean_ctor_set(v___x_6987_, 3, v___f_6996_);
                    crate::leanh::lean_ctor_set(v___x_6987_, 2, v___f_6997_);
                    crate::leanh::lean_ctor_set(v___x_6987_, 1, v___f_6990_);
                    crate::leanh::lean_ctor_set(v___x_6987_, 0, v___x_6994_);
                    v___x_6999_ = v___x_6987_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7007_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 0, v___x_6994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 1, v___f_6990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 2, v___f_6997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 3, v___f_6996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 4, v___f_6995_);
                    v___x_6999_ = v_reuseFailAlloc_7007_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6980_, 1, v___f_6991_);
                    crate::leanh::lean_ctor_set(v___x_6980_, 0, v___x_6999_);
                    v___x_7001_ = v___x_6980_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7006_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7006_, 0, v___x_6999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7006_, 1, v___f_6991_);
                    v___x_7001_ = v_reuseFailAlloc_7006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_7002_ = lean_array_size(v_a_6955_);
                v___x_7003_ = 0usize;
                v___x_190__overap_7004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7001_,
                    v___f_6989_,
                    v_sz_7002_,
                    v___x_7003_,
                    v_a_6955_,
                );
                crate::leanh::lean_inc(v_a_6959_);
                crate::leanh::lean_inc_ref(v_a_6958_);
                crate::leanh::lean_inc(v_a_6957_);
                crate::leanh::lean_inc_ref(v_a_6956_);
                v___x_7005_ = crate::leanh::lean_apply_5(
                    v___x_190__overap_7004_,
                    v_a_6956_,
                    v_a_6957_,
                    v_a_6958_,
                    v_a_6959_,
                    crate::leanh::lean_box(0),
                );
                return v___x_7005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toString___boxed(
    mut v_00_u03b1_7012_: *mut crate::leanh::LeanObject,
    mut v_inst_7013_: *mut crate::leanh::LeanObject,
    mut v_a_7014_: *mut crate::leanh::LeanObject,
    mut v_a_7015_: *mut crate::leanh::LeanObject,
    mut v_a_7016_: *mut crate::leanh::LeanObject,
    mut v_a_7017_: *mut crate::leanh::LeanObject,
    mut v_a_7018_: *mut crate::leanh::LeanObject,
    mut v_a_7019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7020_ = l_Lean_Compiler_LCNF_Probe_toString(
        v_00_u03b1_7012_,
        v_inst_7013_,
        v_a_7014_,
        v_a_7015_,
        v_a_7016_,
        v_a_7017_,
        v_a_7018_,
    );
    crate::leanh::lean_dec(v_a_7018_);
    crate::leanh::lean_dec_ref(v_a_7017_);
    crate::leanh::lean_dec(v_a_7016_);
    crate::leanh::lean_dec_ref(v_a_7015_);
    return v_res_7020_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_count___redArg(
    mut v_data_7021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7023_ = lean_array_get_size(v_data_7021_);
    v___x_7024_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_7025_ = lean_mk_empty_array_with_capacity(v___x_7024_);
    v___x_7026_ = lean_array_push(v___x_7025_, v___x_7023_);
    v___x_7027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7027_, 0, v___x_7026_);
    return v___x_7027_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(
    mut v_data_7028_: *mut crate::leanh::LeanObject,
    mut v_a_7029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7030_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_7028_);
    crate::leanh::lean_dec_ref(v_data_7028_);
    return v_res_7030_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_count(
    mut v_00_u03b1_7031_: *mut crate::leanh::LeanObject,
    mut v_data_7032_: *mut crate::leanh::LeanObject,
    mut v_a_7033_: *mut crate::leanh::LeanObject,
    mut v_a_7034_: *mut crate::leanh::LeanObject,
    mut v_a_7035_: *mut crate::leanh::LeanObject,
    mut v_a_7036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7038_ = lean_array_get_size(v_data_7032_);
    v___x_7039_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_7040_ = lean_mk_empty_array_with_capacity(v___x_7039_);
    v___x_7041_ = lean_array_push(v___x_7040_, v___x_7038_);
    v___x_7042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7042_, 0, v___x_7041_);
    return v___x_7042_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_count___boxed(
    mut v_00_u03b1_7043_: *mut crate::leanh::LeanObject,
    mut v_data_7044_: *mut crate::leanh::LeanObject,
    mut v_a_7045_: *mut crate::leanh::LeanObject,
    mut v_a_7046_: *mut crate::leanh::LeanObject,
    mut v_a_7047_: *mut crate::leanh::LeanObject,
    mut v_a_7048_: *mut crate::leanh::LeanObject,
    mut v_a_7049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7050_ = l_Lean_Compiler_LCNF_Probe_count(
        v_00_u03b1_7043_,
        v_data_7044_,
        v_a_7045_,
        v_a_7046_,
        v_a_7047_,
        v_a_7048_,
    );
    crate::leanh::lean_dec(v_a_7048_);
    crate::leanh::lean_dec_ref(v_a_7047_);
    crate::leanh::lean_dec(v_a_7046_);
    crate::leanh::lean_dec_ref(v_a_7045_);
    crate::leanh::lean_dec_ref(v_data_7044_);
    return v_res_7050_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sum___redArg(
    mut v_data_7052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: u8 = 0;
    let mut v___f_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: u8 = 0;
    let mut v___x_7066_: usize = 0;
    let mut v___x_7067_: usize = 0;
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: usize = 0;
    let mut v___x_7070_: usize = 0;
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7060_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7061_ = lean_array_get_size(v_data_7052_);
                v___x_7062_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9;
                v___x_7063_ = lean_nat_dec_lt(v___x_7060_, v___x_7061_);
                if v___x_7063_ == 0 {
                    crate::leanh::lean_dec_ref(v_data_7052_);
                    v___y_7055_ = v___x_7060_;
                    state = 1;
                    continue;
                } else {
                    v___f_7064_ = l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0;
                    v___x_7065_ = lean_nat_dec_le(v___x_7061_, v___x_7061_);
                    if v___x_7065_ == 0 {
                        if v___x_7063_ == 0 {
                            crate::leanh::lean_dec_ref(v_data_7052_);
                            v___y_7055_ = v___x_7060_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7066_ = 0usize;
                            v___x_7067_ = lean_usize_of_nat(v___x_7061_);
                            v___x_7068_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_7062_,
                                    v___f_7064_,
                                    v_data_7052_,
                                    v___x_7066_,
                                    v___x_7067_,
                                    v___x_7060_,
                                );
                            v___y_7055_ = v___x_7068_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7069_ = 0usize;
                        v___x_7070_ = lean_usize_of_nat(v___x_7061_);
                        v___x_7071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_7062_,
                            v___f_7064_,
                            v_data_7052_,
                            v___x_7069_,
                            v___x_7070_,
                            v___x_7060_,
                        );
                        v___y_7055_ = v___x_7071_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7056_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7057_ = lean_mk_empty_array_with_capacity(v___x_7056_);
                v___x_7058_ = lean_array_push(v___x_7057_, v___y_7055_);
                v___x_7059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7059_, 0, v___x_7058_);
                return v___x_7059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(
    mut v_data_7072_: *mut crate::leanh::LeanObject,
    mut v_a_7073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7074_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_7072_);
    return v_res_7074_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sum(
    mut v_data_7075_: *mut crate::leanh::LeanObject,
    mut v_a_7076_: *mut crate::leanh::LeanObject,
    mut v_a_7077_: *mut crate::leanh::LeanObject,
    mut v_a_7078_: *mut crate::leanh::LeanObject,
    mut v_a_7079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: u8 = 0;
    let mut v___f_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: u8 = 0;
    let mut v___x_7093_: usize = 0;
    let mut v___x_7094_: usize = 0;
    let mut v___x_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: usize = 0;
    let mut v___x_7097_: usize = 0;
    let mut v___x_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7087_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7088_ = lean_array_get_size(v_data_7075_);
                v___x_7089_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9;
                v___x_7090_ = lean_nat_dec_lt(v___x_7087_, v___x_7088_);
                if v___x_7090_ == 0 {
                    crate::leanh::lean_dec_ref(v_data_7075_);
                    v___y_7082_ = v___x_7087_;
                    state = 1;
                    continue;
                } else {
                    v___f_7091_ = l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0;
                    v___x_7092_ = lean_nat_dec_le(v___x_7088_, v___x_7088_);
                    if v___x_7092_ == 0 {
                        if v___x_7090_ == 0 {
                            crate::leanh::lean_dec_ref(v_data_7075_);
                            v___y_7082_ = v___x_7087_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7093_ = 0usize;
                            v___x_7094_ = lean_usize_of_nat(v___x_7088_);
                            v___x_7095_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_7089_,
                                    v___f_7091_,
                                    v_data_7075_,
                                    v___x_7093_,
                                    v___x_7094_,
                                    v___x_7087_,
                                );
                            v___y_7082_ = v___x_7095_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7096_ = 0usize;
                        v___x_7097_ = lean_usize_of_nat(v___x_7088_);
                        v___x_7098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_7089_,
                            v___f_7091_,
                            v_data_7075_,
                            v___x_7096_,
                            v___x_7097_,
                            v___x_7087_,
                        );
                        v___y_7082_ = v___x_7098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7083_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7084_ = lean_mk_empty_array_with_capacity(v___x_7083_);
                v___x_7085_ = lean_array_push(v___x_7084_, v___y_7082_);
                v___x_7086_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7086_, 0, v___x_7085_);
                return v___x_7086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_sum___boxed(
    mut v_data_7099_: *mut crate::leanh::LeanObject,
    mut v_a_7100_: *mut crate::leanh::LeanObject,
    mut v_a_7101_: *mut crate::leanh::LeanObject,
    mut v_a_7102_: *mut crate::leanh::LeanObject,
    mut v_a_7103_: *mut crate::leanh::LeanObject,
    mut v_a_7104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7105_ =
        l_Lean_Compiler_LCNF_Probe_sum(v_data_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_);
    crate::leanh::lean_dec(v_a_7103_);
    crate::leanh::lean_dec_ref(v_a_7102_);
    crate::leanh::lean_dec(v_a_7101_);
    crate::leanh::lean_dec_ref(v_a_7100_);
    return v_res_7105_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_tail___redArg(
    mut v_n_7106_: *mut crate::leanh::LeanObject,
    mut v_data_7107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7115_ = lean_array_get_size(v_data_7107_);
                v___x_7116_ = lean_nat_sub(v___x_7115_, v_n_7106_);
                v___x_7117_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7118_ = lean_nat_dec_le(v___x_7116_, v___x_7117_);
                if v___x_7118_ == 0 {
                    v_lower_7110_ = v___x_7116_;
                    v_upper_7111_ = v___x_7115_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_7116_);
                    v_lower_7110_ = v___x_7117_;
                    v_upper_7111_ = v___x_7115_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7112_ =
                    l_Array_toSubarray___redArg(v_data_7107_, v_lower_7110_, v_upper_7111_);
                v___x_7113_ = l_Subarray_copy___redArg(v___x_7112_);
                v___x_7114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7114_, 0, v___x_7113_);
                return v___x_7114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(
    mut v_n_7119_: *mut crate::leanh::LeanObject,
    mut v_data_7120_: *mut crate::leanh::LeanObject,
    mut v_a_7121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7122_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_7119_, v_data_7120_);
    crate::leanh::lean_dec(v_n_7119_);
    return v_res_7122_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_tail(
    mut v_00_u03b1_7123_: *mut crate::leanh::LeanObject,
    mut v_n_7124_: *mut crate::leanh::LeanObject,
    mut v_data_7125_: *mut crate::leanh::LeanObject,
    mut v_a_7126_: *mut crate::leanh::LeanObject,
    mut v_a_7127_: *mut crate::leanh::LeanObject,
    mut v_a_7128_: *mut crate::leanh::LeanObject,
    mut v_a_7129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7137_ = lean_array_get_size(v_data_7125_);
                v___x_7138_ = lean_nat_sub(v___x_7137_, v_n_7124_);
                v___x_7139_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7140_ = lean_nat_dec_le(v___x_7138_, v___x_7139_);
                if v___x_7140_ == 0 {
                    v_lower_7132_ = v___x_7138_;
                    v_upper_7133_ = v___x_7137_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_7138_);
                    v_lower_7132_ = v___x_7139_;
                    v_upper_7133_ = v___x_7137_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7134_ =
                    l_Array_toSubarray___redArg(v_data_7125_, v_lower_7132_, v_upper_7133_);
                v___x_7135_ = l_Subarray_copy___redArg(v___x_7134_);
                v___x_7136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7136_, 0, v___x_7135_);
                return v___x_7136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_tail___boxed(
    mut v_00_u03b1_7141_: *mut crate::leanh::LeanObject,
    mut v_n_7142_: *mut crate::leanh::LeanObject,
    mut v_data_7143_: *mut crate::leanh::LeanObject,
    mut v_a_7144_: *mut crate::leanh::LeanObject,
    mut v_a_7145_: *mut crate::leanh::LeanObject,
    mut v_a_7146_: *mut crate::leanh::LeanObject,
    mut v_a_7147_: *mut crate::leanh::LeanObject,
    mut v_a_7148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7149_ = l_Lean_Compiler_LCNF_Probe_tail(
        v_00_u03b1_7141_,
        v_n_7142_,
        v_data_7143_,
        v_a_7144_,
        v_a_7145_,
        v_a_7146_,
        v_a_7147_,
    );
    crate::leanh::lean_dec(v_a_7147_);
    crate::leanh::lean_dec_ref(v_a_7146_);
    crate::leanh::lean_dec(v_a_7145_);
    crate::leanh::lean_dec_ref(v_a_7144_);
    crate::leanh::lean_dec(v_n_7142_);
    return v_res_7149_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_head___redArg(
    mut v_n_7150_: *mut crate::leanh::LeanObject,
    mut v_data_7151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7153_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7154_ = l_Array_toSubarray___redArg(v_data_7151_, v___x_7153_, v_n_7150_);
    v___x_7155_ = l_Subarray_copy___redArg(v___x_7154_);
    v___x_7156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7156_, 0, v___x_7155_);
    return v___x_7156_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(
    mut v_n_7157_: *mut crate::leanh::LeanObject,
    mut v_data_7158_: *mut crate::leanh::LeanObject,
    mut v_a_7159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7160_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_7157_, v_data_7158_);
    return v_res_7160_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_head(
    mut v_00_u03b1_7161_: *mut crate::leanh::LeanObject,
    mut v_n_7162_: *mut crate::leanh::LeanObject,
    mut v_data_7163_: *mut crate::leanh::LeanObject,
    mut v_a_7164_: *mut crate::leanh::LeanObject,
    mut v_a_7165_: *mut crate::leanh::LeanObject,
    mut v_a_7166_: *mut crate::leanh::LeanObject,
    mut v_a_7167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7169_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7170_ = l_Array_toSubarray___redArg(v_data_7163_, v___x_7169_, v_n_7162_);
    v___x_7171_ = l_Subarray_copy___redArg(v___x_7170_);
    v___x_7172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7172_, 0, v___x_7171_);
    return v___x_7172_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_head___boxed(
    mut v_00_u03b1_7173_: *mut crate::leanh::LeanObject,
    mut v_n_7174_: *mut crate::leanh::LeanObject,
    mut v_data_7175_: *mut crate::leanh::LeanObject,
    mut v_a_7176_: *mut crate::leanh::LeanObject,
    mut v_a_7177_: *mut crate::leanh::LeanObject,
    mut v_a_7178_: *mut crate::leanh::LeanObject,
    mut v_a_7179_: *mut crate::leanh::LeanObject,
    mut v_a_7180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7181_ = l_Lean_Compiler_LCNF_Probe_head(
        v_00_u03b1_7173_,
        v_n_7174_,
        v_data_7175_,
        v_a_7176_,
        v_a_7177_,
        v_a_7178_,
        v_a_7179_,
    );
    crate::leanh::lean_dec(v_a_7179_);
    crate::leanh::lean_dec_ref(v_a_7178_);
    crate::leanh::lean_dec(v_a_7177_);
    crate::leanh::lean_dec_ref(v_a_7176_);
    return v_res_7181_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(
    mut v_probe_7190_: *mut crate::leanh::LeanObject,
    mut v___x_7191_: *mut crate::leanh::LeanObject,
    mut v___x_7192_: *mut crate::leanh::LeanObject,
    mut v___f_7193_: *mut crate::leanh::LeanObject,
    mut v_inst_7194_: *mut crate::leanh::LeanObject,
    mut v___x_7195_: *mut crate::leanh::LeanObject,
    mut v___x_7196_: *mut crate::leanh::LeanObject,
    mut v_decls_7197_: *mut crate::leanh::LeanObject,
    mut v___y_7198_: *mut crate::leanh::LeanObject,
    mut v___y_7199_: *mut crate::leanh::LeanObject,
    mut v___y_7200_: *mut crate::leanh::LeanObject,
    mut v___y_7201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7205_: u8 = 0;
    let mut v___x_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7208_: u8 = 0;
    let mut v___x_7210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7212_: u8 = 0;
    let mut v_unused_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7217_: u8 = 0;
    let mut v_inheritedTraceOptions_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: u8 = 0;
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077__overap_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7244_: u8 = 0;
    let mut v___x_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7248_: u8 = 0;
    let mut v_unused_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7253_: u8 = 0;
    let mut v___x_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7257_: u8 = 0;
    let mut v_isSharedCheck_7258_: u8 = 0;
    let mut v_a_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7262_: u8 = 0;
    let mut v___x_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_7201_);
                crate::leanh::lean_inc_ref(v___y_7200_);
                crate::leanh::lean_inc(v___y_7199_);
                crate::leanh::lean_inc_ref(v___y_7198_);
                crate::leanh::lean_inc_ref(v_decls_7197_);
                v___x_7203_ = crate::leanh::lean_apply_6(
                    v_probe_7190_,
                    v_decls_7197_,
                    v___y_7198_,
                    v___y_7199_,
                    v___y_7200_,
                    v___y_7201_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7203_) == 0 {
                    v_options_7204_ = crate::leanh::lean_ctor_get(v___y_7200_, 2);
                    v_hasTrace_7205_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_7204_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_7205_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_7196_);
                        crate::leanh::lean_dec_ref(v___x_7195_);
                        crate::leanh::lean_dec_ref(v_inst_7194_);
                        crate::leanh::lean_dec(v___f_7193_);
                        crate::leanh::lean_dec(v___x_7192_);
                        crate::leanh::lean_dec_ref(v___x_7191_);
                        v_isSharedCheck_7212_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7203_)) as u8;
                        if v_isSharedCheck_7212_ == 0 {
                            v_unused_7213_ = crate::leanh::lean_ctor_get(v___x_7203_, 0);
                            crate::leanh::lean_dec(v_unused_7213_);
                            v___x_7207_ = v___x_7203_;
                            v_isShared_7208_ = v_isSharedCheck_7212_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_7203_);
                            v___x_7207_ = crate::leanh::lean_box(0);
                            v_isShared_7208_ = v_isSharedCheck_7212_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7214_ = crate::leanh::lean_ctor_get(v___x_7203_, 0);
                        v_isSharedCheck_7258_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7203_)) as u8;
                        if v_isSharedCheck_7258_ == 0 {
                            v___x_7216_ = v___x_7203_;
                            v_isShared_7217_ = v_isSharedCheck_7258_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7214_);
                            crate::leanh::lean_dec(v___x_7203_);
                            v___x_7216_ = crate::leanh::lean_box(0);
                            v_isShared_7217_ = v_isSharedCheck_7258_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decls_7197_);
                    crate::leanh::lean_dec_ref(v___x_7196_);
                    crate::leanh::lean_dec_ref(v___x_7195_);
                    crate::leanh::lean_dec_ref(v_inst_7194_);
                    crate::leanh::lean_dec(v___f_7193_);
                    crate::leanh::lean_dec(v___x_7192_);
                    crate::leanh::lean_dec_ref(v___x_7191_);
                    v_a_7259_ = crate::leanh::lean_ctor_get(v___x_7203_, 0);
                    v_isSharedCheck_7266_ = (!crate::leanh::lean_is_exclusive(v___x_7203_)) as u8;
                    if v_isSharedCheck_7266_ == 0 {
                        v___x_7261_ = v___x_7203_;
                        v_isShared_7262_ = v_isSharedCheck_7266_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7259_);
                        crate::leanh::lean_dec(v___x_7203_);
                        v___x_7261_ = crate::leanh::lean_box(0);
                        v_isShared_7262_ = v_isSharedCheck_7266_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7208_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7207_, 0, v_decls_7197_);
                    v___x_7210_ = v___x_7207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7211_, 0, v_decls_7197_);
                    v___x_7210_ = v_reuseFailAlloc_7211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7210_;
            }
            3 => {
                v_inheritedTraceOptions_7218_ = crate::leanh::lean_ctor_get(v___y_7200_, 13);
                v___x_7219_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0;
                v___x_7220_ = l_Lean_Name_mkStr2(v___x_7219_, v___x_7191_);
                v___x_7221_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2;
                crate::leanh::lean_inc(v___x_7220_);
                v___x_7222_ = l_Lean_Name_append(v___x_7221_, v___x_7220_);
                v___x_7223_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_7218_,
                    v_options_7204_,
                    v___x_7222_,
                );
                crate::leanh::lean_dec(v___x_7222_);
                if v___x_7223_ == 0 {
                    crate::leanh::lean_dec(v___x_7220_);
                    crate::leanh::lean_dec(v_a_7214_);
                    crate::leanh::lean_dec_ref(v___x_7196_);
                    crate::leanh::lean_dec_ref(v___x_7195_);
                    crate::leanh::lean_dec_ref(v_inst_7194_);
                    crate::leanh::lean_dec(v___f_7193_);
                    crate::leanh::lean_dec(v___x_7192_);
                    if v_isShared_7217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7216_, 0, v_decls_7197_);
                        v___x_7225_ = v___x_7216_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7226_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7226_, 0, v_decls_7197_);
                        v___x_7225_ = v_reuseFailAlloc_7226_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7216_);
                    v___f_7227_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3;
                    v___x_7228_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4;
                    v___x_7229_ = l_Lean_Core_instMonadQuotationCoreM;
                    v___x_7230_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                        v___x_7228_,
                        v___x_7192_,
                        v___x_7229_,
                    );
                    v___x_7231_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
                        v___f_7227_,
                        v___f_7193_,
                        v___x_7230_,
                    );
                    v_toMonadRef_7232_ = crate::leanh::lean_ctor_get(v___x_7231_, 0);
                    crate::leanh::lean_inc_ref(v_toMonadRef_7232_);
                    crate::leanh::lean_dec_ref(v___x_7231_);
                    v___f_7233_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5;
                    v___x_7234_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6;
                    v___x_7235_ = lean_array_to_list(v_a_7214_);
                    v___x_7236_ = l_List_toString___redArg(v_inst_7194_, v___x_7235_);
                    v___x_7237_ = lean_string_append(v___x_7234_, v___x_7236_);
                    crate::leanh::lean_dec_ref(v___x_7236_);
                    v___x_7238_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7238_, 0, v___x_7237_);
                    v___x_7239_ = l_Lean_MessageData_ofFormat(v___x_7238_);
                    v___x_1077__overap_7240_ = l_Lean_addTrace___redArg(
                        v___x_7195_,
                        v___x_7196_,
                        v_toMonadRef_7232_,
                        v___f_7233_,
                        v___x_7220_,
                        v___x_7239_,
                    );
                    crate::leanh::lean_inc(v___y_7201_);
                    crate::leanh::lean_inc_ref(v___y_7200_);
                    crate::leanh::lean_inc(v___y_7199_);
                    crate::leanh::lean_inc_ref(v___y_7198_);
                    v___x_7241_ = crate::leanh::lean_apply_5(
                        v___x_1077__overap_7240_,
                        v___y_7198_,
                        v___y_7199_,
                        v___y_7200_,
                        v___y_7201_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7241_) == 0 {
                        v_isSharedCheck_7248_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7241_)) as u8;
                        if v_isSharedCheck_7248_ == 0 {
                            v_unused_7249_ = crate::leanh::lean_ctor_get(v___x_7241_, 0);
                            crate::leanh::lean_dec(v_unused_7249_);
                            v___x_7243_ = v___x_7241_;
                            v_isShared_7244_ = v_isSharedCheck_7248_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_7241_);
                            v___x_7243_ = crate::leanh::lean_box(0);
                            v_isShared_7244_ = v_isSharedCheck_7248_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_decls_7197_);
                        v_a_7250_ = crate::leanh::lean_ctor_get(v___x_7241_, 0);
                        v_isSharedCheck_7257_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7241_)) as u8;
                        if v_isSharedCheck_7257_ == 0 {
                            v___x_7252_ = v___x_7241_;
                            v_isShared_7253_ = v_isSharedCheck_7257_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7250_);
                            crate::leanh::lean_dec(v___x_7241_);
                            v___x_7252_ = crate::leanh::lean_box(0);
                            v_isShared_7253_ = v_isSharedCheck_7257_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_7225_;
            }
            5 => {
                if v_isShared_7244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7243_, 0, v_decls_7197_);
                    v___x_7246_ = v___x_7243_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7247_, 0, v_decls_7197_);
                    v___x_7246_ = v_reuseFailAlloc_7247_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7246_;
            }
            7 => {
                if v_isShared_7253_ == 0 {
                    v___x_7255_ = v___x_7252_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7256_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7256_, 0, v_a_7250_);
                    v___x_7255_ = v_reuseFailAlloc_7256_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7255_;
            }
            9 => {
                if v_isShared_7262_ == 0 {
                    v___x_7264_ = v___x_7261_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7265_, 0, v_a_7259_);
                    v___x_7264_ = v_reuseFailAlloc_7265_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(
    mut v_probe_7267_: *mut crate::leanh::LeanObject,
    mut v___x_7268_: *mut crate::leanh::LeanObject,
    mut v___x_7269_: *mut crate::leanh::LeanObject,
    mut v___f_7270_: *mut crate::leanh::LeanObject,
    mut v_inst_7271_: *mut crate::leanh::LeanObject,
    mut v___x_7272_: *mut crate::leanh::LeanObject,
    mut v___x_7273_: *mut crate::leanh::LeanObject,
    mut v_decls_7274_: *mut crate::leanh::LeanObject,
    mut v___y_7275_: *mut crate::leanh::LeanObject,
    mut v___y_7276_: *mut crate::leanh::LeanObject,
    mut v___y_7277_: *mut crate::leanh::LeanObject,
    mut v___y_7278_: *mut crate::leanh::LeanObject,
    mut v___y_7279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7280_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(
        v_probe_7267_,
        v___x_7268_,
        v___x_7269_,
        v___f_7270_,
        v_inst_7271_,
        v___x_7272_,
        v___x_7273_,
        v_decls_7274_,
        v___y_7275_,
        v___y_7276_,
        v___y_7277_,
        v___y_7278_,
    );
    crate::leanh::lean_dec(v___y_7278_);
    crate::leanh::lean_dec_ref(v___y_7277_);
    crate::leanh::lean_dec(v___y_7276_);
    crate::leanh::lean_dec_ref(v___y_7275_);
    return v_res_7280_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7283_ = l_Lean_Core_instMonadTraceCoreM;
    v___x_7284_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1;
    v___x_7285_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_7284_, v___x_7283_);
    return v___x_7285_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once),
        _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2,
    );
    v___f_7287_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0;
    v___x_7288_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_7287_, v___x_7286_);
    return v___x_7288_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toPass___redArg(
    mut v_inst_7292_: *mut crate::leanh::LeanObject,
    mut v_phase_7293_: u8,
    mut v_probe_7294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7315_: u8 = 0;
    let mut v_toFunctor_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7322_: u8 = 0;
    let mut v___f_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: u8 = 0;
    let mut v___x_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7346_: u8 = 0;
    let mut v_unused_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7348_: u8 = 0;
    let mut v_unused_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7295_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1,
                );
                v_toApplicative_7296_ = crate::leanh::lean_ctor_get(v___x_7295_, 0);
                v_toFunctor_7297_ = crate::leanh::lean_ctor_get(v_toApplicative_7296_, 0);
                v_toSeq_7298_ = crate::leanh::lean_ctor_get(v_toApplicative_7296_, 2);
                v_toSeqLeft_7299_ = crate::leanh::lean_ctor_get(v_toApplicative_7296_, 3);
                v_toSeqRight_7300_ = crate::leanh::lean_ctor_get(v_toApplicative_7296_, 4);
                v___f_7301_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2;
                v___f_7302_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_7297_, 2);
                v___f_7303_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7303_, 0, v_toFunctor_7297_);
                v___f_7304_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7304_, 0, v_toFunctor_7297_);
                v___x_7305_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7305_, 0, v___f_7303_);
                crate::leanh::lean_ctor_set(v___x_7305_, 1, v___f_7304_);
                crate::leanh::lean_inc(v_toSeqRight_7300_);
                v___f_7306_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7306_, 0, v_toSeqRight_7300_);
                crate::leanh::lean_inc(v_toSeqLeft_7299_);
                v___f_7307_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7307_, 0, v_toSeqLeft_7299_);
                crate::leanh::lean_inc(v_toSeq_7298_);
                v___f_7308_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7308_, 0, v_toSeq_7298_);
                v___x_7309_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7309_, 0, v___x_7305_);
                crate::leanh::lean_ctor_set(v___x_7309_, 1, v___f_7301_);
                crate::leanh::lean_ctor_set(v___x_7309_, 2, v___f_7308_);
                crate::leanh::lean_ctor_set(v___x_7309_, 3, v___f_7307_);
                crate::leanh::lean_ctor_set(v___x_7309_, 4, v___f_7306_);
                v___x_7310_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7310_, 0, v___x_7309_);
                crate::leanh::lean_ctor_set(v___x_7310_, 1, v___f_7302_);
                v___x_7311_ = l_StateRefT_x27_instMonad___redArg(v___x_7310_);
                v_toApplicative_7312_ = crate::leanh::lean_ctor_get(v___x_7311_, 0);
                v_isSharedCheck_7348_ = (!crate::leanh::lean_is_exclusive(v___x_7311_)) as u8;
                if v_isSharedCheck_7348_ == 0 {
                    v_unused_7349_ = crate::leanh::lean_ctor_get(v___x_7311_, 1);
                    crate::leanh::lean_dec(v_unused_7349_);
                    v___x_7314_ = v___x_7311_;
                    v_isShared_7315_ = v_isSharedCheck_7348_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_7312_);
                    crate::leanh::lean_dec(v___x_7311_);
                    v___x_7314_ = crate::leanh::lean_box(0);
                    v_isShared_7315_ = v_isSharedCheck_7348_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_7316_ = crate::leanh::lean_ctor_get(v_toApplicative_7312_, 0);
                v_toSeq_7317_ = crate::leanh::lean_ctor_get(v_toApplicative_7312_, 2);
                v_toSeqLeft_7318_ = crate::leanh::lean_ctor_get(v_toApplicative_7312_, 3);
                v_toSeqRight_7319_ = crate::leanh::lean_ctor_get(v_toApplicative_7312_, 4);
                v_isSharedCheck_7346_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_7312_)) as u8;
                if v_isSharedCheck_7346_ == 0 {
                    v_unused_7347_ = crate::leanh::lean_ctor_get(v_toApplicative_7312_, 1);
                    crate::leanh::lean_dec(v_unused_7347_);
                    v___x_7321_ = v_toApplicative_7312_;
                    v_isShared_7322_ = v_isSharedCheck_7346_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_7319_);
                    crate::leanh::lean_inc(v_toSeqLeft_7318_);
                    crate::leanh::lean_inc(v_toSeq_7317_);
                    crate::leanh::lean_inc(v_toFunctor_7316_);
                    crate::leanh::lean_dec(v_toApplicative_7312_);
                    v___x_7321_ = crate::leanh::lean_box(0);
                    v_isShared_7322_ = v_isSharedCheck_7346_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_7323_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4;
                v___f_7324_ = l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_7316_);
                v___f_7325_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7325_, 0, v_toFunctor_7316_);
                v___f_7326_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7326_, 0, v_toFunctor_7316_);
                v___x_7327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7327_, 0, v___f_7325_);
                crate::leanh::lean_ctor_set(v___x_7327_, 1, v___f_7326_);
                v___f_7328_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7328_, 0, v_toSeqRight_7319_);
                v___f_7329_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7329_, 0, v_toSeqLeft_7318_);
                v___f_7330_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7330_, 0, v_toSeq_7317_);
                if v_isShared_7322_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7321_, 4, v___f_7328_);
                    crate::leanh::lean_ctor_set(v___x_7321_, 3, v___f_7329_);
                    crate::leanh::lean_ctor_set(v___x_7321_, 2, v___f_7330_);
                    crate::leanh::lean_ctor_set(v___x_7321_, 1, v___f_7323_);
                    crate::leanh::lean_ctor_set(v___x_7321_, 0, v___x_7327_);
                    v___x_7332_ = v___x_7321_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7345_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7345_, 0, v___x_7327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7345_, 1, v___f_7323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7345_, 2, v___f_7330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7345_, 3, v___f_7329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7345_, 4, v___f_7328_);
                    v___x_7332_ = v_reuseFailAlloc_7345_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7315_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7314_, 1, v___f_7324_);
                    crate::leanh::lean_ctor_set(v___x_7314_, 0, v___x_7332_);
                    v___x_7334_ = v___x_7314_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7344_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7344_, 0, v___x_7332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7344_, 1, v___f_7324_);
                    v___x_7334_ = v_reuseFailAlloc_7344_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___f_7335_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0;
                v___x_7336_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1;
                v___x_7337_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3,
                );
                v___x_7338_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7339_ = 0;
                v___x_7340_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4;
                v___f_7341_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    13,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_7341_, 0, v_probe_7294_);
                crate::leanh::lean_closure_set(v___f_7341_, 1, v___x_7340_);
                crate::leanh::lean_closure_set(v___f_7341_, 2, v___x_7336_);
                crate::leanh::lean_closure_set(v___f_7341_, 3, v___f_7335_);
                crate::leanh::lean_closure_set(v___f_7341_, 4, v_inst_7292_);
                crate::leanh::lean_closure_set(v___f_7341_, 5, v___x_7334_);
                crate::leanh::lean_closure_set(v___f_7341_, 6, v___x_7337_);
                v___x_7342_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5;
                v___x_7343_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_7343_, 0, v___x_7338_);
                crate::leanh::lean_ctor_set(v___x_7343_, 1, v___x_7342_);
                crate::leanh::lean_ctor_set(v___x_7343_, 2, v___f_7341_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7343_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_phase_7293_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7343_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v_phase_7293_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7343_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                    v___x_7339_,
                );
                return v___x_7343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(
    mut v_inst_7350_: *mut crate::leanh::LeanObject,
    mut v_phase_7351_: *mut crate::leanh::LeanObject,
    mut v_probe_7352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_7353_: u8 = 0;
    let mut v_res_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_7353_ = (crate::leanh::lean_unbox(v_phase_7351_) as u8);
    v_res_7354_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(
        v_inst_7350_,
        v_phase_boxed_7353_,
        v_probe_7352_,
    );
    return v_res_7354_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toPass(
    mut v_00_u03b2_7355_: *mut crate::leanh::LeanObject,
    mut v_inst_7356_: *mut crate::leanh::LeanObject,
    mut v_phase_7357_: u8,
    mut v_probe_7358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7359_ =
        l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_7356_, v_phase_7357_, v_probe_7358_);
    return v___x_7359_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Probe_toPass___boxed(
    mut v_00_u03b2_7360_: *mut crate::leanh::LeanObject,
    mut v_inst_7361_: *mut crate::leanh::LeanObject,
    mut v_phase_7362_: *mut crate::leanh::LeanObject,
    mut v_probe_7363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_7364_: u8 = 0;
    let mut v_res_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_7364_ = (crate::leanh::lean_unbox(v_phase_7362_) as u8);
    v_res_7365_ = l_Lean_Compiler_LCNF_Probe_toPass(
        v_00_u03b2_7360_,
        v_inst_7361_,
        v_phase_boxed_7364_,
        v_probe_7363_,
    );
    return v_res_7365_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7424_ = crate::leanh::lean_unsigned_to_nat(4008565020);
    v___x_7425_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_;
    v___x_7426_ = l_Lean_Name_num___override(v___x_7425_, v___x_7424_);
    return v___x_7426_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7428_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_;
    v___x_7429_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
    v___x_7430_ = l_Lean_Name_str___override(v___x_7429_, v___x_7428_);
    return v___x_7430_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7432_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_;
    v___x_7433_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
    v___x_7434_ = l_Lean_Name_str___override(v___x_7433_, v___x_7432_);
    return v___x_7434_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7435_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_7436_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
    v___x_7437_ = l_Lean_Name_num___override(v___x_7436_, v___x_7435_);
    return v___x_7437_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7440_: u8 = 0;
    let mut v___x_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7439_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_;
    v___x_7440_ = 1;
    v___x_7441_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
    v___x_7442_ = l_Lean_registerTraceClass(v___x_7439_, v___x_7440_, v___x_7441_);
    return v___x_7442_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(
    mut v_a_7443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7444_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
    return v_res_7444_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Probing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Probing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Probing(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Probing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Probing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Probing(builtin);
}
