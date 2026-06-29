// Lean compiler output
// Module: Lean.Compiler.LCNF.PropagateBorrow
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PhaseExt
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed,
    lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_dec_eq, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_CtorInfo_isScalar, l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg,
    l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instBEqFVarId_beq___boxed, l_Lean_instHashableFVarId_hash,
    l_Lean_instHashableFVarId_hash___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
pub static mut l_Lean_Compiler_LCNF_instInhabitedOwnedness_default: u8 = 0;
pub static mut l_Lean_Compiler_LCNF_instInhabitedOwnedness: u8 = 0;
pub static l_Lean_Compiler_LCNF_instBEqOwnedness___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instBEqOwnedness_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instBEqOwnedness___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instBEqOwnedness___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instBEqOwnedness: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instBEqOwnedness___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__1_value: crate::leanh::LeanStringObject<105> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 105, m_capacity: 105, m_length: 104, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 97, 110, 97, 108, 121, 122, 101, 80, 114, 111, 112, 97, 103, 97, 116, 101, 100, 66, 111, 114, 114, 111, 119, 115, 46, 103, 101, 116, 80, 97, 114, 97, 109, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [103, 101, 116, 73, 110, 116, 101, 114, 110, 97, 108, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [103, 101, 116, 33, 73, 110, 116, 101, 114, 110, 97, 108, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 103, 101, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__4_value: crate::leanh::LeanStringObject<111> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 111, m_capacity: 111, m_length: 110, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 97, 110, 97, 108, 121, 122, 101, 80, 114, 111, 112, 97, 103, 97, 116, 101, 100, 66, 111, 114, 114, 111, 119, 115, 46, 99, 111, 108, 108, 101, 99, 116, 76, 101, 116, 86, 97, 108, 117, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__0_value: crate::leanh::LeanStringObject<107> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 107, m_capacity: 107, m_length: 106, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 97, 110, 97, 108, 121, 122, 101, 80, 114, 111, 112, 97, 103, 97, 116, 101, 100, 66, 111, 114, 114, 111, 119, 115, 46, 99, 111, 108, 108, 101, 99, 116, 67, 111, 100, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__0_value: crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 97, 112, 112, 108, 121, 79, 119, 110, 101, 100, 110, 101, 115, 115, 46, 103, 111, 67, 111, 100, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorIdx(
    mut v_x_2272_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2272_ {
        0 => {
            let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2273_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2273_;
        }
        1 => {
            let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2274_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2274_;
        }
        2 => {
            let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2275_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2275_;
        }
        _ => {
            let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2276_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2276_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorIdx___boxed(
    mut v_x_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2278_: u8 = 0;
    let mut v_res_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2278_ = (crate::leanh::lean_unbox(v_x_2277_) as u8);
    v_res_2279_ = l_Lean_Compiler_LCNF_Ownedness_ctorIdx(v_x_boxed_2278_);
    return v_res_2279_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_toCtorIdx(
    mut v_x_2280_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_Lean_Compiler_LCNF_Ownedness_ctorIdx(v_x_2280_);
    return v___x_2281_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_toCtorIdx___boxed(
    mut v_x_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2283_: u8 = 0;
    let mut v_res_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2283_ = (crate::leanh::lean_unbox(v_x_2282_) as u8);
    v_res_2284_ = l_Lean_Compiler_LCNF_Ownedness_toCtorIdx(v_x_4__boxed_2283_);
    return v_res_2284_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorElim___redArg(
    mut v_k_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2285_);
    return v_k_2285_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorElim___redArg___boxed(
    mut v_k_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2287_ = l_Lean_Compiler_LCNF_Ownedness_ctorElim___redArg(v_k_2286_);
    crate::leanh::lean_dec(v_k_2286_);
    return v_res_2287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorElim(
    mut v_motive_2288_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2289_: *mut crate::leanh::LeanObject,
    mut v_t_2290_: u8,
    mut v_h_2291_: *mut crate::leanh::LeanObject,
    mut v_k_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2292_);
    return v_k_2292_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorElim___boxed(
    mut v_motive_2293_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2294_: *mut crate::leanh::LeanObject,
    mut v_t_2295_: *mut crate::leanh::LeanObject,
    mut v_h_2296_: *mut crate::leanh::LeanObject,
    mut v_k_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2298_: u8 = 0;
    let mut v_res_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2298_ = (crate::leanh::lean_unbox(v_t_2295_) as u8);
    v_res_2299_ = l_Lean_Compiler_LCNF_Ownedness_ctorElim(
        v_motive_2293_,
        v_ctorIdx_2294_,
        v_t_boxed_2298_,
        v_h_2296_,
        v_k_2297_,
    );
    crate::leanh::lean_dec(v_k_2297_);
    crate::leanh::lean_dec(v_ctorIdx_2294_);
    return v_res_2299_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_bot_elim___redArg(
    mut v_bot_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_bot_2300_);
    return v_bot_2300_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_bot_elim___redArg___boxed(
    mut v_bot_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Lean_Compiler_LCNF_Ownedness_bot_elim___redArg(v_bot_2301_);
    crate::leanh::lean_dec(v_bot_2301_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_bot_elim(
    mut v_motive_2303_: *mut crate::leanh::LeanObject,
    mut v_t_2304_: u8,
    mut v_h_2305_: *mut crate::leanh::LeanObject,
    mut v_bot_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_bot_2306_);
    return v_bot_2306_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_bot_elim___boxed(
    mut v_motive_2307_: *mut crate::leanh::LeanObject,
    mut v_t_2308_: *mut crate::leanh::LeanObject,
    mut v_h_2309_: *mut crate::leanh::LeanObject,
    mut v_bot_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2311_: u8 = 0;
    let mut v_res_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2311_ = (crate::leanh::lean_unbox(v_t_2308_) as u8);
    v_res_2312_ = l_Lean_Compiler_LCNF_Ownedness_bot_elim(
        v_motive_2307_,
        v_t_boxed_2311_,
        v_h_2309_,
        v_bot_2310_,
    );
    crate::leanh::lean_dec(v_bot_2310_);
    return v_res_2312_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_borrow_elim___redArg(
    mut v_borrow_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_borrow_2313_);
    return v_borrow_2313_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_borrow_elim___redArg___boxed(
    mut v_borrow_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Lean_Compiler_LCNF_Ownedness_borrow_elim___redArg(v_borrow_2314_);
    crate::leanh::lean_dec(v_borrow_2314_);
    return v_res_2315_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_borrow_elim(
    mut v_motive_2316_: *mut crate::leanh::LeanObject,
    mut v_t_2317_: u8,
    mut v_h_2318_: *mut crate::leanh::LeanObject,
    mut v_borrow_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_borrow_2319_);
    return v_borrow_2319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_borrow_elim___boxed(
    mut v_motive_2320_: *mut crate::leanh::LeanObject,
    mut v_t_2321_: *mut crate::leanh::LeanObject,
    mut v_h_2322_: *mut crate::leanh::LeanObject,
    mut v_borrow_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2324_: u8 = 0;
    let mut v_res_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2324_ = (crate::leanh::lean_unbox(v_t_2321_) as u8);
    v_res_2325_ = l_Lean_Compiler_LCNF_Ownedness_borrow_elim(
        v_motive_2320_,
        v_t_boxed_2324_,
        v_h_2322_,
        v_borrow_2323_,
    );
    crate::leanh::lean_dec(v_borrow_2323_);
    return v_res_2325_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_own_elim___redArg(
    mut v_own_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_own_2326_);
    return v_own_2326_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_own_elim___redArg___boxed(
    mut v_own_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_Compiler_LCNF_Ownedness_own_elim___redArg(v_own_2327_);
    crate::leanh::lean_dec(v_own_2327_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_own_elim(
    mut v_motive_2329_: *mut crate::leanh::LeanObject,
    mut v_t_2330_: u8,
    mut v_h_2331_: *mut crate::leanh::LeanObject,
    mut v_own_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_own_2332_);
    return v_own_2332_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_own_elim___boxed(
    mut v_motive_2333_: *mut crate::leanh::LeanObject,
    mut v_t_2334_: *mut crate::leanh::LeanObject,
    mut v_h_2335_: *mut crate::leanh::LeanObject,
    mut v_own_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2337_: u8 = 0;
    let mut v_res_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2337_ = (crate::leanh::lean_unbox(v_t_2334_) as u8);
    v_res_2338_ = l_Lean_Compiler_LCNF_Ownedness_own_elim(
        v_motive_2333_,
        v_t_boxed_2337_,
        v_h_2335_,
        v_own_2336_,
    );
    crate::leanh::lean_dec(v_own_2336_);
    return v_res_2338_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_top_elim___redArg(
    mut v_top_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_top_2339_);
    return v_top_2339_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_top_elim___redArg___boxed(
    mut v_top_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Lean_Compiler_LCNF_Ownedness_top_elim___redArg(v_top_2340_);
    crate::leanh::lean_dec(v_top_2340_);
    return v_res_2341_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_top_elim(
    mut v_motive_2342_: *mut crate::leanh::LeanObject,
    mut v_t_2343_: u8,
    mut v_h_2344_: *mut crate::leanh::LeanObject,
    mut v_top_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_top_2345_);
    return v_top_2345_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_top_elim___boxed(
    mut v_motive_2346_: *mut crate::leanh::LeanObject,
    mut v_t_2347_: *mut crate::leanh::LeanObject,
    mut v_h_2348_: *mut crate::leanh::LeanObject,
    mut v_top_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2350_: u8 = 0;
    let mut v_res_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2350_ = (crate::leanh::lean_unbox(v_t_2347_) as u8);
    v_res_2351_ = l_Lean_Compiler_LCNF_Ownedness_top_elim(
        v_motive_2346_,
        v_t_boxed_2350_,
        v_h_2348_,
        v_top_2349_,
    );
    crate::leanh::lean_dec(v_top_2349_);
    return v_res_2351_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedOwnedness_default() -> u8 {
    let mut v___x_2352_: u8 = 0;
    v___x_2352_ = 0;
    return v___x_2352_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedOwnedness() -> u8 {
    let mut v___x_2353_: u8 = 0;
    v___x_2353_ = 0;
    return v___x_2353_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instBEqOwnedness_beq(
    mut v_x_2354_: u8,
    mut v_y_2355_: u8,
) -> u8 {
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u8 = 0;
    v___x_2356_ = l_Lean_Compiler_LCNF_Ownedness_ctorIdx(v_x_2354_);
    v___x_2357_ = l_Lean_Compiler_LCNF_Ownedness_ctorIdx(v_y_2355_);
    v___x_2358_ = lean_nat_dec_eq(v___x_2356_, v___x_2357_);
    crate::leanh::lean_dec(v___x_2357_);
    crate::leanh::lean_dec(v___x_2356_);
    return v___x_2358_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instBEqOwnedness_beq___boxed(
    mut v_x_2359_: *mut crate::leanh::LeanObject,
    mut v_y_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_2361_: u8 = 0;
    let mut v_y_18__boxed_2362_: u8 = 0;
    let mut v_res_2363_: u8 = 0;
    let mut v_r_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2361_ = (crate::leanh::lean_unbox(v_x_2359_) as u8);
    v_y_18__boxed_2362_ = (crate::leanh::lean_unbox(v_y_2360_) as u8);
    v_res_2363_ =
        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v_x_17__boxed_2361_, v_y_18__boxed_2362_);
    v_r_2364_ = crate::leanh::lean_box((v_res_2363_) as usize);
    return v_r_2364_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(
    mut v_x_2367_: u8,
    mut v_x_2368_: u8,
) -> u8 {
    match v_x_2367_ {
        0 => {
            return v_x_2368_;
        }
        1 => {
            if v_x_2368_ == 1 {
                return v_x_2368_;
            } else {
                let mut v___x_2369_: u8 = 0;
                v___x_2369_ = 3;
                return v___x_2369_;
            }
        }
        2 => {
            if v_x_2368_ == 2 {
                return v_x_2368_;
            } else {
                let mut v___x_2370_: u8 = 0;
                v___x_2370_ = 3;
                return v___x_2370_;
            }
        }
        _ => {
            let mut v___x_2371_: u8 = 0;
            v___x_2371_ = 3;
            return v___x_2371_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join___boxed(
    mut v_x_2372_: *mut crate::leanh::LeanObject,
    mut v_x_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_2374_: u8 = 0;
    let mut v_x_52__boxed_2375_: u8 = 0;
    let mut v_res_2376_: u8 = 0;
    let mut v_r_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_2374_ = (crate::leanh::lean_unbox(v_x_2372_) as u8);
    v_x_52__boxed_2375_ = (crate::leanh::lean_unbox(v_x_2373_) as u8);
    v_res_2376_ =
        l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(
            v_x_51__boxed_2374_,
            v_x_52__boxed_2375_,
        );
    v_r_2377_ = crate::leanh::lean_box((v_res_2376_) as usize);
    return v_r_2377_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2378_ = crate::leanh::lean_box(0);
    v___x_2379_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2380_ = lean_mk_array(v___x_2379_, v___x_2378_);
    return v___x_2380_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2381_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0,
    );
    v___x_2382_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2383_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
    crate::leanh::lean_ctor_set(v___x_2383_, 1, v___x_2381_);
    return v___x_2383_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2384_: u8 = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = 0;
    v___x_2385_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1,
    );
    v___x_2386_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2386_, 0, v___x_2385_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2386_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2384_,
    );
    return v___x_2386_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2387_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2,
    );
    return v___x_2387_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2388_ = l_Lean_Compiler_LCNF_instInhabitedState_default;
    return v___x_2388_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg(
    mut v_fvarId_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = lean_st_ref_get(v_a_2392_);
    v_values_2395_ = crate::leanh::lean_ctor_get(v___x_2394_, 0);
    crate::leanh::lean_inc_ref(v_values_2395_);
    crate::leanh::lean_dec(v___x_2394_);
    v___x_2396_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0;
    v___x_2397_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1;
    v___x_2398_ = 0;
    v___x_2399_ = crate::leanh::lean_box((v___x_2398_) as usize);
    v___x_2400_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v___x_2396_,
        v___x_2397_,
        v_values_2395_,
        v_fvarId_2391_,
        v___x_2399_,
    );
    crate::leanh::lean_dec(v___x_2399_);
    crate::leanh::lean_dec_ref(v_values_2395_);
    v___x_2401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2401_, 0, v___x_2400_);
    return v___x_2401_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___boxed(
    mut v_fvarId_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2405_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg(v_fvarId_2402_, v_a_2403_);
    crate::leanh::lean_dec(v_a_2403_);
    return v_res_2405_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness(
    mut v_fvarId_2406_: *mut crate::leanh::LeanObject,
    mut v_a_2407_: *mut crate::leanh::LeanObject,
    mut v_a_2408_: *mut crate::leanh::LeanObject,
    mut v_a_2409_: *mut crate::leanh::LeanObject,
    mut v_a_2410_: *mut crate::leanh::LeanObject,
    mut v_a_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2413_ = lean_st_ref_get(v_a_2407_);
    v_values_2414_ = crate::leanh::lean_ctor_get(v___x_2413_, 0);
    crate::leanh::lean_inc_ref(v_values_2414_);
    crate::leanh::lean_dec(v___x_2413_);
    v___x_2415_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0;
    v___x_2416_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1;
    v___x_2417_ = 0;
    v___x_2418_ = crate::leanh::lean_box((v___x_2417_) as usize);
    v___x_2419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v___x_2415_,
        v___x_2416_,
        v_values_2414_,
        v_fvarId_2406_,
        v___x_2418_,
    );
    crate::leanh::lean_dec(v___x_2418_);
    crate::leanh::lean_dec_ref(v_values_2414_);
    v___x_2420_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2420_, 0, v___x_2419_);
    return v___x_2420_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___boxed(
    mut v_fvarId_2421_: *mut crate::leanh::LeanObject,
    mut v_a_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
    mut v_a_2425_: *mut crate::leanh::LeanObject,
    mut v_a_2426_: *mut crate::leanh::LeanObject,
    mut v_a_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2428_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness(v_fvarId_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
    crate::leanh::lean_dec(v_a_2426_);
    crate::leanh::lean_dec_ref(v_a_2425_);
    crate::leanh::lean_dec(v_a_2424_);
    crate::leanh::lean_dec_ref(v_a_2423_);
    crate::leanh::lean_dec(v_a_2422_);
    return v_res_2428_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join___redArg(
    mut v_fvarId_2429_: *mut crate::leanh::LeanObject,
    mut v_v_2430_: u8,
    mut v_a_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: u8 = 0;
    let mut v_new_2447_: u8 = 0;
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: u8 = 0;
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2452_: u8 = 0;
    let mut v___x_2453_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_unused_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2433_ = lean_st_ref_take(v_a_2431_);
                v_values_2439_ = crate::leanh::lean_ctor_get(v___x_2433_, 0);
                crate::leanh::lean_inc_ref(v_values_2439_);
                v___x_2440_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0;
                v___x_2441_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1;
                v___x_2442_ = crate::leanh::lean_box(0);
                v___x_2443_ = 0;
                v___x_2444_ = crate::leanh::lean_box((v___x_2443_) as usize);
                crate::leanh::lean_inc(v_fvarId_2429_);
                v_old_2445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
                    v___x_2440_,
                    v___x_2441_,
                    v_values_2439_,
                    v_fvarId_2429_,
                    v___x_2444_,
                );
                crate::leanh::lean_dec(v___x_2444_);
                v___x_2446_ = (crate::leanh::lean_unbox(v_old_2445_) as u8);
                v_new_2447_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2446_, v_v_2430_);
                v___x_2448_ = (crate::leanh::lean_unbox(v_old_2445_) as u8);
                crate::leanh::lean_dec(v_old_2445_);
                v___x_2449_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2448_, v_new_2447_);
                if v___x_2449_ == 0 {
                    v_isSharedCheck_2459_ = (!crate::leanh::lean_is_exclusive(v___x_2433_)) as u8;
                    if v_isSharedCheck_2459_ == 0 {
                        v_unused_2460_ = crate::leanh::lean_ctor_get(v___x_2433_, 0);
                        crate::leanh::lean_dec(v_unused_2460_);
                        v___x_2451_ = v___x_2433_;
                        v_isShared_2452_ = v_isSharedCheck_2459_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2433_);
                        v___x_2451_ = crate::leanh::lean_box(0);
                        v_isShared_2452_ = v_isSharedCheck_2459_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_values_2439_);
                    crate::leanh::lean_dec(v_fvarId_2429_);
                    v_fst_2435_ = v___x_2442_;
                    v_snd_2436_ = v___x_2433_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2437_ = lean_st_ref_set(v_a_2431_, v_snd_2436_);
                v___x_2438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2438_, 0, v_fst_2435_);
                return v___x_2438_;
            }
            2 => {
                v___x_2453_ = 1;
                v___x_2454_ = crate::leanh::lean_box((v_new_2447_) as usize);
                v___x_2455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_2440_,
                    v___x_2441_,
                    v_values_2439_,
                    v_fvarId_2429_,
                    v___x_2454_,
                );
                if v_isShared_2452_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2451_, 0, v___x_2455_);
                    v___x_2457_ = v___x_2451_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
                    v___x_2457_ = v_reuseFailAlloc_2458_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2453_,
                );
                v_fst_2435_ = v___x_2442_;
                v_snd_2436_ = v___x_2457_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join___redArg___boxed(
    mut v_fvarId_2461_: *mut crate::leanh::LeanObject,
    mut v_v_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
    mut v_a_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_2465_: u8 = 0;
    let mut v_res_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_2465_ = (crate::leanh::lean_unbox(v_v_2462_) as u8);
    v_res_2466_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join___redArg(v_fvarId_2461_, v_v_boxed_2465_, v_a_2463_);
    crate::leanh::lean_dec(v_a_2463_);
    return v_res_2466_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join(
    mut v_fvarId_2467_: *mut crate::leanh::LeanObject,
    mut v_v_2468_: u8,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
    mut v_a_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
    mut v_a_2473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: u8 = 0;
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v_new_2489_: u8 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_unused_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2475_ = lean_st_ref_take(v_a_2469_);
                v_values_2481_ = crate::leanh::lean_ctor_get(v___x_2475_, 0);
                crate::leanh::lean_inc_ref(v_values_2481_);
                v___x_2482_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0;
                v___x_2483_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1;
                v___x_2484_ = crate::leanh::lean_box(0);
                v___x_2485_ = 0;
                v___x_2486_ = crate::leanh::lean_box((v___x_2485_) as usize);
                crate::leanh::lean_inc(v_fvarId_2467_);
                v_old_2487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
                    v___x_2482_,
                    v___x_2483_,
                    v_values_2481_,
                    v_fvarId_2467_,
                    v___x_2486_,
                );
                crate::leanh::lean_dec(v___x_2486_);
                v___x_2488_ = (crate::leanh::lean_unbox(v_old_2487_) as u8);
                v_new_2489_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2488_, v_v_2468_);
                v___x_2490_ = (crate::leanh::lean_unbox(v_old_2487_) as u8);
                crate::leanh::lean_dec(v_old_2487_);
                v___x_2491_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2490_, v_new_2489_);
                if v___x_2491_ == 0 {
                    v_isSharedCheck_2501_ = (!crate::leanh::lean_is_exclusive(v___x_2475_)) as u8;
                    if v_isSharedCheck_2501_ == 0 {
                        v_unused_2502_ = crate::leanh::lean_ctor_get(v___x_2475_, 0);
                        crate::leanh::lean_dec(v_unused_2502_);
                        v___x_2493_ = v___x_2475_;
                        v_isShared_2494_ = v_isSharedCheck_2501_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2475_);
                        v___x_2493_ = crate::leanh::lean_box(0);
                        v_isShared_2494_ = v_isSharedCheck_2501_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_values_2481_);
                    crate::leanh::lean_dec(v_fvarId_2467_);
                    v_fst_2477_ = v___x_2484_;
                    v_snd_2478_ = v___x_2475_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2479_ = lean_st_ref_set(v_a_2469_, v_snd_2478_);
                v___x_2480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2480_, 0, v_fst_2477_);
                return v___x_2480_;
            }
            2 => {
                v___x_2495_ = 1;
                v___x_2496_ = crate::leanh::lean_box((v_new_2489_) as usize);
                v___x_2497_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_2482_,
                    v___x_2483_,
                    v_values_2481_,
                    v_fvarId_2467_,
                    v___x_2496_,
                );
                if v_isShared_2494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2497_);
                    v___x_2499_ = v___x_2493_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2499_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2495_,
                );
                v_fst_2477_ = v___x_2484_;
                v_snd_2478_ = v___x_2499_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join___boxed(
    mut v_fvarId_2503_: *mut crate::leanh::LeanObject,
    mut v_v_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_2511_: u8 = 0;
    let mut v_res_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_2511_ = (crate::leanh::lean_unbox(v_v_2504_) as u8);
    v_res_2512_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join(v_fvarId_2503_, v_v_boxed_2511_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
    crate::leanh::lean_dec(v_a_2509_);
    crate::leanh::lean_dec_ref(v_a_2508_);
    crate::leanh::lean_dec(v_a_2507_);
    crate::leanh::lean_dec_ref(v_a_2506_);
    crate::leanh::lean_dec(v_a_2505_);
    return v_res_2512_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2513_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_2518_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0(
    mut v_msg_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
    mut v___y_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v_toFunctor_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v___f_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v_toFunctor_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___f_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405__overap_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut v_unused_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut v_unused_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_unused_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v_unused_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2526_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0);
                v___x_2527_ = l_StateRefT_x27_instMonad___redArg(v___x_2526_);
                v_toApplicative_2528_ = crate::leanh::lean_ctor_get(v___x_2527_, 0);
                v_isSharedCheck_2590_ = (!crate::leanh::lean_is_exclusive(v___x_2527_)) as u8;
                if v_isSharedCheck_2590_ == 0 {
                    v_unused_2591_ = crate::leanh::lean_ctor_get(v___x_2527_, 1);
                    crate::leanh::lean_dec(v_unused_2591_);
                    v___x_2530_ = v___x_2527_;
                    v_isShared_2531_ = v_isSharedCheck_2590_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2528_);
                    crate::leanh::lean_dec(v___x_2527_);
                    v___x_2530_ = crate::leanh::lean_box(0);
                    v_isShared_2531_ = v_isSharedCheck_2590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2532_ = crate::leanh::lean_ctor_get(v_toApplicative_2528_, 0);
                v_toSeq_2533_ = crate::leanh::lean_ctor_get(v_toApplicative_2528_, 2);
                v_toSeqLeft_2534_ = crate::leanh::lean_ctor_get(v_toApplicative_2528_, 3);
                v_toSeqRight_2535_ = crate::leanh::lean_ctor_get(v_toApplicative_2528_, 4);
                v_isSharedCheck_2588_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2528_)) as u8;
                if v_isSharedCheck_2588_ == 0 {
                    v_unused_2589_ = crate::leanh::lean_ctor_get(v_toApplicative_2528_, 1);
                    crate::leanh::lean_dec(v_unused_2589_);
                    v___x_2537_ = v_toApplicative_2528_;
                    v_isShared_2538_ = v_isSharedCheck_2588_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2535_);
                    crate::leanh::lean_inc(v_toSeqLeft_2534_);
                    crate::leanh::lean_inc(v_toSeq_2533_);
                    crate::leanh::lean_inc(v_toFunctor_2532_);
                    crate::leanh::lean_dec(v_toApplicative_2528_);
                    v___x_2537_ = crate::leanh::lean_box(0);
                    v_isShared_2538_ = v_isSharedCheck_2588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2539_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1;
                v___f_2540_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2532_);
                v___f_2541_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2541_, 0, v_toFunctor_2532_);
                v___f_2542_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2542_, 0, v_toFunctor_2532_);
                v___x_2543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2543_, 0, v___f_2541_);
                crate::leanh::lean_ctor_set(v___x_2543_, 1, v___f_2542_);
                v___f_2544_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2544_, 0, v_toSeqRight_2535_);
                v___f_2545_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2545_, 0, v_toSeqLeft_2534_);
                v___f_2546_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2546_, 0, v_toSeq_2533_);
                if v_isShared_2538_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2537_, 4, v___f_2544_);
                    crate::leanh::lean_ctor_set(v___x_2537_, 3, v___f_2545_);
                    crate::leanh::lean_ctor_set(v___x_2537_, 2, v___f_2546_);
                    crate::leanh::lean_ctor_set(v___x_2537_, 1, v___f_2539_);
                    crate::leanh::lean_ctor_set(v___x_2537_, 0, v___x_2543_);
                    v___x_2548_ = v___x_2537_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2587_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___f_2539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 2, v___f_2546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 3, v___f_2545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 4, v___f_2544_);
                    v___x_2548_ = v_reuseFailAlloc_2587_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2530_, 1, v___f_2540_);
                    crate::leanh::lean_ctor_set(v___x_2530_, 0, v___x_2548_);
                    v___x_2550_ = v___x_2530_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___f_2540_);
                    v___x_2550_ = v_reuseFailAlloc_2586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2551_ = l_StateRefT_x27_instMonad___redArg(v___x_2550_);
                v_toApplicative_2552_ = crate::leanh::lean_ctor_get(v___x_2551_, 0);
                v_isSharedCheck_2584_ = (!crate::leanh::lean_is_exclusive(v___x_2551_)) as u8;
                if v_isSharedCheck_2584_ == 0 {
                    v_unused_2585_ = crate::leanh::lean_ctor_get(v___x_2551_, 1);
                    crate::leanh::lean_dec(v_unused_2585_);
                    v___x_2554_ = v___x_2551_;
                    v_isShared_2555_ = v_isSharedCheck_2584_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2552_);
                    crate::leanh::lean_dec(v___x_2551_);
                    v___x_2554_ = crate::leanh::lean_box(0);
                    v_isShared_2555_ = v_isSharedCheck_2584_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2556_ = crate::leanh::lean_ctor_get(v_toApplicative_2552_, 0);
                v_toSeq_2557_ = crate::leanh::lean_ctor_get(v_toApplicative_2552_, 2);
                v_toSeqLeft_2558_ = crate::leanh::lean_ctor_get(v_toApplicative_2552_, 3);
                v_toSeqRight_2559_ = crate::leanh::lean_ctor_get(v_toApplicative_2552_, 4);
                v_isSharedCheck_2582_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2552_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v_unused_2583_ = crate::leanh::lean_ctor_get(v_toApplicative_2552_, 1);
                    crate::leanh::lean_dec(v_unused_2583_);
                    v___x_2561_ = v_toApplicative_2552_;
                    v_isShared_2562_ = v_isSharedCheck_2582_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2559_);
                    crate::leanh::lean_inc(v_toSeqLeft_2558_);
                    crate::leanh::lean_inc(v_toSeq_2557_);
                    crate::leanh::lean_inc(v_toFunctor_2556_);
                    crate::leanh::lean_dec(v_toApplicative_2552_);
                    v___x_2561_ = crate::leanh::lean_box(0);
                    v_isShared_2562_ = v_isSharedCheck_2582_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2563_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3;
                v___f_2564_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_2556_);
                v___f_2565_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2565_, 0, v_toFunctor_2556_);
                v___f_2566_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2566_, 0, v_toFunctor_2556_);
                v___x_2567_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2567_, 0, v___f_2565_);
                crate::leanh::lean_ctor_set(v___x_2567_, 1, v___f_2566_);
                v___f_2568_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2568_, 0, v_toSeqRight_2559_);
                v___f_2569_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2569_, 0, v_toSeqLeft_2558_);
                v___f_2570_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2570_, 0, v_toSeq_2557_);
                if v_isShared_2562_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2561_, 4, v___f_2568_);
                    crate::leanh::lean_ctor_set(v___x_2561_, 3, v___f_2569_);
                    crate::leanh::lean_ctor_set(v___x_2561_, 2, v___f_2570_);
                    crate::leanh::lean_ctor_set(v___x_2561_, 1, v___f_2563_);
                    crate::leanh::lean_ctor_set(v___x_2561_, 0, v___x_2567_);
                    v___x_2572_ = v___x_2561_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___f_2563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 2, v___f_2570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 3, v___f_2569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 4, v___f_2568_);
                    v___x_2572_ = v_reuseFailAlloc_2581_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2555_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2554_, 1, v___f_2564_);
                    crate::leanh::lean_ctor_set(v___x_2554_, 0, v___x_2572_);
                    v___x_2574_ = v___x_2554_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___f_2564_);
                    v___x_2574_ = v_reuseFailAlloc_2580_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2575_ = l_StateRefT_x27_instMonad___redArg(v___x_2574_);
                v___x_2576_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5);
                v___x_2577_ = l_instInhabitedOfMonad___redArg(v___x_2575_, v___x_2576_);
                v___x_405__overap_2578_ = lean_panic_fn_borrowed(v___x_2577_, v_msg_2519_);
                crate::leanh::lean_dec(v___x_2577_);
                crate::leanh::lean_inc(v___y_2524_);
                crate::leanh::lean_inc_ref(v___y_2523_);
                crate::leanh::lean_inc(v___y_2522_);
                crate::leanh::lean_inc_ref(v___y_2521_);
                crate::leanh::lean_inc(v___y_2520_);
                v___x_2579_ = crate::leanh::lean_apply_6(
                    v___x_405__overap_2578_,
                    v___y_2520_,
                    v___y_2521_,
                    v___y_2522_,
                    v___y_2523_,
                    v___y_2524_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___boxed(
    mut v_msg_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2599_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0(v_msg_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
    crate::leanh::lean_dec(v___y_2597_);
    crate::leanh::lean_dec_ref(v___y_2596_);
    crate::leanh::lean_dec(v___y_2595_);
    crate::leanh::lean_dec_ref(v___y_2594_);
    crate::leanh::lean_dec(v___y_2593_);
    return v_res_2599_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2603_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_2604_ = crate::leanh::lean_unsigned_to_nat(43);
    v___x_2605_ = crate::leanh::lean_unsigned_to_nat(61);
    v___x_2606_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__1;
    v___x_2607_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0;
    v___x_2608_ = l_mkPanicMessageWithDecl(
        v___x_2607_,
        v___x_2606_,
        v___x_2605_,
        v___x_2604_,
        v___x_2603_,
    );
    return v___x_2608_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams(
    mut v_f_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v_val_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2628_: u8 = 0;
    let mut v_a_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2616_ =
                    l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_f_2609_, v_a_2614_);
                if crate::leanh::lean_obj_tag(v___x_2616_) == 0 {
                    v_a_2617_ = crate::leanh::lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2628_ = (!crate::leanh::lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2628_ == 0 {
                        v___x_2619_ = v___x_2616_;
                        v_isShared_2620_ = v_isSharedCheck_2628_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2617_);
                        crate::leanh::lean_dec(v___x_2616_);
                        v___x_2619_ = crate::leanh::lean_box(0);
                        v_isShared_2620_ = v_isSharedCheck_2628_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2629_ = crate::leanh::lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2636_ = (!crate::leanh::lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2636_ == 0 {
                        v___x_2631_ = v___x_2616_;
                        v_isShared_2632_ = v_isSharedCheck_2636_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2629_);
                        crate::leanh::lean_dec(v___x_2616_);
                        v___x_2631_ = crate::leanh::lean_box(0);
                        v_isShared_2632_ = v_isSharedCheck_2636_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2617_) == 1 {
                    v_val_2621_ = crate::leanh::lean_ctor_get(v_a_2617_, 0);
                    crate::leanh::lean_inc(v_val_2621_);
                    crate::leanh::lean_dec_ref_known(v_a_2617_, 1);
                    v_params_2622_ = crate::leanh::lean_ctor_get(v_val_2621_, 3);
                    crate::leanh::lean_inc_ref(v_params_2622_);
                    crate::leanh::lean_dec(v_val_2621_);
                    if v_isShared_2620_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2619_, 0, v_params_2622_);
                        v___x_2624_ = v___x_2619_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_params_2622_);
                        v___x_2624_ = v_reuseFailAlloc_2625_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2619_);
                    crate::leanh::lean_dec(v_a_2617_);
                    v___x_2626_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3);
                    v___x_2627_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0(v___x_2626_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    return v___x_2627_;
                }
            }
            2 => {
                return v___x_2624_;
            }
            3 => {
                if v_isShared_2632_ == 0 {
                    v___x_2634_ = v___x_2631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
                    v___x_2634_ = v_reuseFailAlloc_2635_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___boxed(
    mut v_f_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v_a_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_a_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
    mut v_a_2643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2644_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams(v_f_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
    crate::leanh::lean_dec(v_a_2642_);
    crate::leanh::lean_dec_ref(v_a_2641_);
    crate::leanh::lean_dec(v_a_2640_);
    crate::leanh::lean_dec_ref(v_a_2639_);
    crate::leanh::lean_dec(v_a_2638_);
    return v_res_2644_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(
    mut v_msg_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
    mut v___y_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v_toFunctor_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___f_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v_toFunctor_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___f_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397__overap_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2708_: u8 = 0;
    let mut v_unused_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut v_unused_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_unused_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2716_: u8 = 0;
    let mut v_unused_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0);
                v___x_2653_ = l_StateRefT_x27_instMonad___redArg(v___x_2652_);
                v_toApplicative_2654_ = crate::leanh::lean_ctor_get(v___x_2653_, 0);
                v_isSharedCheck_2716_ = (!crate::leanh::lean_is_exclusive(v___x_2653_)) as u8;
                if v_isSharedCheck_2716_ == 0 {
                    v_unused_2717_ = crate::leanh::lean_ctor_get(v___x_2653_, 1);
                    crate::leanh::lean_dec(v_unused_2717_);
                    v___x_2656_ = v___x_2653_;
                    v_isShared_2657_ = v_isSharedCheck_2716_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2654_);
                    crate::leanh::lean_dec(v___x_2653_);
                    v___x_2656_ = crate::leanh::lean_box(0);
                    v_isShared_2657_ = v_isSharedCheck_2716_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2658_ = crate::leanh::lean_ctor_get(v_toApplicative_2654_, 0);
                v_toSeq_2659_ = crate::leanh::lean_ctor_get(v_toApplicative_2654_, 2);
                v_toSeqLeft_2660_ = crate::leanh::lean_ctor_get(v_toApplicative_2654_, 3);
                v_toSeqRight_2661_ = crate::leanh::lean_ctor_get(v_toApplicative_2654_, 4);
                v_isSharedCheck_2714_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2654_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v_unused_2715_ = crate::leanh::lean_ctor_get(v_toApplicative_2654_, 1);
                    crate::leanh::lean_dec(v_unused_2715_);
                    v___x_2663_ = v_toApplicative_2654_;
                    v_isShared_2664_ = v_isSharedCheck_2714_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2661_);
                    crate::leanh::lean_inc(v_toSeqLeft_2660_);
                    crate::leanh::lean_inc(v_toSeq_2659_);
                    crate::leanh::lean_inc(v_toFunctor_2658_);
                    crate::leanh::lean_dec(v_toApplicative_2654_);
                    v___x_2663_ = crate::leanh::lean_box(0);
                    v_isShared_2664_ = v_isSharedCheck_2714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2665_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1;
                v___f_2666_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2658_);
                v___f_2667_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2667_, 0, v_toFunctor_2658_);
                v___f_2668_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2668_, 0, v_toFunctor_2658_);
                v___x_2669_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2669_, 0, v___f_2667_);
                crate::leanh::lean_ctor_set(v___x_2669_, 1, v___f_2668_);
                v___f_2670_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2670_, 0, v_toSeqRight_2661_);
                v___f_2671_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2671_, 0, v_toSeqLeft_2660_);
                v___f_2672_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2672_, 0, v_toSeq_2659_);
                if v_isShared_2664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2663_, 4, v___f_2670_);
                    crate::leanh::lean_ctor_set(v___x_2663_, 3, v___f_2671_);
                    crate::leanh::lean_ctor_set(v___x_2663_, 2, v___f_2672_);
                    crate::leanh::lean_ctor_set(v___x_2663_, 1, v___f_2665_);
                    crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2669_);
                    v___x_2674_ = v___x_2663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___f_2665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 2, v___f_2672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 3, v___f_2671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 4, v___f_2670_);
                    v___x_2674_ = v_reuseFailAlloc_2713_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2657_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2656_, 1, v___f_2666_);
                    crate::leanh::lean_ctor_set(v___x_2656_, 0, v___x_2674_);
                    v___x_2676_ = v___x_2656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___f_2666_);
                    v___x_2676_ = v_reuseFailAlloc_2712_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2677_ = l_StateRefT_x27_instMonad___redArg(v___x_2676_);
                v_toApplicative_2678_ = crate::leanh::lean_ctor_get(v___x_2677_, 0);
                v_isSharedCheck_2710_ = (!crate::leanh::lean_is_exclusive(v___x_2677_)) as u8;
                if v_isSharedCheck_2710_ == 0 {
                    v_unused_2711_ = crate::leanh::lean_ctor_get(v___x_2677_, 1);
                    crate::leanh::lean_dec(v_unused_2711_);
                    v___x_2680_ = v___x_2677_;
                    v_isShared_2681_ = v_isSharedCheck_2710_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2678_);
                    crate::leanh::lean_dec(v___x_2677_);
                    v___x_2680_ = crate::leanh::lean_box(0);
                    v_isShared_2681_ = v_isSharedCheck_2710_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2682_ = crate::leanh::lean_ctor_get(v_toApplicative_2678_, 0);
                v_toSeq_2683_ = crate::leanh::lean_ctor_get(v_toApplicative_2678_, 2);
                v_toSeqLeft_2684_ = crate::leanh::lean_ctor_get(v_toApplicative_2678_, 3);
                v_toSeqRight_2685_ = crate::leanh::lean_ctor_get(v_toApplicative_2678_, 4);
                v_isSharedCheck_2708_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2678_)) as u8;
                if v_isSharedCheck_2708_ == 0 {
                    v_unused_2709_ = crate::leanh::lean_ctor_get(v_toApplicative_2678_, 1);
                    crate::leanh::lean_dec(v_unused_2709_);
                    v___x_2687_ = v_toApplicative_2678_;
                    v_isShared_2688_ = v_isSharedCheck_2708_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2685_);
                    crate::leanh::lean_inc(v_toSeqLeft_2684_);
                    crate::leanh::lean_inc(v_toSeq_2683_);
                    crate::leanh::lean_inc(v_toFunctor_2682_);
                    crate::leanh::lean_dec(v_toApplicative_2678_);
                    v___x_2687_ = crate::leanh::lean_box(0);
                    v_isShared_2688_ = v_isSharedCheck_2708_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2689_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3;
                v___f_2690_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_2682_);
                v___f_2691_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2691_, 0, v_toFunctor_2682_);
                v___f_2692_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2692_, 0, v_toFunctor_2682_);
                v___x_2693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2693_, 0, v___f_2691_);
                crate::leanh::lean_ctor_set(v___x_2693_, 1, v___f_2692_);
                v___f_2694_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2694_, 0, v_toSeqRight_2685_);
                v___f_2695_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2695_, 0, v_toSeqLeft_2684_);
                v___f_2696_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2696_, 0, v_toSeq_2683_);
                if v_isShared_2688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2687_, 4, v___f_2694_);
                    crate::leanh::lean_ctor_set(v___x_2687_, 3, v___f_2695_);
                    crate::leanh::lean_ctor_set(v___x_2687_, 2, v___f_2696_);
                    crate::leanh::lean_ctor_set(v___x_2687_, 1, v___f_2689_);
                    crate::leanh::lean_ctor_set(v___x_2687_, 0, v___x_2693_);
                    v___x_2698_ = v___x_2687_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2707_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___f_2689_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 2, v___f_2696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 3, v___f_2695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 4, v___f_2694_);
                    v___x_2698_ = v_reuseFailAlloc_2707_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2681_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2680_, 1, v___f_2690_);
                    crate::leanh::lean_ctor_set(v___x_2680_, 0, v___x_2698_);
                    v___x_2700_ = v___x_2680_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___f_2690_);
                    v___x_2700_ = v_reuseFailAlloc_2706_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2701_ = l_StateRefT_x27_instMonad___redArg(v___x_2700_);
                v___x_2702_ = crate::leanh::lean_box(0);
                v___x_2703_ = l_instInhabitedOfMonad___redArg(v___x_2701_, v___x_2702_);
                v___x_3397__overap_2704_ = lean_panic_fn_borrowed(v___x_2703_, v_msg_2645_);
                crate::leanh::lean_dec(v___x_2703_);
                crate::leanh::lean_inc(v___y_2650_);
                crate::leanh::lean_inc_ref(v___y_2649_);
                crate::leanh::lean_inc(v___y_2648_);
                crate::leanh::lean_inc_ref(v___y_2647_);
                crate::leanh::lean_inc(v___y_2646_);
                v___x_2705_ = crate::leanh::lean_apply_6(
                    v___x_3397__overap_2704_,
                    v___y_2646_,
                    v___y_2647_,
                    v___y_2648_,
                    v___y_2649_,
                    v___y_2650_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2___boxed(
    mut v_msg_2718_: *mut crate::leanh::LeanObject,
    mut v___y_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
    mut v___y_2721_: *mut crate::leanh::LeanObject,
    mut v___y_2722_: *mut crate::leanh::LeanObject,
    mut v___y_2723_: *mut crate::leanh::LeanObject,
    mut v___y_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(v_msg_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
    crate::leanh::lean_dec(v___y_2723_);
    crate::leanh::lean_dec_ref(v___y_2722_);
    crate::leanh::lean_dec(v___y_2721_);
    crate::leanh::lean_dec_ref(v___y_2720_);
    crate::leanh::lean_dec(v___y_2719_);
    return v_res_2725_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4___redArg(
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_b_2727_: *mut crate::leanh::LeanObject,
    mut v_x_2728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2735_: u8 = 0;
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2728_) == 0 {
                    crate::leanh::lean_dec(v_b_2727_);
                    crate::leanh::lean_dec(v_a_2726_);
                    return v_x_2728_;
                } else {
                    v_key_2729_ = crate::leanh::lean_ctor_get(v_x_2728_, 0);
                    v_value_2730_ = crate::leanh::lean_ctor_get(v_x_2728_, 1);
                    v_tail_2731_ = crate::leanh::lean_ctor_get(v_x_2728_, 2);
                    v_isSharedCheck_2743_ = (!crate::leanh::lean_is_exclusive(v_x_2728_)) as u8;
                    if v_isSharedCheck_2743_ == 0 {
                        v___x_2733_ = v_x_2728_;
                        v_isShared_2734_ = v_isSharedCheck_2743_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2731_);
                        crate::leanh::lean_inc(v_value_2730_);
                        crate::leanh::lean_inc(v_key_2729_);
                        crate::leanh::lean_dec(v_x_2728_);
                        v___x_2733_ = crate::leanh::lean_box(0);
                        v_isShared_2734_ = v_isSharedCheck_2743_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2735_ = l_Lean_instBEqFVarId_beq(v_key_2729_, v_a_2726_);
                if v___x_2735_ == 0 {
                    v___x_2736_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4___redArg(v_a_2726_, v_b_2727_, v_tail_2731_);
                    if v_isShared_2734_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2733_, 2, v___x_2736_);
                        v___x_2738_ = v___x_2733_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2739_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_key_2729_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_value_2730_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 2, v___x_2736_);
                        v___x_2738_ = v_reuseFailAlloc_2739_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2730_);
                    crate::leanh::lean_dec(v_key_2729_);
                    if v_isShared_2734_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2733_, 1, v_b_2727_);
                        crate::leanh::lean_ctor_set(v___x_2733_, 0, v_a_2726_);
                        v___x_2741_ = v___x_2733_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2742_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2726_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_b_2727_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_tail_2731_);
                        v___x_2741_ = v_reuseFailAlloc_2742_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2738_;
            }
            3 => {
                return v___x_2741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5_spec__6___redArg(
    mut v_x_2744_: *mut crate::leanh::LeanObject,
    mut v_x_2745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: u64 = 0;
    let mut v___x_2754_: u64 = 0;
    let mut v___x_2755_: u64 = 0;
    let mut v_fold_2756_: u64 = 0;
    let mut v___x_2757_: u64 = 0;
    let mut v___x_2758_: u64 = 0;
    let mut v___x_2759_: u64 = 0;
    let mut v___x_2760_: usize = 0;
    let mut v___x_2761_: usize = 0;
    let mut v___x_2762_: usize = 0;
    let mut v___x_2763_: usize = 0;
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2745_) == 0 {
                    return v_x_2744_;
                } else {
                    v_key_2746_ = crate::leanh::lean_ctor_get(v_x_2745_, 0);
                    v_value_2747_ = crate::leanh::lean_ctor_get(v_x_2745_, 1);
                    v_tail_2748_ = crate::leanh::lean_ctor_get(v_x_2745_, 2);
                    v_isSharedCheck_2771_ = (!crate::leanh::lean_is_exclusive(v_x_2745_)) as u8;
                    if v_isSharedCheck_2771_ == 0 {
                        v___x_2750_ = v_x_2745_;
                        v_isShared_2751_ = v_isSharedCheck_2771_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2748_);
                        crate::leanh::lean_inc(v_value_2747_);
                        crate::leanh::lean_inc(v_key_2746_);
                        crate::leanh::lean_dec(v_x_2745_);
                        v___x_2750_ = crate::leanh::lean_box(0);
                        v_isShared_2751_ = v_isSharedCheck_2771_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2752_ = lean_array_get_size(v_x_2744_);
                v___x_2753_ = l_Lean_instHashableFVarId_hash(v_key_2746_);
                v___x_2754_ = 32u64;
                v___x_2755_ = lean_uint64_shift_right(v___x_2753_, v___x_2754_);
                v_fold_2756_ = lean_uint64_xor(v___x_2753_, v___x_2755_);
                v___x_2757_ = 16u64;
                v___x_2758_ = lean_uint64_shift_right(v_fold_2756_, v___x_2757_);
                v___x_2759_ = lean_uint64_xor(v_fold_2756_, v___x_2758_);
                v___x_2760_ = lean_uint64_to_usize(v___x_2759_);
                v___x_2761_ = lean_usize_of_nat(v___x_2752_);
                v___x_2762_ = 1usize;
                v___x_2763_ = lean_usize_sub(v___x_2761_, v___x_2762_);
                v___x_2764_ = lean_usize_land(v___x_2760_, v___x_2763_);
                v___x_2765_ = lean_array_uget_borrowed(v_x_2744_, v___x_2764_);
                crate::leanh::lean_inc(v___x_2765_);
                if v_isShared_2751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2750_, 2, v___x_2765_);
                    v___x_2767_ = v___x_2750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_key_2746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_value_2747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 2, v___x_2765_);
                    v___x_2767_ = v_reuseFailAlloc_2770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2768_ = lean_array_uset(v_x_2744_, v___x_2764_, v___x_2767_);
                v_x_2744_ = v___x_2768_;
                v_x_2745_ = v_tail_2748_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5___redArg(
    mut v_i_2772_: *mut crate::leanh::LeanObject,
    mut v_source_2773_: *mut crate::leanh::LeanObject,
    mut v_target_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: u8 = 0;
    let mut v_es_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2775_ = lean_array_get_size(v_source_2773_);
                v___x_2776_ = lean_nat_dec_lt(v_i_2772_, v___x_2775_);
                if v___x_2776_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2773_);
                    crate::leanh::lean_dec(v_i_2772_);
                    return v_target_2774_;
                } else {
                    v_es_2777_ = lean_array_fget(v_source_2773_, v_i_2772_);
                    v___x_2778_ = crate::leanh::lean_box(0);
                    v_source_2779_ = lean_array_fset(v_source_2773_, v_i_2772_, v___x_2778_);
                    v_target_2780_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5_spec__6___redArg(v_target_2774_, v_es_2777_);
                    v___x_2781_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2782_ = lean_nat_add(v_i_2772_, v___x_2781_);
                    crate::leanh::lean_dec(v_i_2772_);
                    v_i_2772_ = v___x_2782_;
                    v_source_2773_ = v_source_2779_;
                    v_target_2774_ = v_target_2780_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3___redArg(
    mut v_data_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2785_ = lean_array_get_size(v_data_2784_);
    v___x_2786_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2787_ = lean_nat_mul(v___x_2785_, v___x_2786_);
    v___x_2788_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2789_ = crate::leanh::lean_box(0);
    v___x_2790_ = lean_mk_array(v_nbuckets_2787_, v___x_2789_);
    v___x_2791_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5___redArg(v___x_2788_, v_data_2784_, v___x_2790_);
    return v___x_2791_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg(
    mut v_a_2792_: *mut crate::leanh::LeanObject,
    mut v_x_2793_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2794_: u8 = 0;
    let mut v_key_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2793_) == 0 {
                    v___x_2794_ = 0;
                    return v___x_2794_;
                } else {
                    v_key_2795_ = crate::leanh::lean_ctor_get(v_x_2793_, 0);
                    v_tail_2796_ = crate::leanh::lean_ctor_get(v_x_2793_, 2);
                    v___x_2797_ = l_Lean_instBEqFVarId_beq(v_key_2795_, v_a_2792_);
                    if v___x_2797_ == 0 {
                        v_x_2793_ = v_tail_2796_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2797_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg___boxed(
    mut v_a_2799_: *mut crate::leanh::LeanObject,
    mut v_x_2800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2801_: u8 = 0;
    let mut v_r_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg(v_a_2799_, v_x_2800_);
    crate::leanh::lean_dec(v_x_2800_);
    crate::leanh::lean_dec(v_a_2799_);
    v_r_2802_ = crate::leanh::lean_box((v_res_2801_) as usize);
    return v_r_2802_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(
    mut v_m_2803_: *mut crate::leanh::LeanObject,
    mut v_a_2804_: *mut crate::leanh::LeanObject,
    mut v_b_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: u64 = 0;
    let mut v___x_2813_: u64 = 0;
    let mut v___x_2814_: u64 = 0;
    let mut v_fold_2815_: u64 = 0;
    let mut v___x_2816_: u64 = 0;
    let mut v___x_2817_: u64 = 0;
    let mut v___x_2818_: u64 = 0;
    let mut v___x_2819_: usize = 0;
    let mut v___x_2820_: usize = 0;
    let mut v___x_2821_: usize = 0;
    let mut v___x_2822_: usize = 0;
    let mut v___x_2823_: usize = 0;
    let mut v_bkt_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v_val_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2806_ = crate::leanh::lean_ctor_get(v_m_2803_, 0);
                v_buckets_2807_ = crate::leanh::lean_ctor_get(v_m_2803_, 1);
                v_isSharedCheck_2850_ = (!crate::leanh::lean_is_exclusive(v_m_2803_)) as u8;
                if v_isSharedCheck_2850_ == 0 {
                    v___x_2809_ = v_m_2803_;
                    v_isShared_2810_ = v_isSharedCheck_2850_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2807_);
                    crate::leanh::lean_inc(v_size_2806_);
                    crate::leanh::lean_dec(v_m_2803_);
                    v___x_2809_ = crate::leanh::lean_box(0);
                    v_isShared_2810_ = v_isSharedCheck_2850_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2811_ = lean_array_get_size(v_buckets_2807_);
                v___x_2812_ = l_Lean_instHashableFVarId_hash(v_a_2804_);
                v___x_2813_ = 32u64;
                v___x_2814_ = lean_uint64_shift_right(v___x_2812_, v___x_2813_);
                v_fold_2815_ = lean_uint64_xor(v___x_2812_, v___x_2814_);
                v___x_2816_ = 16u64;
                v___x_2817_ = lean_uint64_shift_right(v_fold_2815_, v___x_2816_);
                v___x_2818_ = lean_uint64_xor(v_fold_2815_, v___x_2817_);
                v___x_2819_ = lean_uint64_to_usize(v___x_2818_);
                v___x_2820_ = lean_usize_of_nat(v___x_2811_);
                v___x_2821_ = 1usize;
                v___x_2822_ = lean_usize_sub(v___x_2820_, v___x_2821_);
                v___x_2823_ = lean_usize_land(v___x_2819_, v___x_2822_);
                v_bkt_2824_ = lean_array_uget_borrowed(v_buckets_2807_, v___x_2823_);
                v___x_2825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg(v_a_2804_, v_bkt_2824_);
                if v___x_2825_ == 0 {
                    v___x_2826_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2827_ = lean_nat_add(v_size_2806_, v___x_2826_);
                    crate::leanh::lean_dec(v_size_2806_);
                    crate::leanh::lean_inc(v_bkt_2824_);
                    v___x_2828_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2828_, 0, v_a_2804_);
                    crate::leanh::lean_ctor_set(v___x_2828_, 1, v_b_2805_);
                    crate::leanh::lean_ctor_set(v___x_2828_, 2, v_bkt_2824_);
                    v_buckets_x27_2829_ =
                        lean_array_uset(v_buckets_2807_, v___x_2823_, v___x_2828_);
                    v___x_2830_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2831_ = lean_nat_mul(v_size_x27_2827_, v___x_2830_);
                    v___x_2832_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2833_ = lean_nat_div(v___x_2831_, v___x_2832_);
                    crate::leanh::lean_dec(v___x_2831_);
                    v___x_2834_ = lean_array_get_size(v_buckets_x27_2829_);
                    v___x_2835_ = lean_nat_dec_le(v___x_2833_, v___x_2834_);
                    crate::leanh::lean_dec(v___x_2833_);
                    if v___x_2835_ == 0 {
                        v_val_2836_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3___redArg(v_buckets_x27_2829_);
                        if v_isShared_2810_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2809_, 1, v_val_2836_);
                            crate::leanh::lean_ctor_set(v___x_2809_, 0, v_size_x27_2827_);
                            v___x_2838_ = v___x_2809_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2839_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2839_,
                                0,
                                v_size_x27_2827_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_val_2836_);
                            v___x_2838_ = v_reuseFailAlloc_2839_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2810_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2809_, 1, v_buckets_x27_2829_);
                            crate::leanh::lean_ctor_set(v___x_2809_, 0, v_size_x27_2827_);
                            v___x_2841_ = v___x_2809_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2842_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2842_,
                                0,
                                v_size_x27_2827_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2842_,
                                1,
                                v_buckets_x27_2829_,
                            );
                            v___x_2841_ = v_reuseFailAlloc_2842_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2824_);
                    v___x_2843_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2844_ =
                        lean_array_uset(v_buckets_2807_, v___x_2823_, v___x_2843_);
                    v___x_2845_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4___redArg(v_a_2804_, v_b_2805_, v_bkt_2824_);
                    v___x_2846_ = lean_array_uset(v_buckets_x27_2844_, v___x_2823_, v___x_2845_);
                    if v_isShared_2810_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2809_, 1, v___x_2846_);
                        v___x_2848_ = v___x_2809_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2849_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_size_2806_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 1, v___x_2846_);
                        v___x_2848_ = v_reuseFailAlloc_2849_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2838_;
            }
            3 => {
                return v___x_2841_;
            }
            4 => {
                return v___x_2848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___redArg(
    mut v_a_2851_: *mut crate::leanh::LeanObject,
    mut v_fallback_2852_: *mut crate::leanh::LeanObject,
    mut v_x_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2853_) == 0 {
                    crate::leanh::lean_inc(v_fallback_2852_);
                    return v_fallback_2852_;
                } else {
                    v_key_2854_ = crate::leanh::lean_ctor_get(v_x_2853_, 0);
                    v_value_2855_ = crate::leanh::lean_ctor_get(v_x_2853_, 1);
                    v_tail_2856_ = crate::leanh::lean_ctor_get(v_x_2853_, 2);
                    v___x_2857_ = l_Lean_instBEqFVarId_beq(v_key_2854_, v_a_2851_);
                    if v___x_2857_ == 0 {
                        v_x_2853_ = v_tail_2856_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2855_);
                        return v_value_2855_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___redArg___boxed(
    mut v_a_2859_: *mut crate::leanh::LeanObject,
    mut v_fallback_2860_: *mut crate::leanh::LeanObject,
    mut v_x_2861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2862_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___redArg(v_a_2859_, v_fallback_2860_, v_x_2861_);
    crate::leanh::lean_dec(v_x_2861_);
    crate::leanh::lean_dec(v_fallback_2860_);
    crate::leanh::lean_dec(v_a_2859_);
    return v_res_2862_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(
    mut v_m_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_fallback_2865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u64 = 0;
    let mut v___x_2869_: u64 = 0;
    let mut v___x_2870_: u64 = 0;
    let mut v_fold_2871_: u64 = 0;
    let mut v___x_2872_: u64 = 0;
    let mut v___x_2873_: u64 = 0;
    let mut v___x_2874_: u64 = 0;
    let mut v___x_2875_: usize = 0;
    let mut v___x_2876_: usize = 0;
    let mut v___x_2877_: usize = 0;
    let mut v___x_2878_: usize = 0;
    let mut v___x_2879_: usize = 0;
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2866_ = crate::leanh::lean_ctor_get(v_m_2863_, 1);
    v___x_2867_ = lean_array_get_size(v_buckets_2866_);
    v___x_2868_ = l_Lean_instHashableFVarId_hash(v_a_2864_);
    v___x_2869_ = 32u64;
    v___x_2870_ = lean_uint64_shift_right(v___x_2868_, v___x_2869_);
    v_fold_2871_ = lean_uint64_xor(v___x_2868_, v___x_2870_);
    v___x_2872_ = 16u64;
    v___x_2873_ = lean_uint64_shift_right(v_fold_2871_, v___x_2872_);
    v___x_2874_ = lean_uint64_xor(v_fold_2871_, v___x_2873_);
    v___x_2875_ = lean_uint64_to_usize(v___x_2874_);
    v___x_2876_ = lean_usize_of_nat(v___x_2867_);
    v___x_2877_ = 1usize;
    v___x_2878_ = lean_usize_sub(v___x_2876_, v___x_2877_);
    v___x_2879_ = lean_usize_land(v___x_2875_, v___x_2878_);
    v___x_2880_ = lean_array_uget_borrowed(v_buckets_2866_, v___x_2879_);
    v___x_2881_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___redArg(v_a_2864_, v_fallback_2865_, v___x_2880_);
    return v___x_2881_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg___boxed(
    mut v_m_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
    mut v_fallback_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_m_2882_, v_a_2883_, v_fallback_2884_);
    crate::leanh::lean_dec(v_fallback_2884_);
    crate::leanh::lean_dec(v_a_2883_);
    crate::leanh::lean_dec_ref(v_m_2882_);
    return v_res_2885_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2891_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_2892_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2893_ = crate::leanh::lean_unsigned_to_nat(135);
    v___x_2894_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__4;
    v___x_2895_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0;
    v___x_2896_ = l_mkPanicMessageWithDecl(
        v___x_2895_,
        v___x_2894_,
        v___x_2893_,
        v___x_2892_,
        v___x_2891_,
    );
    return v___x_2896_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue(
    mut v_z_2897_: *mut crate::leanh::LeanObject,
    mut v_v_2898_: *mut crate::leanh::LeanObject,
    mut v_a_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
    mut v_a_2901_: *mut crate::leanh::LeanObject,
    mut v_a_2902_: *mut crate::leanh::LeanObject,
    mut v_a_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2913_: u8 = 0;
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v_new_2921_: u8 = 0;
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_unused_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2953_: u8 = 0;
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v_new_2961_: u8 = 0;
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2967_: u8 = 0;
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2973_: u8 = 0;
    let mut v_unused_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: u8 = 0;
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: u8 = 0;
    let mut v_new_2993_: u8 = 0;
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_unused_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: u8 = 0;
    let mut v___x_3015_: u8 = 0;
    let mut v_pre_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v_args_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: u8 = 0;
    let mut v_new_3041_: u8 = 0;
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3052_: u8 = 0;
    let mut v_unused_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v___y_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: u8 = 0;
    let mut v_new_3078_: u8 = 0;
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_unused_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: u8 = 0;
    let mut v_new_3113_: u8 = 0;
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3118_: u8 = 0;
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_unused_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: u8 = 0;
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: u8 = 0;
    let mut v_new_3143_: u8 = 0;
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3149_: u8 = 0;
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut v_unused_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: u8 = 0;
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: u8 = 0;
    let mut v_new_3170_: u8 = 0;
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3175_: u8 = 0;
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut v_unused_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: u8 = 0;
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: u8 = 0;
    let mut v_new_3197_: u8 = 0;
    let mut v___x_3198_: u8 = 0;
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3202_: u8 = 0;
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut v_unused_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v_new_3224_: u8 = 0;
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3226_: u8 = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3229_: u8 = 0;
    let mut v___x_3230_: u8 = 0;
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_unused_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: u8 = 0;
    let mut v_new_3251_: u8 = 0;
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_unused_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3267_: u8 = 0;
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v_new_3283_: u8 = 0;
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3289_: u8 = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v_unused_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_unused_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_v_2898_) {
                6 => {
                    v_var_2975_ = crate::leanh::lean_ctor_get(v_v_2898_, 1);
                    crate::leanh::lean_inc(v_var_2975_);
                    crate::leanh::lean_dec_ref_known(v_v_2898_, 2);
                    v___x_2976_ = lean_st_ref_get(v_a_2899_);
                    v___x_2977_ = lean_st_ref_take(v_a_2899_);
                    v_values_2983_ = crate::leanh::lean_ctor_get(v___x_2976_, 0);
                    crate::leanh::lean_inc_ref(v_values_2983_);
                    crate::leanh::lean_dec(v___x_2976_);
                    v_values_2984_ = crate::leanh::lean_ctor_get(v___x_2977_, 0);
                    crate::leanh::lean_inc_ref(v_values_2984_);
                    v___x_2985_ = 0;
                    v___x_2986_ = crate::leanh::lean_box((v___x_2985_) as usize);
                    v___x_2987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_2983_, v_var_2975_, v___x_2986_);
                    crate::leanh::lean_dec(v___x_2986_);
                    crate::leanh::lean_dec(v_var_2975_);
                    crate::leanh::lean_dec_ref(v_values_2983_);
                    v___x_2988_ = crate::leanh::lean_box(0);
                    v___x_2989_ = crate::leanh::lean_box((v___x_2985_) as usize);
                    v_old_2990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_2984_, v_z_2897_, v___x_2989_);
                    crate::leanh::lean_dec(v___x_2989_);
                    v___x_2991_ = (crate::leanh::lean_unbox(v_old_2990_) as u8);
                    v___x_2992_ = (crate::leanh::lean_unbox(v___x_2987_) as u8);
                    crate::leanh::lean_dec(v___x_2987_);
                    v_new_2993_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2991_, v___x_2992_);
                    v___x_2994_ = (crate::leanh::lean_unbox(v_old_2990_) as u8);
                    crate::leanh::lean_dec(v_old_2990_);
                    v___x_2995_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2994_, v_new_2993_);
                    if v___x_2995_ == 0 {
                        v_isSharedCheck_3005_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2977_)) as u8;
                        if v_isSharedCheck_3005_ == 0 {
                            v_unused_3006_ = crate::leanh::lean_ctor_get(v___x_2977_, 0);
                            crate::leanh::lean_dec(v_unused_3006_);
                            v___x_2997_ = v___x_2977_;
                            v_isShared_2998_ = v_isSharedCheck_3005_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2977_);
                            v___x_2997_ = crate::leanh::lean_box(0);
                            v_isShared_2998_ = v_isSharedCheck_3005_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_2984_);
                        crate::leanh::lean_dec(v_z_2897_);
                        v_fst_2979_ = v___x_2988_;
                        v_snd_2980_ = v___x_2977_;
                        state = 11;
                        continue;
                    }
                }
                9 => {
                    v_fn_3007_ = crate::leanh::lean_ctor_get(v_v_2898_, 0);
                    crate::leanh::lean_inc(v_fn_3007_);
                    v_args_3008_ = crate::leanh::lean_ctor_get(v_v_2898_, 1);
                    crate::leanh::lean_inc_ref(v_args_3008_);
                    crate::leanh::lean_dec_ref_known(v_v_2898_, 2);
                    if crate::leanh::lean_obj_tag(v_fn_3007_) == 1 {
                        v_pre_3016_ = crate::leanh::lean_ctor_get(v_fn_3007_, 0);
                        crate::leanh::lean_inc(v_pre_3016_);
                        if crate::leanh::lean_obj_tag(v_pre_3016_) == 1 {
                            v_pre_3017_ = crate::leanh::lean_ctor_get(v_pre_3016_, 0);
                            if crate::leanh::lean_obj_tag(v_pre_3017_) == 0 {
                                v_str_3018_ = crate::leanh::lean_ctor_get(v_fn_3007_, 1);
                                crate::leanh::lean_inc_ref(v_str_3018_);
                                crate::leanh::lean_dec_ref_known(v_fn_3007_, 2);
                                v_str_3019_ = crate::leanh::lean_ctor_get(v_pre_3016_, 1);
                                crate::leanh::lean_inc_ref(v_str_3019_);
                                crate::leanh::lean_dec_ref_known(v_pre_3016_, 2);
                                v___x_3020_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__0;
                                v___x_3021_ = lean_string_dec_eq(v_str_3019_, v___x_3020_);
                                crate::leanh::lean_dec_ref(v_str_3019_);
                                if v___x_3021_ == 0 {
                                    crate::leanh::lean_dec_ref(v_str_3018_);
                                    v___y_3010_ = v_a_2899_;
                                    state = 14;
                                    continue;
                                } else {
                                    v___x_3056_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__1;
                                    v___x_3057_ = lean_string_dec_eq(v_str_3018_, v___x_3056_);
                                    if v___x_3057_ == 0 {
                                        v___x_3058_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__2;
                                        v___x_3059_ = lean_string_dec_eq(v_str_3018_, v___x_3058_);
                                        if v___x_3059_ == 0 {
                                            v___x_3093_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__3;
                                            v___x_3094_ =
                                                lean_string_dec_eq(v_str_3018_, v___x_3093_);
                                            crate::leanh::lean_dec_ref(v_str_3018_);
                                            if v___x_3094_ == 0 {
                                                v___y_3010_ = v_a_2899_;
                                                state = 14;
                                                continue;
                                            } else {
                                                v_args_3023_ = v_args_3008_;
                                                v___y_3024_ = v_a_2899_;
                                                state = 15;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_str_3018_);
                                            v___x_3095_ = crate::leanh::lean_box(0);
                                            v___x_3096_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_3097_ = lean_array_get_borrowed(
                                                v___x_3095_,
                                                v_args_3008_,
                                                v___x_3096_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_3097_) == 1 {
                                                v_fvarId_3098_ =
                                                    crate::leanh::lean_ctor_get(v___x_3097_, 0);
                                                v___x_3099_ = lean_st_ref_get(v_a_2899_);
                                                v___x_3100_ = lean_st_ref_take(v_a_2899_);
                                                v_values_3104_ =
                                                    crate::leanh::lean_ctor_get(v___x_3099_, 0);
                                                crate::leanh::lean_inc_ref(v_values_3104_);
                                                crate::leanh::lean_dec(v___x_3099_);
                                                v_values_3105_ =
                                                    crate::leanh::lean_ctor_get(v___x_3100_, 0);
                                                crate::leanh::lean_inc_ref(v_values_3105_);
                                                v___x_3106_ = 0;
                                                v___x_3107_ =
                                                    crate::leanh::lean_box((v___x_3106_) as usize);
                                                v___x_3108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3104_, v_fvarId_3098_, v___x_3107_);
                                                crate::leanh::lean_dec(v___x_3107_);
                                                crate::leanh::lean_dec_ref(v_values_3104_);
                                                v___x_3109_ =
                                                    crate::leanh::lean_box((v___x_3106_) as usize);
                                                v_old_3110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3105_, v_z_2897_, v___x_3109_);
                                                crate::leanh::lean_dec(v___x_3109_);
                                                v___x_3111_ =
                                                    (crate::leanh::lean_unbox(v_old_3110_) as u8);
                                                v___x_3112_ =
                                                    (crate::leanh::lean_unbox(v___x_3108_) as u8);
                                                crate::leanh::lean_dec(v___x_3108_);
                                                v_new_3113_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3111_, v___x_3112_);
                                                v___x_3114_ =
                                                    (crate::leanh::lean_unbox(v_old_3110_) as u8);
                                                crate::leanh::lean_dec(v_old_3110_);
                                                v___x_3115_ =
                                                    l_Lean_Compiler_LCNF_instBEqOwnedness_beq(
                                                        v___x_3114_,
                                                        v_new_3113_,
                                                    );
                                                if v___x_3115_ == 0 {
                                                    v_isSharedCheck_3124_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_3100_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3124_ == 0 {
                                                        v_unused_3125_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___x_3100_,
                                                                0,
                                                            );
                                                        crate::leanh::lean_dec(v_unused_3125_);
                                                        v___x_3117_ = v___x_3100_;
                                                        v_isShared_3118_ = v_isSharedCheck_3124_;
                                                        state = 22;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_3100_);
                                                        v___x_3117_ = crate::leanh::lean_box(0);
                                                        v_isShared_3118_ = v_isSharedCheck_3124_;
                                                        state = 22;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_values_3105_);
                                                    v_snd_3102_ = v___x_3100_;
                                                    state = 21;
                                                    continue;
                                                }
                                            } else {
                                                v___y_3061_ = v_a_2899_;
                                                state = 18;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_str_3018_);
                                        v_args_3023_ = v_args_3008_;
                                        v___y_3024_ = v_a_2899_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_pre_3016_, 2);
                                crate::leanh::lean_dec_ref_known(v_fn_3007_, 2);
                                v___y_3010_ = v_a_2899_;
                                state = 14;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_fn_3007_, 2);
                            crate::leanh::lean_dec(v_pre_3016_);
                            v___y_3010_ = v_a_2899_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fn_3007_);
                        v___y_3010_ = v_a_2899_;
                        state = 14;
                        continue;
                    }
                }
                5 => {
                    v_i_3126_ = crate::leanh::lean_ctor_get(v_v_2898_, 0);
                    crate::leanh::lean_inc_ref(v_i_3126_);
                    crate::leanh::lean_dec_ref_known(v_v_2898_, 2);
                    v___x_3127_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_3126_);
                    crate::leanh::lean_dec_ref(v_i_3126_);
                    if v___x_3127_ == 0 {
                        v___x_3128_ = 2;
                        v___y_2953_ = v___x_3128_;
                        state = 8;
                        continue;
                    } else {
                        v___x_3129_ = 1;
                        v___y_2953_ = v___x_3129_;
                        state = 8;
                        continue;
                    }
                }
                4 => {
                    crate::leanh::lean_dec_ref_known(v_v_2898_, 2);
                    v___x_3130_ = lean_st_ref_take(v_a_2899_);
                    v_values_3136_ = crate::leanh::lean_ctor_get(v___x_3130_, 0);
                    crate::leanh::lean_inc_ref(v_values_3136_);
                    v___x_3137_ = 2;
                    v___x_3138_ = crate::leanh::lean_box(0);
                    v___x_3139_ = 0;
                    v___x_3140_ = crate::leanh::lean_box((v___x_3139_) as usize);
                    v_old_3141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3136_, v_z_2897_, v___x_3140_);
                    crate::leanh::lean_dec(v___x_3140_);
                    v___x_3142_ = (crate::leanh::lean_unbox(v_old_3141_) as u8);
                    v_new_3143_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3142_, v___x_3137_);
                    v___x_3144_ = (crate::leanh::lean_unbox(v_old_3141_) as u8);
                    crate::leanh::lean_dec(v_old_3141_);
                    v___x_3145_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3144_, v_new_3143_);
                    if v___x_3145_ == 0 {
                        v_isSharedCheck_3155_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3130_)) as u8;
                        if v_isSharedCheck_3155_ == 0 {
                            v_unused_3156_ = crate::leanh::lean_ctor_get(v___x_3130_, 0);
                            crate::leanh::lean_dec(v_unused_3156_);
                            v___x_3147_ = v___x_3130_;
                            v_isShared_3148_ = v_isSharedCheck_3155_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3130_);
                            v___x_3147_ = crate::leanh::lean_box(0);
                            v_isShared_3148_ = v_isSharedCheck_3155_;
                            state = 25;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_3136_);
                        crate::leanh::lean_dec(v_z_2897_);
                        v_fst_3132_ = v___x_3138_;
                        v_snd_3133_ = v___x_3130_;
                        state = 24;
                        continue;
                    }
                }
                10 => {
                    crate::leanh::lean_dec_ref_known(v_v_2898_, 2);
                    v___x_3157_ = lean_st_ref_take(v_a_2899_);
                    v_values_3163_ = crate::leanh::lean_ctor_get(v___x_3157_, 0);
                    crate::leanh::lean_inc_ref(v_values_3163_);
                    v___x_3164_ = 2;
                    v___x_3165_ = crate::leanh::lean_box(0);
                    v___x_3166_ = 0;
                    v___x_3167_ = crate::leanh::lean_box((v___x_3166_) as usize);
                    v_old_3168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3163_, v_z_2897_, v___x_3167_);
                    crate::leanh::lean_dec(v___x_3167_);
                    v___x_3169_ = (crate::leanh::lean_unbox(v_old_3168_) as u8);
                    v_new_3170_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3169_, v___x_3164_);
                    v___x_3171_ = (crate::leanh::lean_unbox(v_old_3168_) as u8);
                    crate::leanh::lean_dec(v_old_3168_);
                    v___x_3172_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3171_, v_new_3170_);
                    if v___x_3172_ == 0 {
                        v_isSharedCheck_3182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3157_)) as u8;
                        if v_isSharedCheck_3182_ == 0 {
                            v_unused_3183_ = crate::leanh::lean_ctor_get(v___x_3157_, 0);
                            crate::leanh::lean_dec(v_unused_3183_);
                            v___x_3174_ = v___x_3157_;
                            v_isShared_3175_ = v_isSharedCheck_3182_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3157_);
                            v___x_3174_ = crate::leanh::lean_box(0);
                            v_isShared_3175_ = v_isSharedCheck_3182_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_3163_);
                        crate::leanh::lean_dec(v_z_2897_);
                        v_fst_3159_ = v___x_3165_;
                        v_snd_3160_ = v___x_3157_;
                        state = 27;
                        continue;
                    }
                }
                8 => {
                    crate::leanh::lean_dec_ref_known(v_v_2898_, 3);
                    v___x_3184_ = lean_st_ref_take(v_a_2899_);
                    v_values_3190_ = crate::leanh::lean_ctor_get(v___x_3184_, 0);
                    crate::leanh::lean_inc_ref(v_values_3190_);
                    v___x_3191_ = 2;
                    v___x_3192_ = crate::leanh::lean_box(0);
                    v___x_3193_ = 0;
                    v___x_3194_ = crate::leanh::lean_box((v___x_3193_) as usize);
                    v_old_3195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3190_, v_z_2897_, v___x_3194_);
                    crate::leanh::lean_dec(v___x_3194_);
                    v___x_3196_ = (crate::leanh::lean_unbox(v_old_3195_) as u8);
                    v_new_3197_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3196_, v___x_3191_);
                    v___x_3198_ = (crate::leanh::lean_unbox(v_old_3195_) as u8);
                    crate::leanh::lean_dec(v_old_3195_);
                    v___x_3199_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3198_, v_new_3197_);
                    if v___x_3199_ == 0 {
                        v_isSharedCheck_3209_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3184_)) as u8;
                        if v_isSharedCheck_3209_ == 0 {
                            v_unused_3210_ = crate::leanh::lean_ctor_get(v___x_3184_, 0);
                            crate::leanh::lean_dec(v_unused_3210_);
                            v___x_3201_ = v___x_3184_;
                            v_isShared_3202_ = v_isSharedCheck_3209_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3184_);
                            v___x_3201_ = crate::leanh::lean_box(0);
                            v_isShared_3202_ = v_isSharedCheck_3209_;
                            state = 31;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_3190_);
                        crate::leanh::lean_dec(v_z_2897_);
                        v_fst_3186_ = v___x_3192_;
                        v_snd_3187_ = v___x_3184_;
                        state = 30;
                        continue;
                    }
                }
                7 => {
                    crate::leanh::lean_dec_ref_known(v_v_2898_, 2);
                    v___x_3211_ = lean_st_ref_take(v_a_2899_);
                    v_values_3217_ = crate::leanh::lean_ctor_get(v___x_3211_, 0);
                    crate::leanh::lean_inc_ref(v_values_3217_);
                    v___x_3218_ = 2;
                    v___x_3219_ = crate::leanh::lean_box(0);
                    v___x_3220_ = 0;
                    v___x_3221_ = crate::leanh::lean_box((v___x_3220_) as usize);
                    v_old_3222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3217_, v_z_2897_, v___x_3221_);
                    crate::leanh::lean_dec(v___x_3221_);
                    v___x_3223_ = (crate::leanh::lean_unbox(v_old_3222_) as u8);
                    v_new_3224_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3223_, v___x_3218_);
                    v___x_3225_ = (crate::leanh::lean_unbox(v_old_3222_) as u8);
                    crate::leanh::lean_dec(v_old_3222_);
                    v___x_3226_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3225_, v_new_3224_);
                    if v___x_3226_ == 0 {
                        v_isSharedCheck_3236_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3211_)) as u8;
                        if v_isSharedCheck_3236_ == 0 {
                            v_unused_3237_ = crate::leanh::lean_ctor_get(v___x_3211_, 0);
                            crate::leanh::lean_dec(v_unused_3237_);
                            v___x_3228_ = v___x_3211_;
                            v_isShared_3229_ = v_isSharedCheck_3236_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3211_);
                            v___x_3228_ = crate::leanh::lean_box(0);
                            v_isShared_3229_ = v_isSharedCheck_3236_;
                            state = 34;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_3217_);
                        crate::leanh::lean_dec(v_z_2897_);
                        v_fst_3213_ = v___x_3219_;
                        v_snd_3214_ = v___x_3211_;
                        state = 33;
                        continue;
                    }
                }
                1 => {
                    v___x_3238_ = lean_st_ref_take(v_a_2899_);
                    v_values_3244_ = crate::leanh::lean_ctor_get(v___x_3238_, 0);
                    crate::leanh::lean_inc_ref(v_values_3244_);
                    v___x_3245_ = 2;
                    v___x_3246_ = crate::leanh::lean_box(0);
                    v___x_3247_ = 0;
                    v___x_3248_ = crate::leanh::lean_box((v___x_3247_) as usize);
                    v_old_3249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3244_, v_z_2897_, v___x_3248_);
                    crate::leanh::lean_dec(v___x_3248_);
                    v___x_3250_ = (crate::leanh::lean_unbox(v_old_3249_) as u8);
                    v_new_3251_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3250_, v___x_3245_);
                    v___x_3252_ = (crate::leanh::lean_unbox(v_old_3249_) as u8);
                    crate::leanh::lean_dec(v_old_3249_);
                    v___x_3253_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3252_, v_new_3251_);
                    if v___x_3253_ == 0 {
                        v_isSharedCheck_3263_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3238_)) as u8;
                        if v_isSharedCheck_3263_ == 0 {
                            v_unused_3264_ = crate::leanh::lean_ctor_get(v___x_3238_, 0);
                            crate::leanh::lean_dec(v_unused_3264_);
                            v___x_3255_ = v___x_3238_;
                            v_isShared_3256_ = v_isSharedCheck_3263_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3238_);
                            v___x_3255_ = crate::leanh::lean_box(0);
                            v_isShared_3256_ = v_isSharedCheck_3263_;
                            state = 37;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_3244_);
                        crate::leanh::lean_dec(v_z_2897_);
                        v_fst_3240_ = v___x_3246_;
                        v_snd_3241_ = v___x_3238_;
                        state = 36;
                        continue;
                    }
                }
                0 => {
                    v_isSharedCheck_3297_ = (!crate::leanh::lean_is_exclusive(v_v_2898_)) as u8;
                    if v_isSharedCheck_3297_ == 0 {
                        v_unused_3298_ = crate::leanh::lean_ctor_get(v_v_2898_, 0);
                        crate::leanh::lean_dec(v_unused_3298_);
                        v___x_3266_ = v_v_2898_;
                        v_isShared_3267_ = v_isSharedCheck_3297_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_2898_);
                        v___x_3266_ = crate::leanh::lean_box(0);
                        v_isShared_3267_ = v_isSharedCheck_3297_;
                        state = 39;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_v_2898_);
                    crate::leanh::lean_dec(v_z_2897_);
                    v___x_3299_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5);
                    v___x_3300_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(v___x_3299_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
                    return v___x_3300_;
                }
            },
            1 => {
                v___x_2909_ = lean_st_ref_set(v___y_2906_, v_snd_2908_);
                v___x_2910_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2910_, 0, v_fst_2907_);
                return v___x_2910_;
            }
            2 => {
                v___x_2914_ = lean_st_ref_take(v___y_2912_);
                v_values_2915_ = crate::leanh::lean_ctor_get(v___x_2914_, 0);
                crate::leanh::lean_inc_ref(v_values_2915_);
                v___x_2916_ = crate::leanh::lean_box(0);
                v___x_2917_ = 0;
                v___x_2918_ = crate::leanh::lean_box((v___x_2917_) as usize);
                v_old_2919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_2915_, v_z_2897_, v___x_2918_);
                crate::leanh::lean_dec(v___x_2918_);
                v___x_2920_ = (crate::leanh::lean_unbox(v_old_2919_) as u8);
                v_new_2921_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2920_, v___y_2913_);
                v___x_2922_ = (crate::leanh::lean_unbox(v_old_2919_) as u8);
                crate::leanh::lean_dec(v_old_2919_);
                v___x_2923_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2922_, v_new_2921_);
                if v___x_2923_ == 0 {
                    v_isSharedCheck_2933_ = (!crate::leanh::lean_is_exclusive(v___x_2914_)) as u8;
                    if v_isSharedCheck_2933_ == 0 {
                        v_unused_2934_ = crate::leanh::lean_ctor_get(v___x_2914_, 0);
                        crate::leanh::lean_dec(v_unused_2934_);
                        v___x_2925_ = v___x_2914_;
                        v_isShared_2926_ = v_isSharedCheck_2933_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2914_);
                        v___x_2925_ = crate::leanh::lean_box(0);
                        v_isShared_2926_ = v_isSharedCheck_2933_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_values_2915_);
                    crate::leanh::lean_dec(v_z_2897_);
                    v___y_2906_ = v___y_2912_;
                    v_fst_2907_ = v___x_2916_;
                    v_snd_2908_ = v___x_2914_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2927_ = 1;
                v___x_2928_ = crate::leanh::lean_box((v_new_2921_) as usize);
                v___x_2929_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_2915_, v_z_2897_, v___x_2928_);
                if v_isShared_2926_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2925_, 0, v___x_2929_);
                    v___x_2931_ = v___x_2925_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2929_);
                    v___x_2931_ = v_reuseFailAlloc_2932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2931_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2927_,
                );
                v___y_2906_ = v___y_2912_;
                v_fst_2907_ = v___x_2916_;
                v_snd_2908_ = v___x_2931_;
                state = 1;
                continue;
            }
            5 => {
                v___x_2939_ = lean_st_ref_set(v___y_2936_, v_snd_2938_);
                v___x_2940_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2940_, 0, v_fst_2937_);
                return v___x_2940_;
            }
            6 => {
                v___x_2945_ = lean_st_ref_set(v___y_2942_, v_snd_2944_);
                v___x_2946_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2946_, 0, v_fst_2943_);
                return v___x_2946_;
            }
            7 => {
                v___x_2950_ = lean_st_ref_set(v_a_2899_, v_snd_2949_);
                v___x_2951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2951_, 0, v_fst_2948_);
                return v___x_2951_;
            }
            8 => {
                v___x_2954_ = lean_st_ref_take(v_a_2899_);
                v_values_2955_ = crate::leanh::lean_ctor_get(v___x_2954_, 0);
                crate::leanh::lean_inc_ref(v_values_2955_);
                v___x_2956_ = crate::leanh::lean_box(0);
                v___x_2957_ = 0;
                v___x_2958_ = crate::leanh::lean_box((v___x_2957_) as usize);
                v_old_2959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_2955_, v_z_2897_, v___x_2958_);
                crate::leanh::lean_dec(v___x_2958_);
                v___x_2960_ = (crate::leanh::lean_unbox(v_old_2959_) as u8);
                v_new_2961_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2960_, v___y_2953_);
                v___x_2962_ = (crate::leanh::lean_unbox(v_old_2959_) as u8);
                crate::leanh::lean_dec(v_old_2959_);
                v___x_2963_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2962_, v_new_2961_);
                if v___x_2963_ == 0 {
                    v_isSharedCheck_2973_ = (!crate::leanh::lean_is_exclusive(v___x_2954_)) as u8;
                    if v_isSharedCheck_2973_ == 0 {
                        v_unused_2974_ = crate::leanh::lean_ctor_get(v___x_2954_, 0);
                        crate::leanh::lean_dec(v_unused_2974_);
                        v___x_2965_ = v___x_2954_;
                        v_isShared_2966_ = v_isSharedCheck_2973_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2954_);
                        v___x_2965_ = crate::leanh::lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2973_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_values_2955_);
                    crate::leanh::lean_dec(v_z_2897_);
                    v_fst_2948_ = v___x_2956_;
                    v_snd_2949_ = v___x_2954_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_2967_ = 1;
                v___x_2968_ = crate::leanh::lean_box((v_new_2961_) as usize);
                v___x_2969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_2955_, v_z_2897_, v___x_2968_);
                if v_isShared_2966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2965_, 0, v___x_2969_);
                    v___x_2971_ = v___x_2965_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2972_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2969_);
                    v___x_2971_ = v_reuseFailAlloc_2972_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2971_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2967_,
                );
                v_fst_2948_ = v___x_2956_;
                v_snd_2949_ = v___x_2971_;
                state = 7;
                continue;
            }
            11 => {
                v___x_2981_ = lean_st_ref_set(v_a_2899_, v_snd_2980_);
                v___x_2982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2982_, 0, v_fst_2979_);
                return v___x_2982_;
            }
            12 => {
                v___x_2999_ = 1;
                v___x_3000_ = crate::leanh::lean_box((v_new_2993_) as usize);
                v___x_3001_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_2984_, v_z_2897_, v___x_3000_);
                if v_isShared_2998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2997_, 0, v___x_3001_);
                    v___x_3003_ = v___x_2997_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
                    v___x_3003_ = v_reuseFailAlloc_3004_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3003_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2999_,
                );
                v_fst_2979_ = v___x_2988_;
                v_snd_2980_ = v___x_3003_;
                state = 11;
                continue;
            }
            14 => {
                v___x_3011_ = lean_array_get_size(v_args_3008_);
                crate::leanh::lean_dec_ref(v_args_3008_);
                v___x_3012_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3013_ = lean_nat_dec_eq(v___x_3011_, v___x_3012_);
                if v___x_3013_ == 0 {
                    v___x_3014_ = 2;
                    v___y_2912_ = v___y_3010_;
                    v___y_2913_ = v___x_3014_;
                    state = 2;
                    continue;
                } else {
                    v___x_3015_ = 1;
                    v___y_2912_ = v___y_3010_;
                    v___y_2913_ = v___x_3015_;
                    state = 2;
                    continue;
                }
            }
            15 => {
                v___x_3025_ = crate::leanh::lean_box(0);
                v___x_3026_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3027_ = lean_array_get(v___x_3025_, v_args_3023_, v___x_3026_);
                crate::leanh::lean_dec_ref(v_args_3023_);
                if crate::leanh::lean_obj_tag(v___x_3027_) == 1 {
                    v_fvarId_3028_ = crate::leanh::lean_ctor_get(v___x_3027_, 0);
                    crate::leanh::lean_inc(v_fvarId_3028_);
                    crate::leanh::lean_dec_ref_known(v___x_3027_, 1);
                    v___x_3029_ = lean_st_ref_get(v___y_3024_);
                    v___x_3030_ = lean_st_ref_take(v___y_3024_);
                    v_values_3031_ = crate::leanh::lean_ctor_get(v___x_3029_, 0);
                    crate::leanh::lean_inc_ref(v_values_3031_);
                    crate::leanh::lean_dec(v___x_3029_);
                    v_values_3032_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                    crate::leanh::lean_inc_ref(v_values_3032_);
                    v___x_3033_ = 0;
                    v___x_3034_ = crate::leanh::lean_box((v___x_3033_) as usize);
                    v___x_3035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3031_, v_fvarId_3028_, v___x_3034_);
                    crate::leanh::lean_dec(v___x_3034_);
                    crate::leanh::lean_dec(v_fvarId_3028_);
                    crate::leanh::lean_dec_ref(v_values_3031_);
                    v___x_3036_ = crate::leanh::lean_box(0);
                    v___x_3037_ = crate::leanh::lean_box((v___x_3033_) as usize);
                    v_old_3038_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3032_, v_z_2897_, v___x_3037_);
                    crate::leanh::lean_dec(v___x_3037_);
                    v___x_3039_ = (crate::leanh::lean_unbox(v_old_3038_) as u8);
                    v___x_3040_ = (crate::leanh::lean_unbox(v___x_3035_) as u8);
                    crate::leanh::lean_dec(v___x_3035_);
                    v_new_3041_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3039_, v___x_3040_);
                    v___x_3042_ = (crate::leanh::lean_unbox(v_old_3038_) as u8);
                    crate::leanh::lean_dec(v_old_3038_);
                    v___x_3043_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3042_, v_new_3041_);
                    if v___x_3043_ == 0 {
                        v_isSharedCheck_3052_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3030_)) as u8;
                        if v_isSharedCheck_3052_ == 0 {
                            v_unused_3053_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                            crate::leanh::lean_dec(v_unused_3053_);
                            v___x_3045_ = v___x_3030_;
                            v_isShared_3046_ = v_isSharedCheck_3052_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3030_);
                            v___x_3045_ = crate::leanh::lean_box(0);
                            v_isShared_3046_ = v_isSharedCheck_3052_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_3032_);
                        crate::leanh::lean_dec(v_z_2897_);
                        v___y_2936_ = v___y_3024_;
                        v_fst_2937_ = v___x_3036_;
                        v_snd_2938_ = v___x_3030_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3027_);
                    crate::leanh::lean_dec(v_z_2897_);
                    v___x_3054_ = crate::leanh::lean_box(0);
                    v___x_3055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3055_, 0, v___x_3054_);
                    return v___x_3055_;
                }
            }
            16 => {
                v___x_3047_ = crate::leanh::lean_box((v_new_3041_) as usize);
                v___x_3048_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3032_, v_z_2897_, v___x_3047_);
                if v_isShared_3046_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3045_, 0, v___x_3048_);
                    v___x_3050_ = v___x_3045_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3051_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
                    v___x_3050_ = v_reuseFailAlloc_3051_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3050_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3021_,
                );
                v___y_2936_ = v___y_3024_;
                v_fst_2937_ = v___x_3036_;
                v_snd_2938_ = v___x_3050_;
                state = 5;
                continue;
            }
            18 => {
                v___x_3062_ = crate::leanh::lean_box(0);
                v___x_3063_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3064_ = lean_array_get(v___x_3062_, v_args_3008_, v___x_3063_);
                crate::leanh::lean_dec_ref(v_args_3008_);
                if crate::leanh::lean_obj_tag(v___x_3064_) == 1 {
                    v_fvarId_3065_ = crate::leanh::lean_ctor_get(v___x_3064_, 0);
                    crate::leanh::lean_inc(v_fvarId_3065_);
                    crate::leanh::lean_dec_ref_known(v___x_3064_, 1);
                    v___x_3066_ = lean_st_ref_get(v___y_3061_);
                    v___x_3067_ = lean_st_ref_take(v___y_3061_);
                    v_values_3068_ = crate::leanh::lean_ctor_get(v___x_3066_, 0);
                    crate::leanh::lean_inc_ref(v_values_3068_);
                    crate::leanh::lean_dec(v___x_3066_);
                    v_values_3069_ = crate::leanh::lean_ctor_get(v___x_3067_, 0);
                    crate::leanh::lean_inc_ref(v_values_3069_);
                    v___x_3070_ = 0;
                    v___x_3071_ = crate::leanh::lean_box((v___x_3070_) as usize);
                    v___x_3072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3068_, v_fvarId_3065_, v___x_3071_);
                    crate::leanh::lean_dec(v___x_3071_);
                    crate::leanh::lean_dec(v_fvarId_3065_);
                    crate::leanh::lean_dec_ref(v_values_3068_);
                    v___x_3073_ = crate::leanh::lean_box(0);
                    v___x_3074_ = crate::leanh::lean_box((v___x_3070_) as usize);
                    v_old_3075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3069_, v_z_2897_, v___x_3074_);
                    crate::leanh::lean_dec(v___x_3074_);
                    v___x_3076_ = (crate::leanh::lean_unbox(v_old_3075_) as u8);
                    v___x_3077_ = (crate::leanh::lean_unbox(v___x_3072_) as u8);
                    crate::leanh::lean_dec(v___x_3072_);
                    v_new_3078_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3076_, v___x_3077_);
                    v___x_3079_ = (crate::leanh::lean_unbox(v_old_3075_) as u8);
                    crate::leanh::lean_dec(v_old_3075_);
                    v___x_3080_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3079_, v_new_3078_);
                    if v___x_3080_ == 0 {
                        v_isSharedCheck_3089_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3067_)) as u8;
                        if v_isSharedCheck_3089_ == 0 {
                            v_unused_3090_ = crate::leanh::lean_ctor_get(v___x_3067_, 0);
                            crate::leanh::lean_dec(v_unused_3090_);
                            v___x_3082_ = v___x_3067_;
                            v_isShared_3083_ = v_isSharedCheck_3089_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3067_);
                            v___x_3082_ = crate::leanh::lean_box(0);
                            v_isShared_3083_ = v_isSharedCheck_3089_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_3069_);
                        crate::leanh::lean_dec(v_z_2897_);
                        v___y_2942_ = v___y_3061_;
                        v_fst_2943_ = v___x_3073_;
                        v_snd_2944_ = v___x_3067_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3064_);
                    crate::leanh::lean_dec(v_z_2897_);
                    v___x_3091_ = crate::leanh::lean_box(0);
                    v___x_3092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3092_, 0, v___x_3091_);
                    return v___x_3092_;
                }
            }
            19 => {
                v___x_3084_ = crate::leanh::lean_box((v_new_3078_) as usize);
                v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3069_, v_z_2897_, v___x_3084_);
                if v_isShared_3083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3082_, 0, v___x_3085_);
                    v___x_3087_ = v___x_3082_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
                    v___x_3087_ = v_reuseFailAlloc_3088_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3087_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3059_,
                );
                v___y_2942_ = v___y_3061_;
                v_fst_2943_ = v___x_3073_;
                v_snd_2944_ = v___x_3087_;
                state = 6;
                continue;
            }
            21 => {
                v___x_3103_ = lean_st_ref_set(v_a_2899_, v_snd_3102_);
                v___y_3061_ = v_a_2899_;
                state = 18;
                continue;
            }
            22 => {
                v___x_3119_ = crate::leanh::lean_box((v_new_3113_) as usize);
                crate::leanh::lean_inc(v_z_2897_);
                v___x_3120_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3105_, v_z_2897_, v___x_3119_);
                if v_isShared_3118_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3117_, 0, v___x_3120_);
                    v___x_3122_ = v___x_3117_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3122_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3059_,
                );
                v_snd_3102_ = v___x_3122_;
                state = 21;
                continue;
            }
            24 => {
                v___x_3134_ = lean_st_ref_set(v_a_2899_, v_snd_3133_);
                v___x_3135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3135_, 0, v_fst_3132_);
                return v___x_3135_;
            }
            25 => {
                v___x_3149_ = 1;
                v___x_3150_ = crate::leanh::lean_box((v_new_3143_) as usize);
                v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3136_, v_z_2897_, v___x_3150_);
                if v_isShared_3148_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3147_, 0, v___x_3151_);
                    v___x_3153_ = v___x_3147_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
                    v___x_3153_ = v_reuseFailAlloc_3154_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3153_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3149_,
                );
                v_fst_3132_ = v___x_3138_;
                v_snd_3133_ = v___x_3153_;
                state = 24;
                continue;
            }
            27 => {
                v___x_3161_ = lean_st_ref_set(v_a_2899_, v_snd_3160_);
                v___x_3162_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3162_, 0, v_fst_3159_);
                return v___x_3162_;
            }
            28 => {
                v___x_3176_ = 1;
                v___x_3177_ = crate::leanh::lean_box((v_new_3170_) as usize);
                v___x_3178_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3163_, v_z_2897_, v___x_3177_);
                if v_isShared_3175_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3174_, 0, v___x_3178_);
                    v___x_3180_ = v___x_3174_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3181_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
                    v___x_3180_ = v_reuseFailAlloc_3181_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3180_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3176_,
                );
                v_fst_3159_ = v___x_3165_;
                v_snd_3160_ = v___x_3180_;
                state = 27;
                continue;
            }
            30 => {
                v___x_3188_ = lean_st_ref_set(v_a_2899_, v_snd_3187_);
                v___x_3189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3189_, 0, v_fst_3186_);
                return v___x_3189_;
            }
            31 => {
                v___x_3203_ = 1;
                v___x_3204_ = crate::leanh::lean_box((v_new_3197_) as usize);
                v___x_3205_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3190_, v_z_2897_, v___x_3204_);
                if v_isShared_3202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3201_, 0, v___x_3205_);
                    v___x_3207_ = v___x_3201_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
                    v___x_3207_ = v_reuseFailAlloc_3208_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3203_,
                );
                v_fst_3186_ = v___x_3192_;
                v_snd_3187_ = v___x_3207_;
                state = 30;
                continue;
            }
            33 => {
                v___x_3215_ = lean_st_ref_set(v_a_2899_, v_snd_3214_);
                v___x_3216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3216_, 0, v_fst_3213_);
                return v___x_3216_;
            }
            34 => {
                v___x_3230_ = 1;
                v___x_3231_ = crate::leanh::lean_box((v_new_3224_) as usize);
                v___x_3232_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3217_, v_z_2897_, v___x_3231_);
                if v_isShared_3229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3228_, 0, v___x_3232_);
                    v___x_3234_ = v___x_3228_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3235_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
                    v___x_3234_ = v_reuseFailAlloc_3235_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3234_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3230_,
                );
                v_fst_3213_ = v___x_3219_;
                v_snd_3214_ = v___x_3234_;
                state = 33;
                continue;
            }
            36 => {
                v___x_3242_ = lean_st_ref_set(v_a_2899_, v_snd_3241_);
                v___x_3243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3243_, 0, v_fst_3240_);
                return v___x_3243_;
            }
            37 => {
                v___x_3257_ = 1;
                v___x_3258_ = crate::leanh::lean_box((v_new_3251_) as usize);
                v___x_3259_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3244_, v_z_2897_, v___x_3258_);
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3259_);
                    v___x_3261_ = v___x_3255_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3261_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3257_,
                );
                v_fst_3240_ = v___x_3246_;
                v_snd_3241_ = v___x_3261_;
                state = 36;
                continue;
            }
            39 => {
                v___x_3268_ = lean_st_ref_take(v_a_2899_);
                v_values_3276_ = crate::leanh::lean_ctor_get(v___x_3268_, 0);
                crate::leanh::lean_inc_ref(v_values_3276_);
                v___x_3277_ = 2;
                v___x_3278_ = crate::leanh::lean_box(0);
                v___x_3279_ = 0;
                v___x_3280_ = crate::leanh::lean_box((v___x_3279_) as usize);
                v_old_3281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3276_, v_z_2897_, v___x_3280_);
                crate::leanh::lean_dec(v___x_3280_);
                v___x_3282_ = (crate::leanh::lean_unbox(v_old_3281_) as u8);
                v_new_3283_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3282_, v___x_3277_);
                v___x_3284_ = (crate::leanh::lean_unbox(v_old_3281_) as u8);
                crate::leanh::lean_dec(v_old_3281_);
                v___x_3285_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3284_, v_new_3283_);
                if v___x_3285_ == 0 {
                    v_isSharedCheck_3295_ = (!crate::leanh::lean_is_exclusive(v___x_3268_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v_unused_3296_ = crate::leanh::lean_ctor_get(v___x_3268_, 0);
                        crate::leanh::lean_dec(v_unused_3296_);
                        v___x_3287_ = v___x_3268_;
                        v_isShared_3288_ = v_isSharedCheck_3295_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3268_);
                        v___x_3287_ = crate::leanh::lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3295_;
                        state = 42;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_values_3276_);
                    crate::leanh::lean_dec(v_z_2897_);
                    v_fst_3270_ = v___x_3278_;
                    v_snd_3271_ = v___x_3268_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v___x_3272_ = lean_st_ref_set(v_a_2899_, v_snd_3271_);
                if v_isShared_3267_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3266_, 0, v_fst_3270_);
                    v___x_3274_ = v___x_3266_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3275_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_fst_3270_);
                    v___x_3274_ = v_reuseFailAlloc_3275_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3274_;
            }
            42 => {
                v___x_3289_ = 1;
                v___x_3290_ = crate::leanh::lean_box((v_new_3283_) as usize);
                v___x_3291_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3276_, v_z_2897_, v___x_3290_);
                if v_isShared_3288_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3287_, 0, v___x_3291_);
                    v___x_3293_ = v___x_3287_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3294_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
                    v___x_3293_ = v_reuseFailAlloc_3294_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3293_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3289_,
                );
                v_fst_3270_ = v___x_3278_;
                v_snd_3271_ = v___x_3293_;
                state = 40;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___boxed(
    mut v_z_3301_: *mut crate::leanh::LeanObject,
    mut v_v_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3309_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue(v_z_3301_, v_v_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
    crate::leanh::lean_dec(v_a_3307_);
    crate::leanh::lean_dec_ref(v_a_3306_);
    crate::leanh::lean_dec(v_a_3305_);
    crate::leanh::lean_dec_ref(v_a_3304_);
    crate::leanh::lean_dec(v_a_3303_);
    return v_res_3309_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0(
    mut v_00_u03b2_3310_: *mut crate::leanh::LeanObject,
    mut v_m_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_fallback_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_m_3311_, v_a_3312_, v_fallback_3313_);
    return v___x_3314_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___boxed(
    mut v_00_u03b2_3315_: *mut crate::leanh::LeanObject,
    mut v_m_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
    mut v_fallback_3318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0(v_00_u03b2_3315_, v_m_3316_, v_a_3317_, v_fallback_3318_);
    crate::leanh::lean_dec(v_fallback_3318_);
    crate::leanh::lean_dec(v_a_3317_);
    crate::leanh::lean_dec_ref(v_m_3316_);
    return v_res_3319_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1(
    mut v_00_u03b2_3320_: *mut crate::leanh::LeanObject,
    mut v_m_3321_: *mut crate::leanh::LeanObject,
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_b_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_m_3321_, v_a_3322_, v_b_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0(
    mut v_00_u03b2_3325_: *mut crate::leanh::LeanObject,
    mut v_a_3326_: *mut crate::leanh::LeanObject,
    mut v_fallback_3327_: *mut crate::leanh::LeanObject,
    mut v_x_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3329_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___redArg(v_a_3326_, v_fallback_3327_, v_x_3328_);
    return v___x_3329_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___boxed(
    mut v_00_u03b2_3330_: *mut crate::leanh::LeanObject,
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_fallback_3332_: *mut crate::leanh::LeanObject,
    mut v_x_3333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0(v_00_u03b2_3330_, v_a_3331_, v_fallback_3332_, v_x_3333_);
    crate::leanh::lean_dec(v_x_3333_);
    crate::leanh::lean_dec(v_fallback_3332_);
    crate::leanh::lean_dec(v_a_3331_);
    return v_res_3334_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2(
    mut v_00_u03b2_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_x_3337_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3338_: u8 = 0;
    v___x_3338_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg(v_a_3336_, v_x_3337_);
    return v___x_3338_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___boxed(
    mut v_00_u03b2_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_x_3341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3342_: u8 = 0;
    let mut v_r_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3342_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2(v_00_u03b2_3339_, v_a_3340_, v_x_3341_);
    crate::leanh::lean_dec(v_x_3341_);
    crate::leanh::lean_dec(v_a_3340_);
    v_r_3343_ = crate::leanh::lean_box((v_res_3342_) as usize);
    return v_r_3343_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3(
    mut v_00_u03b2_3344_: *mut crate::leanh::LeanObject,
    mut v_data_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3346_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3___redArg(v_data_3345_);
    return v___x_3346_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4(
    mut v_00_u03b2_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_b_3349_: *mut crate::leanh::LeanObject,
    mut v_x_3350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4___redArg(v_a_3348_, v_b_3349_, v_x_3350_);
    return v___x_3351_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5(
    mut v_00_u03b2_3352_: *mut crate::leanh::LeanObject,
    mut v_i_3353_: *mut crate::leanh::LeanObject,
    mut v_source_3354_: *mut crate::leanh::LeanObject,
    mut v_target_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5___redArg(v_i_3353_, v_source_3354_, v_target_3355_);
    return v___x_3356_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5_spec__6(
    mut v_00_u03b2_3357_: *mut crate::leanh::LeanObject,
    mut v_x_3358_: *mut crate::leanh::LeanObject,
    mut v_x_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5_spec__6___redArg(v_x_3358_, v_x_3359_);
    return v___x_3360_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg(
    mut v_alt_3361_: *mut crate::leanh::LeanObject,
    mut v_f_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_alt_3361_) {
        0 => {
            let mut v_code_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_3369_ = crate::leanh::lean_ctor_get(v_alt_3361_, 2);
            crate::leanh::lean_inc_ref(v_code_3369_);
            crate::leanh::lean_dec_ref_known(v_alt_3361_, 3);
            crate::leanh::lean_inc(v___y_3367_);
            crate::leanh::lean_inc_ref(v___y_3366_);
            crate::leanh::lean_inc(v___y_3365_);
            crate::leanh::lean_inc_ref(v___y_3364_);
            crate::leanh::lean_inc(v___y_3363_);
            v___x_3370_ = crate::leanh::lean_apply_7(
                v_f_3362_,
                v_code_3369_,
                v___y_3363_,
                v___y_3364_,
                v___y_3365_,
                v___y_3366_,
                v___y_3367_,
                crate::leanh::lean_box(0),
            );
            return v___x_3370_;
        }
        1 => {
            let mut v_code_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_3371_ = crate::leanh::lean_ctor_get(v_alt_3361_, 1);
            crate::leanh::lean_inc_ref(v_code_3371_);
            crate::leanh::lean_dec_ref_known(v_alt_3361_, 2);
            crate::leanh::lean_inc(v___y_3367_);
            crate::leanh::lean_inc_ref(v___y_3366_);
            crate::leanh::lean_inc(v___y_3365_);
            crate::leanh::lean_inc_ref(v___y_3364_);
            crate::leanh::lean_inc(v___y_3363_);
            v___x_3372_ = crate::leanh::lean_apply_7(
                v_f_3362_,
                v_code_3371_,
                v___y_3363_,
                v___y_3364_,
                v___y_3365_,
                v___y_3366_,
                v___y_3367_,
                crate::leanh::lean_box(0),
            );
            return v___x_3372_;
        }
        _ => {
            let mut v_code_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_3373_ = crate::leanh::lean_ctor_get(v_alt_3361_, 0);
            crate::leanh::lean_inc_ref(v_code_3373_);
            crate::leanh::lean_dec_ref_known(v_alt_3361_, 1);
            crate::leanh::lean_inc(v___y_3367_);
            crate::leanh::lean_inc_ref(v___y_3366_);
            crate::leanh::lean_inc(v___y_3365_);
            crate::leanh::lean_inc_ref(v___y_3364_);
            crate::leanh::lean_inc(v___y_3363_);
            v___x_3374_ = crate::leanh::lean_apply_7(
                v_f_3362_,
                v_code_3373_,
                v___y_3363_,
                v___y_3364_,
                v___y_3365_,
                v___y_3366_,
                v___y_3367_,
                crate::leanh::lean_box(0),
            );
            return v___x_3374_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg___boxed(
    mut v_alt_3375_: *mut crate::leanh::LeanObject,
    mut v_f_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
    mut v___y_3378_: *mut crate::leanh::LeanObject,
    mut v___y_3379_: *mut crate::leanh::LeanObject,
    mut v___y_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3383_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg(v_alt_3375_, v_f_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
    crate::leanh::lean_dec(v___y_3381_);
    crate::leanh::lean_dec_ref(v___y_3380_);
    crate::leanh::lean_dec(v___y_3379_);
    crate::leanh::lean_dec_ref(v___y_3378_);
    crate::leanh::lean_dec(v___y_3377_);
    return v_res_3383_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0(
    mut v_pu_3384_: u8,
    mut v_alt_3385_: *mut crate::leanh::LeanObject,
    mut v_f_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg(v_alt_3385_, v_f_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    return v___x_3393_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___boxed(
    mut v_pu_3394_: *mut crate::leanh::LeanObject,
    mut v_alt_3395_: *mut crate::leanh::LeanObject,
    mut v_f_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3403_: u8 = 0;
    let mut v_res_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3403_ = (crate::leanh::lean_unbox(v_pu_3394_) as u8);
    v_res_3404_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0(v_pu_boxed_3403_, v_alt_3395_, v_f_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
    crate::leanh::lean_dec(v___y_3401_);
    crate::leanh::lean_dec_ref(v___y_3400_);
    crate::leanh::lean_dec(v___y_3399_);
    crate::leanh::lean_dec_ref(v___y_3398_);
    crate::leanh::lean_dec(v___y_3397_);
    return v_res_3404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg(
    mut v_as_3405_: *mut crate::leanh::LeanObject,
    mut v_sz_3406_: usize,
    mut v_i_3407_: usize,
    mut v_b_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: usize = 0;
    let mut v___x_3414_: usize = 0;
    let mut v___x_3416_: u8 = 0;
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: u8 = 0;
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v_a_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: u8 = 0;
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: u8 = 0;
    let mut v_new_3448_: u8 = 0;
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: u8 = 0;
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut v_unused_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_unused_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3416_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
                if v___x_3416_ == 0 {
                    v___x_3417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3417_, 0, v_b_3408_);
                    return v___x_3417_;
                } else {
                    v_array_3418_ = crate::leanh::lean_ctor_get(v_b_3408_, 0);
                    v_start_3419_ = crate::leanh::lean_ctor_get(v_b_3408_, 1);
                    v_stop_3420_ = crate::leanh::lean_ctor_get(v_b_3408_, 2);
                    v___x_3421_ = lean_nat_dec_lt(v_start_3419_, v_stop_3420_);
                    if v___x_3421_ == 0 {
                        v___x_3422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3422_, 0, v_b_3408_);
                        return v___x_3422_;
                    } else {
                        crate::leanh::lean_inc(v_stop_3420_);
                        crate::leanh::lean_inc(v_start_3419_);
                        crate::leanh::lean_inc_ref(v_array_3418_);
                        v_isSharedCheck_3462_ = (!crate::leanh::lean_is_exclusive(v_b_3408_)) as u8;
                        if v_isSharedCheck_3462_ == 0 {
                            v_unused_3463_ = crate::leanh::lean_ctor_get(v_b_3408_, 2);
                            crate::leanh::lean_dec(v_unused_3463_);
                            v_unused_3464_ = crate::leanh::lean_ctor_get(v_b_3408_, 1);
                            crate::leanh::lean_dec(v_unused_3464_);
                            v_unused_3465_ = crate::leanh::lean_ctor_get(v_b_3408_, 0);
                            crate::leanh::lean_dec(v_unused_3465_);
                            v___x_3424_ = v_b_3408_;
                            v_isShared_3425_ = v_isSharedCheck_3462_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_3408_);
                            v___x_3424_ = crate::leanh::lean_box(0);
                            v_isShared_3425_ = v_isSharedCheck_3462_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3413_ = 1usize;
                v___x_3414_ = lean_usize_add(v_i_3407_, v___x_3413_);
                v_i_3407_ = v___x_3414_;
                v_b_3408_ = v_a_3412_;
                state = 0;
                continue;
            }
            2 => {
                v_a_3426_ = lean_array_uget_borrowed(v_as_3405_, v_i_3407_);
                v___x_3427_ = lean_array_fget(v_array_3418_, v_start_3419_);
                v___x_3428_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3429_ = lean_nat_add(v_start_3419_, v___x_3428_);
                crate::leanh::lean_dec(v_start_3419_);
                if v_isShared_3425_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3424_, 1, v___x_3429_);
                    v___x_3431_ = v___x_3424_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_array_3418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_stop_3420_);
                    v___x_3431_ = v_reuseFailAlloc_3461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_3426_) == 1 {
                    v_fvarId_3432_ = crate::leanh::lean_ctor_get(v_a_3426_, 0);
                    v___x_3433_ = lean_st_ref_get(v___y_3409_);
                    v___x_3434_ = lean_st_ref_take(v___y_3409_);
                    v_values_3438_ = crate::leanh::lean_ctor_get(v___x_3433_, 0);
                    crate::leanh::lean_inc_ref(v_values_3438_);
                    crate::leanh::lean_dec(v___x_3433_);
                    v_fvarId_3439_ = crate::leanh::lean_ctor_get(v___x_3427_, 0);
                    crate::leanh::lean_inc(v_fvarId_3439_);
                    crate::leanh::lean_dec(v___x_3427_);
                    v_values_3440_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                    crate::leanh::lean_inc_ref(v_values_3440_);
                    v___x_3441_ = 0;
                    v___x_3442_ = crate::leanh::lean_box((v___x_3441_) as usize);
                    v___x_3443_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3438_, v_fvarId_3432_, v___x_3442_);
                    crate::leanh::lean_dec(v___x_3442_);
                    crate::leanh::lean_dec_ref(v_values_3438_);
                    v___x_3444_ = crate::leanh::lean_box((v___x_3441_) as usize);
                    v_old_3445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3440_, v_fvarId_3439_, v___x_3444_);
                    crate::leanh::lean_dec(v___x_3444_);
                    v___x_3446_ = (crate::leanh::lean_unbox(v_old_3445_) as u8);
                    v___x_3447_ = (crate::leanh::lean_unbox(v___x_3443_) as u8);
                    crate::leanh::lean_dec(v___x_3443_);
                    v_new_3448_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3446_, v___x_3447_);
                    v___x_3449_ = (crate::leanh::lean_unbox(v_old_3445_) as u8);
                    crate::leanh::lean_dec(v_old_3445_);
                    v___x_3450_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3449_, v_new_3448_);
                    if v___x_3450_ == 0 {
                        v_isSharedCheck_3459_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3434_)) as u8;
                        if v_isSharedCheck_3459_ == 0 {
                            v_unused_3460_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                            crate::leanh::lean_dec(v_unused_3460_);
                            v___x_3452_ = v___x_3434_;
                            v_isShared_3453_ = v_isSharedCheck_3459_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3434_);
                            v___x_3452_ = crate::leanh::lean_box(0);
                            v_isShared_3453_ = v_isSharedCheck_3459_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_values_3440_);
                        crate::leanh::lean_dec(v_fvarId_3439_);
                        v_snd_3436_ = v___x_3434_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3427_);
                    v_a_3412_ = v___x_3431_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_3437_ = lean_st_ref_set(v___y_3409_, v_snd_3436_);
                v_a_3412_ = v___x_3431_;
                state = 1;
                continue;
            }
            5 => {
                v___x_3454_ = crate::leanh::lean_box((v_new_3448_) as usize);
                v___x_3455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3440_, v_fvarId_3439_, v___x_3454_);
                if v_isShared_3453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3452_, 0, v___x_3455_);
                    v___x_3457_ = v___x_3452_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
                    v___x_3457_ = v_reuseFailAlloc_3458_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3421_,
                );
                v_snd_3436_ = v___x_3457_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg___boxed(
    mut v_as_3466_: *mut crate::leanh::LeanObject,
    mut v_sz_3467_: *mut crate::leanh::LeanObject,
    mut v_i_3468_: *mut crate::leanh::LeanObject,
    mut v_b_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3472_: usize = 0;
    let mut v_i_boxed_3473_: usize = 0;
    let mut v_res_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3472_ = crate::leanh::lean_unbox_usize(v_sz_3467_);
    crate::leanh::lean_dec(v_sz_3467_);
    v_i_boxed_3473_ = crate::leanh::lean_unbox_usize(v_i_3468_);
    crate::leanh::lean_dec(v_i_3468_);
    v_res_3474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg(v_as_3466_, v_sz_boxed_3472_, v_i_boxed_3473_, v_b_3469_, v___y_3470_);
    crate::leanh::lean_dec(v___y_3470_);
    crate::leanh::lean_dec_ref(v_as_3466_);
    return v_res_3474_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg(
    mut v_m_3475_: *mut crate::leanh::LeanObject,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: u64 = 0;
    let mut v___x_3480_: u64 = 0;
    let mut v___x_3481_: u64 = 0;
    let mut v_fold_3482_: u64 = 0;
    let mut v___x_3483_: u64 = 0;
    let mut v___x_3484_: u64 = 0;
    let mut v___x_3485_: u64 = 0;
    let mut v___x_3486_: usize = 0;
    let mut v___x_3487_: usize = 0;
    let mut v___x_3488_: usize = 0;
    let mut v___x_3489_: usize = 0;
    let mut v___x_3490_: usize = 0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: u8 = 0;
    v_buckets_3477_ = crate::leanh::lean_ctor_get(v_m_3475_, 1);
    v___x_3478_ = lean_array_get_size(v_buckets_3477_);
    v___x_3479_ = l_Lean_instHashableFVarId_hash(v_a_3476_);
    v___x_3480_ = 32u64;
    v___x_3481_ = lean_uint64_shift_right(v___x_3479_, v___x_3480_);
    v_fold_3482_ = lean_uint64_xor(v___x_3479_, v___x_3481_);
    v___x_3483_ = 16u64;
    v___x_3484_ = lean_uint64_shift_right(v_fold_3482_, v___x_3483_);
    v___x_3485_ = lean_uint64_xor(v_fold_3482_, v___x_3484_);
    v___x_3486_ = lean_uint64_to_usize(v___x_3485_);
    v___x_3487_ = lean_usize_of_nat(v___x_3478_);
    v___x_3488_ = 1usize;
    v___x_3489_ = lean_usize_sub(v___x_3487_, v___x_3488_);
    v___x_3490_ = lean_usize_land(v___x_3486_, v___x_3489_);
    v___x_3491_ = lean_array_uget_borrowed(v_buckets_3477_, v___x_3490_);
    v___x_3492_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg(v_a_3476_, v___x_3491_);
    return v___x_3492_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg___boxed(
    mut v_m_3493_: *mut crate::leanh::LeanObject,
    mut v_a_3494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3495_: u8 = 0;
    let mut v_r_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3495_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg(v_m_3493_, v_a_3494_);
    crate::leanh::lean_dec(v_a_3494_);
    crate::leanh::lean_dec_ref(v_m_3493_);
    v_r_3496_ = crate::leanh::lean_box((v_res_3495_) as usize);
    return v_r_3496_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg(
    mut v_as_3497_: *mut crate::leanh::LeanObject,
    mut v_sz_3498_: usize,
    mut v_i_3499_: usize,
    mut v_b_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: usize = 0;
    let mut v___x_3506_: usize = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_3514_: u8 = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: u8 = 0;
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_3520_: u8 = 0;
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3508_ = lean_usize_dec_lt(v_i_3499_, v_sz_3498_);
                if v___x_3508_ == 0 {
                    v___x_3509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3509_, 0, v_b_3500_);
                    return v___x_3509_;
                } else {
                    v___x_3510_ = lean_st_ref_get(v___y_3501_);
                    v_values_3511_ = crate::leanh::lean_ctor_get(v___x_3510_, 0);
                    crate::leanh::lean_inc_ref(v_values_3511_);
                    crate::leanh::lean_dec(v___x_3510_);
                    v_a_3512_ = lean_array_uget_borrowed(v_as_3497_, v_i_3499_);
                    v_fvarId_3513_ = crate::leanh::lean_ctor_get(v_a_3512_, 0);
                    v_borrow_3514_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3512_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v___x_3515_ = crate::leanh::lean_box(0);
                    v___x_3531_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg(v_values_3511_, v_fvarId_3513_);
                    crate::leanh::lean_dec_ref(v_values_3511_);
                    if v___x_3531_ == 0 {
                        if v_borrow_3514_ == 0 {
                            v___x_3532_ = 0;
                            v___y_3517_ = v___x_3532_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3533_ = 1;
                            v___y_3517_ = v___x_3533_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3504_ = v___x_3515_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3505_ = 1usize;
                v___x_3506_ = lean_usize_add(v_i_3499_, v___x_3505_);
                v_i_3499_ = v___x_3506_;
                v_b_3500_ = v_a_3504_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3518_ = lean_st_ref_take(v___y_3501_);
                v_values_3519_ = crate::leanh::lean_ctor_get(v___x_3518_, 0);
                v_modified_3520_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3518_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3530_ = (!crate::leanh::lean_is_exclusive(v___x_3518_)) as u8;
                if v_isSharedCheck_3530_ == 0 {
                    v___x_3522_ = v___x_3518_;
                    v_isShared_3523_ = v_isSharedCheck_3530_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_values_3519_);
                    crate::leanh::lean_dec(v___x_3518_);
                    v___x_3522_ = crate::leanh::lean_box(0);
                    v_isShared_3523_ = v_isSharedCheck_3530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3524_ = crate::leanh::lean_box((v___y_3517_) as usize);
                crate::leanh::lean_inc(v_fvarId_3513_);
                v___x_3525_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3519_, v_fvarId_3513_, v___x_3524_);
                if v_isShared_3523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3522_, 0, v___x_3525_);
                    v___x_3527_ = v___x_3522_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3525_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3529_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_modified_3520_,
                    );
                    v___x_3527_ = v_reuseFailAlloc_3529_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3528_ = lean_st_ref_set(v___y_3501_, v___x_3527_);
                v_a_3504_ = v___x_3515_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg___boxed(
    mut v_as_3534_: *mut crate::leanh::LeanObject,
    mut v_sz_3535_: *mut crate::leanh::LeanObject,
    mut v_i_3536_: *mut crate::leanh::LeanObject,
    mut v_b_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3540_: usize = 0;
    let mut v_i_boxed_3541_: usize = 0;
    let mut v_res_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3540_ = crate::leanh::lean_unbox_usize(v_sz_3535_);
    crate::leanh::lean_dec(v_sz_3535_);
    v_i_boxed_3541_ = crate::leanh::lean_unbox_usize(v_i_3536_);
    crate::leanh::lean_dec(v_i_3536_);
    v_res_3542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg(v_as_3534_, v_sz_boxed_3540_, v_i_boxed_3541_, v_b_3537_, v___y_3538_);
    crate::leanh::lean_dec(v___y_3538_);
    crate::leanh::lean_dec_ref(v_as_3534_);
    return v_res_3542_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3544_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_3545_ = crate::leanh::lean_unsigned_to_nat(58);
    v___x_3546_ = crate::leanh::lean_unsigned_to_nat(96);
    v___x_3547_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__0;
    v___x_3548_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0;
    v___x_3549_ = l_mkPanicMessageWithDecl(
        v___x_3548_,
        v___x_3547_,
        v___x_3546_,
        v___x_3545_,
        v___x_3544_,
    );
    return v___x_3549_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3550_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_3551_ = crate::leanh::lean_unsigned_to_nat(61);
    v___x_3552_ = crate::leanh::lean_unsigned_to_nat(104);
    v___x_3553_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__0;
    v___x_3554_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0;
    v___x_3555_ = l_mkPanicMessageWithDecl(
        v___x_3554_,
        v___x_3553_,
        v___x_3552_,
        v___x_3551_,
        v___x_3550_,
    );
    return v___x_3555_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode(
    mut v_code_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
    mut v_a_3560_: *mut crate::leanh::LeanObject,
    mut v_a_3561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3574_: usize = 0;
    let mut v___x_3575_: usize = 0;
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: u8 = 0;
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3589_: usize = 0;
    let mut v___x_3590_: usize = 0;
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3599_: u8 = 0;
    let mut v_unused_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v_cases_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v_alts_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: u8 = 0;
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: usize = 0;
    let mut v___x_3636_: usize = 0;
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: usize = 0;
    let mut v___x_3639_: usize = 0;
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v_unused_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3658_: u8 = 0;
    let mut v_unused_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_3556_) {
                0 => {
                    v_decl_3563_ = crate::leanh::lean_ctor_get(v_code_3556_, 0);
                    crate::leanh::lean_inc_ref(v_decl_3563_);
                    v_k_3564_ = crate::leanh::lean_ctor_get(v_code_3556_, 1);
                    crate::leanh::lean_inc_ref(v_k_3564_);
                    crate::leanh::lean_dec_ref_known(v_code_3556_, 2);
                    v_fvarId_3565_ = crate::leanh::lean_ctor_get(v_decl_3563_, 0);
                    crate::leanh::lean_inc(v_fvarId_3565_);
                    v_value_3566_ = crate::leanh::lean_ctor_get(v_decl_3563_, 3);
                    crate::leanh::lean_inc(v_value_3566_);
                    crate::leanh::lean_dec_ref(v_decl_3563_);
                    v___x_3567_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue(v_fvarId_3565_, v_value_3566_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                    if crate::leanh::lean_obj_tag(v___x_3567_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3567_, 1);
                        v_code_3556_ = v_k_3564_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_3564_);
                        return v___x_3567_;
                    }
                }
                2 => {
                    v_decl_3569_ = crate::leanh::lean_ctor_get(v_code_3556_, 0);
                    crate::leanh::lean_inc_ref(v_decl_3569_);
                    v_k_3570_ = crate::leanh::lean_ctor_get(v_code_3556_, 1);
                    crate::leanh::lean_inc_ref(v_k_3570_);
                    crate::leanh::lean_dec_ref_known(v_code_3556_, 2);
                    v_params_3571_ = crate::leanh::lean_ctor_get(v_decl_3569_, 2);
                    crate::leanh::lean_inc_ref(v_params_3571_);
                    v_value_3572_ = crate::leanh::lean_ctor_get(v_decl_3569_, 4);
                    crate::leanh::lean_inc_ref(v_value_3572_);
                    crate::leanh::lean_dec_ref(v_decl_3569_);
                    v___x_3573_ = crate::leanh::lean_box(0);
                    v_sz_3574_ = lean_array_size(v_params_3571_);
                    v___x_3575_ = 0usize;
                    v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg(v_params_3571_, v_sz_3574_, v___x_3575_, v___x_3573_, v_a_3557_);
                    crate::leanh::lean_dec_ref(v_params_3571_);
                    if crate::leanh::lean_obj_tag(v___x_3576_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3576_, 1);
                        v___x_3577_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode(v_k_3570_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                        if crate::leanh::lean_obj_tag(v___x_3577_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3577_, 1);
                            v_code_3556_ = v_value_3572_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_value_3572_);
                            return v___x_3577_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_value_3572_);
                        crate::leanh::lean_dec_ref(v_k_3570_);
                        return v___x_3576_;
                    }
                }
                3 => {
                    v_fvarId_3579_ = crate::leanh::lean_ctor_get(v_code_3556_, 0);
                    crate::leanh::lean_inc(v_fvarId_3579_);
                    v_args_3580_ = crate::leanh::lean_ctor_get(v_code_3556_, 1);
                    crate::leanh::lean_inc_ref(v_args_3580_);
                    crate::leanh::lean_dec_ref_known(v_code_3556_, 2);
                    v___x_3581_ = 1;
                    v___x_3582_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
                        v___x_3581_,
                        v_fvarId_3579_,
                        v_a_3559_,
                    );
                    crate::leanh::lean_dec(v_fvarId_3579_);
                    if crate::leanh::lean_obj_tag(v___x_3582_) == 0 {
                        v_a_3583_ = crate::leanh::lean_ctor_get(v___x_3582_, 0);
                        crate::leanh::lean_inc(v_a_3583_);
                        crate::leanh::lean_dec_ref_known(v___x_3582_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3583_) == 1 {
                            v_val_3584_ = crate::leanh::lean_ctor_get(v_a_3583_, 0);
                            crate::leanh::lean_inc(v_val_3584_);
                            crate::leanh::lean_dec_ref_known(v_a_3583_, 1);
                            v_params_3585_ = crate::leanh::lean_ctor_get(v_val_3584_, 2);
                            crate::leanh::lean_inc_ref(v_params_3585_);
                            crate::leanh::lean_dec(v_val_3584_);
                            v___x_3586_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_3587_ = lean_array_get_size(v_params_3585_);
                            v___x_3588_ = l_Array_toSubarray___redArg(
                                v_params_3585_,
                                v___x_3586_,
                                v___x_3587_,
                            );
                            v_sz_3589_ = lean_array_size(v_args_3580_);
                            v___x_3590_ = 0usize;
                            v___x_3591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg(v_args_3580_, v_sz_3589_, v___x_3590_, v___x_3588_, v_a_3557_);
                            crate::leanh::lean_dec_ref(v_args_3580_);
                            if crate::leanh::lean_obj_tag(v___x_3591_) == 0 {
                                v_isSharedCheck_3599_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3591_)) as u8;
                                if v_isSharedCheck_3599_ == 0 {
                                    v_unused_3600_ = crate::leanh::lean_ctor_get(v___x_3591_, 0);
                                    crate::leanh::lean_dec(v_unused_3600_);
                                    v___x_3593_ = v___x_3591_;
                                    v_isShared_3594_ = v_isSharedCheck_3599_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3591_);
                                    v___x_3593_ = crate::leanh::lean_box(0);
                                    v_isShared_3594_ = v_isSharedCheck_3599_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3601_ = crate::leanh::lean_ctor_get(v___x_3591_, 0);
                                v_isSharedCheck_3608_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3591_)) as u8;
                                if v_isSharedCheck_3608_ == 0 {
                                    v___x_3603_ = v___x_3591_;
                                    v_isShared_3604_ = v_isSharedCheck_3608_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3601_);
                                    crate::leanh::lean_dec(v___x_3591_);
                                    v___x_3603_ = crate::leanh::lean_box(0);
                                    v_isShared_3604_ = v_isSharedCheck_3608_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3583_);
                            crate::leanh::lean_dec_ref(v_args_3580_);
                            v___x_3609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1);
                            v___x_3610_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(v___x_3609_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                            return v___x_3610_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_3580_);
                        v_a_3611_ = crate::leanh::lean_ctor_get(v___x_3582_, 0);
                        v_isSharedCheck_3618_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3582_)) as u8;
                        if v_isSharedCheck_3618_ == 0 {
                            v___x_3613_ = v___x_3582_;
                            v_isShared_3614_ = v_isSharedCheck_3618_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3611_);
                            crate::leanh::lean_dec(v___x_3582_);
                            v___x_3613_ = crate::leanh::lean_box(0);
                            v_isShared_3614_ = v_isSharedCheck_3618_;
                            state = 5;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_3619_ = crate::leanh::lean_ctor_get(v_code_3556_, 0);
                    v_isSharedCheck_3641_ = (!crate::leanh::lean_is_exclusive(v_code_3556_)) as u8;
                    if v_isSharedCheck_3641_ == 0 {
                        v___x_3621_ = v_code_3556_;
                        v_isShared_3622_ = v_isSharedCheck_3641_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_3619_);
                        crate::leanh::lean_dec(v_code_3556_);
                        v___x_3621_ = crate::leanh::lean_box(0);
                        v_isShared_3622_ = v_isSharedCheck_3641_;
                        state = 7;
                        continue;
                    }
                }
                5 => {
                    v_isSharedCheck_3649_ = (!crate::leanh::lean_is_exclusive(v_code_3556_)) as u8;
                    if v_isSharedCheck_3649_ == 0 {
                        v_unused_3650_ = crate::leanh::lean_ctor_get(v_code_3556_, 0);
                        crate::leanh::lean_dec(v_unused_3650_);
                        v___x_3643_ = v_code_3556_;
                        v_isShared_3644_ = v_isSharedCheck_3649_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_3556_);
                        v___x_3643_ = crate::leanh::lean_box(0);
                        v_isShared_3644_ = v_isSharedCheck_3649_;
                        state = 10;
                        continue;
                    }
                }
                6 => {
                    v_isSharedCheck_3658_ = (!crate::leanh::lean_is_exclusive(v_code_3556_)) as u8;
                    if v_isSharedCheck_3658_ == 0 {
                        v_unused_3659_ = crate::leanh::lean_ctor_get(v_code_3556_, 0);
                        crate::leanh::lean_dec(v_unused_3659_);
                        v___x_3652_ = v_code_3556_;
                        v_isShared_3653_ = v_isSharedCheck_3658_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_3556_);
                        v___x_3652_ = crate::leanh::lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3658_;
                        state = 12;
                        continue;
                    }
                }
                8 => {
                    v_k_3660_ = crate::leanh::lean_ctor_get(v_code_3556_, 3);
                    crate::leanh::lean_inc_ref(v_k_3660_);
                    crate::leanh::lean_dec_ref_known(v_code_3556_, 4);
                    v_code_3556_ = v_k_3660_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_3662_ = crate::leanh::lean_ctor_get(v_code_3556_, 5);
                    crate::leanh::lean_inc_ref(v_k_3662_);
                    crate::leanh::lean_dec_ref_known(v_code_3556_, 6);
                    v_code_3556_ = v_k_3662_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_code_3556_);
                    v___x_3664_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2);
                    v___x_3665_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(v___x_3664_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                    return v___x_3665_;
                }
            },
            1 => {
                v___x_3595_ = crate::leanh::lean_box(0);
                if v_isShared_3594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3593_, 0, v___x_3595_);
                    v___x_3597_ = v___x_3593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3595_);
                    v___x_3597_ = v_reuseFailAlloc_3598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3597_;
            }
            3 => {
                if v_isShared_3604_ == 0 {
                    v___x_3606_ = v___x_3603_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3606_;
            }
            5 => {
                if v_isShared_3614_ == 0 {
                    v___x_3616_ = v___x_3613_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
                    v___x_3616_ = v_reuseFailAlloc_3617_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3616_;
            }
            7 => {
                v_alts_3623_ = crate::leanh::lean_ctor_get(v_cases_3619_, 3);
                crate::leanh::lean_inc_ref(v_alts_3623_);
                crate::leanh::lean_dec_ref(v_cases_3619_);
                v___x_3624_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3625_ = lean_array_get_size(v_alts_3623_);
                v___x_3626_ = crate::leanh::lean_box(0);
                v___x_3627_ = lean_nat_dec_lt(v___x_3624_, v___x_3625_);
                if v___x_3627_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_3623_);
                    if v_isShared_3622_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3621_, 0);
                        crate::leanh::lean_ctor_set(v___x_3621_, 0, v___x_3626_);
                        v___x_3629_ = v___x_3621_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3626_);
                        v___x_3629_ = v_reuseFailAlloc_3630_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___x_3631_ = lean_nat_dec_le(v___x_3625_, v___x_3625_);
                    if v___x_3631_ == 0 {
                        if v___x_3627_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_3623_);
                            if v_isShared_3622_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_3621_, 0);
                                crate::leanh::lean_ctor_set(v___x_3621_, 0, v___x_3626_);
                                v___x_3633_ = v___x_3621_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_3634_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3626_);
                                v___x_3633_ = v_reuseFailAlloc_3634_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3621_);
                            v___x_3635_ = 0usize;
                            v___x_3636_ = lean_usize_of_nat(v___x_3625_);
                            v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4(v_alts_3623_, v___x_3635_, v___x_3636_, v___x_3626_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                            crate::leanh::lean_dec_ref(v_alts_3623_);
                            return v___x_3637_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3621_);
                        v___x_3638_ = 0usize;
                        v___x_3639_ = lean_usize_of_nat(v___x_3625_);
                        v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4(v_alts_3623_, v___x_3638_, v___x_3639_, v___x_3626_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                        crate::leanh::lean_dec_ref(v_alts_3623_);
                        return v___x_3640_;
                    }
                }
            }
            8 => {
                return v___x_3629_;
            }
            9 => {
                return v___x_3633_;
            }
            10 => {
                v___x_3645_ = crate::leanh::lean_box(0);
                if v_isShared_3644_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3643_, 0);
                    crate::leanh::lean_ctor_set(v___x_3643_, 0, v___x_3645_);
                    v___x_3647_ = v___x_3643_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
                    v___x_3647_ = v_reuseFailAlloc_3648_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3647_;
            }
            12 => {
                v___x_3654_ = crate::leanh::lean_box(0);
                if v_isShared_3653_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3652_, 0);
                    crate::leanh::lean_ctor_set(v___x_3652_, 0, v___x_3654_);
                    v___x_3656_ = v___x_3652_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
                    v___x_3656_ = v_reuseFailAlloc_3657_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___boxed(
    mut v_code_3666_: *mut crate::leanh::LeanObject,
    mut v_a_3667_: *mut crate::leanh::LeanObject,
    mut v_a_3668_: *mut crate::leanh::LeanObject,
    mut v_a_3669_: *mut crate::leanh::LeanObject,
    mut v_a_3670_: *mut crate::leanh::LeanObject,
    mut v_a_3671_: *mut crate::leanh::LeanObject,
    mut v_a_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3673_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode(v_code_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_);
    crate::leanh::lean_dec(v_a_3671_);
    crate::leanh::lean_dec_ref(v_a_3670_);
    crate::leanh::lean_dec(v_a_3669_);
    crate::leanh::lean_dec_ref(v_a_3668_);
    crate::leanh::lean_dec(v_a_3667_);
    return v_res_3673_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4(
    mut v_as_3674_: *mut crate::leanh::LeanObject,
    mut v_i_3675_: usize,
    mut v_stop_3676_: usize,
    mut v_b_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: usize = 0;
    let mut v___x_3690_: usize = 0;
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3684_ = lean_usize_dec_eq(v_i_3675_, v_stop_3676_);
                if v___x_3684_ == 0 {
                    v___x_3685_ = lean_array_uget_borrowed(v_as_3674_, v_i_3675_);
                    v___x_3686_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___boxed as *mut core::ffi::c_void, 7, 0);
                    crate::leanh::lean_inc(v___x_3685_);
                    v___x_3687_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg(v___x_3685_, v___x_3686_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
                    if crate::leanh::lean_obj_tag(v___x_3687_) == 0 {
                        v_a_3688_ = crate::leanh::lean_ctor_get(v___x_3687_, 0);
                        crate::leanh::lean_inc(v_a_3688_);
                        crate::leanh::lean_dec_ref_known(v___x_3687_, 1);
                        v___x_3689_ = 1usize;
                        v___x_3690_ = lean_usize_add(v_i_3675_, v___x_3689_);
                        v_i_3675_ = v___x_3690_;
                        v_b_3677_ = v_a_3688_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3687_;
                    }
                } else {
                    v___x_3692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3692_, 0, v_b_3677_);
                    return v___x_3692_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4___boxed(
    mut v_as_3693_: *mut crate::leanh::LeanObject,
    mut v_i_3694_: *mut crate::leanh::LeanObject,
    mut v_stop_3695_: *mut crate::leanh::LeanObject,
    mut v_b_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
    mut v___y_3699_: *mut crate::leanh::LeanObject,
    mut v___y_3700_: *mut crate::leanh::LeanObject,
    mut v___y_3701_: *mut crate::leanh::LeanObject,
    mut v___y_3702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3703_: usize = 0;
    let mut v_stop_boxed_3704_: usize = 0;
    let mut v_res_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3703_ = crate::leanh::lean_unbox_usize(v_i_3694_);
    crate::leanh::lean_dec(v_i_3694_);
    v_stop_boxed_3704_ = crate::leanh::lean_unbox_usize(v_stop_3695_);
    crate::leanh::lean_dec(v_stop_3695_);
    v_res_3705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4(v_as_3693_, v_i_boxed_3703_, v_stop_boxed_3704_, v_b_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
    crate::leanh::lean_dec(v___y_3701_);
    crate::leanh::lean_dec_ref(v___y_3700_);
    crate::leanh::lean_dec(v___y_3699_);
    crate::leanh::lean_dec_ref(v___y_3698_);
    crate::leanh::lean_dec(v___y_3697_);
    crate::leanh::lean_dec_ref(v_as_3693_);
    return v_res_3705_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1(
    mut v_00_u03b2_3706_: *mut crate::leanh::LeanObject,
    mut v_m_3707_: *mut crate::leanh::LeanObject,
    mut v_a_3708_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3709_: u8 = 0;
    v___x_3709_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg(v_m_3707_, v_a_3708_);
    return v___x_3709_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___boxed(
    mut v_00_u03b2_3710_: *mut crate::leanh::LeanObject,
    mut v_m_3711_: *mut crate::leanh::LeanObject,
    mut v_a_3712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3713_: u8 = 0;
    let mut v_r_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3713_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1(v_00_u03b2_3710_, v_m_3711_, v_a_3712_);
    crate::leanh::lean_dec(v_a_3712_);
    crate::leanh::lean_dec_ref(v_m_3711_);
    v_r_3714_ = crate::leanh::lean_box((v_res_3713_) as usize);
    return v_r_3714_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2(
    mut v_as_3715_: *mut crate::leanh::LeanObject,
    mut v_sz_3716_: usize,
    mut v_i_3717_: usize,
    mut v_b_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg(v_as_3715_, v_sz_3716_, v_i_3717_, v_b_3718_, v___y_3719_);
    return v___x_3725_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___boxed(
    mut v_as_3726_: *mut crate::leanh::LeanObject,
    mut v_sz_3727_: *mut crate::leanh::LeanObject,
    mut v_i_3728_: *mut crate::leanh::LeanObject,
    mut v_b_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
    mut v___y_3734_: *mut crate::leanh::LeanObject,
    mut v___y_3735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3736_: usize = 0;
    let mut v_i_boxed_3737_: usize = 0;
    let mut v_res_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3736_ = crate::leanh::lean_unbox_usize(v_sz_3727_);
    crate::leanh::lean_dec(v_sz_3727_);
    v_i_boxed_3737_ = crate::leanh::lean_unbox_usize(v_i_3728_);
    crate::leanh::lean_dec(v_i_3728_);
    v_res_3738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2(v_as_3726_, v_sz_boxed_3736_, v_i_boxed_3737_, v_b_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
    crate::leanh::lean_dec(v___y_3734_);
    crate::leanh::lean_dec_ref(v___y_3733_);
    crate::leanh::lean_dec(v___y_3732_);
    crate::leanh::lean_dec_ref(v___y_3731_);
    crate::leanh::lean_dec(v___y_3730_);
    crate::leanh::lean_dec_ref(v_as_3726_);
    return v_res_3738_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3(
    mut v_as_3739_: *mut crate::leanh::LeanObject,
    mut v_sz_3740_: usize,
    mut v_i_3741_: usize,
    mut v_b_3742_: *mut crate::leanh::LeanObject,
    mut v___y_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg(v_as_3739_, v_sz_3740_, v_i_3741_, v_b_3742_, v___y_3743_);
    return v___x_3749_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___boxed(
    mut v_as_3750_: *mut crate::leanh::LeanObject,
    mut v_sz_3751_: *mut crate::leanh::LeanObject,
    mut v_i_3752_: *mut crate::leanh::LeanObject,
    mut v_b_3753_: *mut crate::leanh::LeanObject,
    mut v___y_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3760_: usize = 0;
    let mut v_i_boxed_3761_: usize = 0;
    let mut v_res_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3760_ = crate::leanh::lean_unbox_usize(v_sz_3751_);
    crate::leanh::lean_dec(v_sz_3751_);
    v_i_boxed_3761_ = crate::leanh::lean_unbox_usize(v_i_3752_);
    crate::leanh::lean_dec(v_i_3752_);
    v_res_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3(v_as_3750_, v_sz_boxed_3760_, v_i_boxed_3761_, v_b_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
    crate::leanh::lean_dec(v___y_3758_);
    crate::leanh::lean_dec_ref(v___y_3757_);
    crate::leanh::lean_dec(v___y_3756_);
    crate::leanh::lean_dec_ref(v___y_3755_);
    crate::leanh::lean_dec(v___y_3754_);
    crate::leanh::lean_dec_ref(v_as_3750_);
    return v_res_3762_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_loop(
    mut v_decl_3763_: *mut crate::leanh::LeanObject,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
    mut v_a_3766_: *mut crate::leanh::LeanObject,
    mut v_a_3767_: *mut crate::leanh::LeanObject,
    mut v_a_3768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_3777_: u8 = 0;
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3781_ = lean_st_ref_take(v_a_3764_);
                v_values_3782_ = crate::leanh::lean_ctor_get(v___x_3781_, 0);
                v_isSharedCheck_3794_ = (!crate::leanh::lean_is_exclusive(v___x_3781_)) as u8;
                if v_isSharedCheck_3794_ == 0 {
                    v___x_3784_ = v___x_3781_;
                    v_isShared_3785_ = v_isSharedCheck_3794_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_values_3782_);
                    crate::leanh::lean_dec(v___x_3781_);
                    v___x_3784_ = crate::leanh::lean_box(0);
                    v_isShared_3785_ = v_isSharedCheck_3794_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3776_ = lean_st_ref_get(v___y_3771_);
                v_modified_3777_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3776_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec(v___x_3776_);
                if v_modified_3777_ == 0 {
                    crate::leanh::lean_dec_ref(v_decl_3763_);
                    v___x_3778_ = crate::leanh::lean_box(0);
                    v___x_3779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3779_, 0, v___x_3778_);
                    return v___x_3779_;
                } else {
                    v_a_3764_ = v___y_3771_;
                    v_a_3765_ = v___y_3772_;
                    v_a_3766_ = v___y_3773_;
                    v_a_3767_ = v___y_3774_;
                    v_a_3768_ = v___y_3775_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_3786_ = 0;
                if v_isShared_3785_ == 0 {
                    v___x_3788_ = v___x_3784_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3793_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_values_3782_);
                    v___x_3788_ = v_reuseFailAlloc_3793_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3788_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3786_,
                );
                v___x_3789_ = lean_st_ref_set(v_a_3764_, v___x_3788_);
                v_value_3790_ = crate::leanh::lean_ctor_get(v_decl_3763_, 1);
                if crate::leanh::lean_obj_tag(v_value_3790_) == 0 {
                    v_code_3791_ = crate::leanh::lean_ctor_get(v_value_3790_, 0);
                    crate::leanh::lean_inc_ref(v_code_3791_);
                    v___x_3792_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode(v_code_3791_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                    if crate::leanh::lean_obj_tag(v___x_3792_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3792_, 1);
                        v___y_3771_ = v_a_3764_;
                        v___y_3772_ = v_a_3765_;
                        v___y_3773_ = v_a_3766_;
                        v___y_3774_ = v_a_3767_;
                        v___y_3775_ = v_a_3768_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_decl_3763_);
                        return v___x_3792_;
                    }
                } else {
                    v___y_3771_ = v_a_3764_;
                    v___y_3772_ = v_a_3765_;
                    v___y_3773_ = v_a_3766_;
                    v___y_3774_ = v_a_3767_;
                    v___y_3775_ = v_a_3768_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_loop___boxed(
    mut v_decl_3795_: *mut crate::leanh::LeanObject,
    mut v_a_3796_: *mut crate::leanh::LeanObject,
    mut v_a_3797_: *mut crate::leanh::LeanObject,
    mut v_a_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3802_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_loop(v_decl_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
    crate::leanh::lean_dec(v_a_3800_);
    crate::leanh::lean_dec_ref(v_a_3799_);
    crate::leanh::lean_dec(v_a_3798_);
    crate::leanh::lean_dec_ref(v_a_3797_);
    crate::leanh::lean_dec(v_a_3796_);
    return v_res_3802_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg(
    mut v_as_3803_: *mut crate::leanh::LeanObject,
    mut v_sz_3804_: usize,
    mut v_i_3805_: usize,
    mut v_b_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3809_: u8 = 0;
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_3812_: u8 = 0;
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3815_: u8 = 0;
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_3818_: u8 = 0;
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3821_: u8 = 0;
    let mut v_fvarId_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: usize = 0;
    let mut v___x_3829_: usize = 0;
    let mut v_reuseFailAlloc_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3809_ = lean_usize_dec_lt(v_i_3805_, v_sz_3804_);
                if v___x_3809_ == 0 {
                    v___x_3810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3810_, 0, v_b_3806_);
                    return v___x_3810_;
                } else {
                    v_a_3811_ = lean_array_uget_borrowed(v_as_3803_, v_i_3805_);
                    v_borrow_3812_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3811_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v___x_3813_ = crate::leanh::lean_box(0);
                    if v_borrow_3812_ == 0 {
                        v___x_3833_ = 3;
                        v___y_3815_ = v___x_3833_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3834_ = 1;
                        v___y_3815_ = v___x_3834_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3816_ = lean_st_ref_take(v___y_3807_);
                v_values_3817_ = crate::leanh::lean_ctor_get(v___x_3816_, 0);
                v_modified_3818_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3816_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3832_ = (!crate::leanh::lean_is_exclusive(v___x_3816_)) as u8;
                if v_isSharedCheck_3832_ == 0 {
                    v___x_3820_ = v___x_3816_;
                    v_isShared_3821_ = v_isSharedCheck_3832_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_values_3817_);
                    crate::leanh::lean_dec(v___x_3816_);
                    v___x_3820_ = crate::leanh::lean_box(0);
                    v_isShared_3821_ = v_isSharedCheck_3832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fvarId_3822_ = crate::leanh::lean_ctor_get(v_a_3811_, 0);
                v___x_3823_ = crate::leanh::lean_box((v___y_3815_) as usize);
                crate::leanh::lean_inc(v_fvarId_3822_);
                v___x_3824_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3817_, v_fvarId_3822_, v___x_3823_);
                if v_isShared_3821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3820_, 0, v___x_3824_);
                    v___x_3826_ = v___x_3820_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3824_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3831_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_modified_3818_,
                    );
                    v___x_3826_ = v_reuseFailAlloc_3831_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3827_ = lean_st_ref_set(v___y_3807_, v___x_3826_);
                v___x_3828_ = 1usize;
                v___x_3829_ = lean_usize_add(v_i_3805_, v___x_3828_);
                v_i_3805_ = v___x_3829_;
                v_b_3806_ = v___x_3813_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg___boxed(
    mut v_as_3835_: *mut crate::leanh::LeanObject,
    mut v_sz_3836_: *mut crate::leanh::LeanObject,
    mut v_i_3837_: *mut crate::leanh::LeanObject,
    mut v_b_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3841_: usize = 0;
    let mut v_i_boxed_3842_: usize = 0;
    let mut v_res_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3841_ = crate::leanh::lean_unbox_usize(v_sz_3836_);
    crate::leanh::lean_dec(v_sz_3836_);
    v_i_boxed_3842_ = crate::leanh::lean_unbox_usize(v_i_3837_);
    crate::leanh::lean_dec(v_i_3837_);
    v_res_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg(v_as_3835_, v_sz_boxed_3841_, v_i_boxed_3842_, v_b_3838_, v___y_3839_);
    crate::leanh::lean_dec(v___y_3839_);
    crate::leanh::lean_dec_ref(v_as_3835_);
    return v_res_3843_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl(
    mut v_decl_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
    mut v_a_3846_: *mut crate::leanh::LeanObject,
    mut v_a_3847_: *mut crate::leanh::LeanObject,
    mut v_a_3848_: *mut crate::leanh::LeanObject,
    mut v_a_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_value_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3855_: usize = 0;
    let mut v___x_3856_: usize = 0;
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3860_: u8 = 0;
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3864_: u8 = 0;
    let mut v_unused_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_3851_ = crate::leanh::lean_ctor_get(v_decl_3844_, 1);
                if crate::leanh::lean_obj_tag(v_value_3851_) == 0 {
                    v_toSignature_3852_ = crate::leanh::lean_ctor_get(v_decl_3844_, 0);
                    v_params_3853_ = crate::leanh::lean_ctor_get(v_toSignature_3852_, 3);
                    v___x_3854_ = crate::leanh::lean_box(0);
                    v_sz_3855_ = lean_array_size(v_params_3853_);
                    v___x_3856_ = 0usize;
                    v___x_3857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg(v_params_3853_, v_sz_3855_, v___x_3856_, v___x_3854_, v_a_3845_);
                    if crate::leanh::lean_obj_tag(v___x_3857_) == 0 {
                        v_isSharedCheck_3864_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3857_)) as u8;
                        if v_isSharedCheck_3864_ == 0 {
                            v_unused_3865_ = crate::leanh::lean_ctor_get(v___x_3857_, 0);
                            crate::leanh::lean_dec(v_unused_3865_);
                            v___x_3859_ = v___x_3857_;
                            v_isShared_3860_ = v_isSharedCheck_3864_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3857_);
                            v___x_3859_ = crate::leanh::lean_box(0);
                            v_isShared_3860_ = v_isSharedCheck_3864_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3857_;
                    }
                } else {
                    v___x_3866_ = crate::leanh::lean_box(0);
                    v___x_3867_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3867_, 0, v___x_3866_);
                    return v___x_3867_;
                }
            }
            1 => {
                if v_isShared_3860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3859_, 0, v___x_3854_);
                    v___x_3862_ = v___x_3859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3854_);
                    v___x_3862_ = v_reuseFailAlloc_3863_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl___boxed(
    mut v_decl_3868_: *mut crate::leanh::LeanObject,
    mut v_a_3869_: *mut crate::leanh::LeanObject,
    mut v_a_3870_: *mut crate::leanh::LeanObject,
    mut v_a_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3875_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl(v_decl_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
    crate::leanh::lean_dec(v_a_3873_);
    crate::leanh::lean_dec_ref(v_a_3872_);
    crate::leanh::lean_dec(v_a_3871_);
    crate::leanh::lean_dec_ref(v_a_3870_);
    crate::leanh::lean_dec(v_a_3869_);
    crate::leanh::lean_dec_ref(v_decl_3868_);
    return v_res_3875_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0(
    mut v_as_3876_: *mut crate::leanh::LeanObject,
    mut v_sz_3877_: usize,
    mut v_i_3878_: usize,
    mut v_b_3879_: *mut crate::leanh::LeanObject,
    mut v___y_3880_: *mut crate::leanh::LeanObject,
    mut v___y_3881_: *mut crate::leanh::LeanObject,
    mut v___y_3882_: *mut crate::leanh::LeanObject,
    mut v___y_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg(v_as_3876_, v_sz_3877_, v_i_3878_, v_b_3879_, v___y_3880_);
    return v___x_3886_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___boxed(
    mut v_as_3887_: *mut crate::leanh::LeanObject,
    mut v_sz_3888_: *mut crate::leanh::LeanObject,
    mut v_i_3889_: *mut crate::leanh::LeanObject,
    mut v_b_3890_: *mut crate::leanh::LeanObject,
    mut v___y_3891_: *mut crate::leanh::LeanObject,
    mut v___y_3892_: *mut crate::leanh::LeanObject,
    mut v___y_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
    mut v___y_3896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3897_: usize = 0;
    let mut v_i_boxed_3898_: usize = 0;
    let mut v_res_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3897_ = crate::leanh::lean_unbox_usize(v_sz_3888_);
    crate::leanh::lean_dec(v_sz_3888_);
    v_i_boxed_3898_ = crate::leanh::lean_unbox_usize(v_i_3889_);
    crate::leanh::lean_dec(v_i_3889_);
    v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0(v_as_3887_, v_sz_boxed_3897_, v_i_boxed_3898_, v_b_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
    crate::leanh::lean_dec(v___y_3895_);
    crate::leanh::lean_dec_ref(v___y_3894_);
    crate::leanh::lean_dec(v___y_3893_);
    crate::leanh::lean_dec_ref(v___y_3892_);
    crate::leanh::lean_dec(v___y_3891_);
    crate::leanh::lean_dec_ref(v_as_3887_);
    return v_res_3899_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_go(
    mut v_decl_3900_: *mut crate::leanh::LeanObject,
    mut v_a_3901_: *mut crate::leanh::LeanObject,
    mut v_a_3902_: *mut crate::leanh::LeanObject,
    mut v_a_3903_: *mut crate::leanh::LeanObject,
    mut v_a_3904_: *mut crate::leanh::LeanObject,
    mut v_a_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3907_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl(v_decl_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
    if crate::leanh::lean_obj_tag(v___x_3907_) == 0 {
        let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3907_, 1);
        v___x_3908_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_loop(v_decl_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
        return v___x_3908_;
    } else {
        crate::leanh::lean_dec_ref(v_decl_3900_);
        return v___x_3907_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_go___boxed(
    mut v_decl_3909_: *mut crate::leanh::LeanObject,
    mut v_a_3910_: *mut crate::leanh::LeanObject,
    mut v_a_3911_: *mut crate::leanh::LeanObject,
    mut v_a_3912_: *mut crate::leanh::LeanObject,
    mut v_a_3913_: *mut crate::leanh::LeanObject,
    mut v_a_3914_: *mut crate::leanh::LeanObject,
    mut v_a_3915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3916_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_go(v_decl_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_);
    crate::leanh::lean_dec(v_a_3914_);
    crate::leanh::lean_dec_ref(v_a_3913_);
    crate::leanh::lean_dec(v_a_3912_);
    crate::leanh::lean_dec_ref(v_a_3911_);
    crate::leanh::lean_dec(v_a_3910_);
    return v_res_3916_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(
    mut v_decl_3917_: *mut crate::leanh::LeanObject,
    mut v_a_3918_: *mut crate::leanh::LeanObject,
    mut v_a_3919_: *mut crate::leanh::LeanObject,
    mut v_a_3920_: *mut crate::leanh::LeanObject,
    mut v_a_3921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut v_unused_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3923_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2,
                );
                v___x_3924_ = lean_st_mk_ref(v___x_3923_);
                v___x_3925_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_go(v_decl_3917_, v___x_3924_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
                if crate::leanh::lean_obj_tag(v___x_3925_) == 0 {
                    v_isSharedCheck_3934_ = (!crate::leanh::lean_is_exclusive(v___x_3925_)) as u8;
                    if v_isSharedCheck_3934_ == 0 {
                        v_unused_3935_ = crate::leanh::lean_ctor_get(v___x_3925_, 0);
                        crate::leanh::lean_dec(v_unused_3935_);
                        v___x_3927_ = v___x_3925_;
                        v_isShared_3928_ = v_isSharedCheck_3934_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3925_);
                        v___x_3927_ = crate::leanh::lean_box(0);
                        v_isShared_3928_ = v_isSharedCheck_3934_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3924_);
                    v_a_3936_ = crate::leanh::lean_ctor_get(v___x_3925_, 0);
                    v_isSharedCheck_3943_ = (!crate::leanh::lean_is_exclusive(v___x_3925_)) as u8;
                    if v_isSharedCheck_3943_ == 0 {
                        v___x_3938_ = v___x_3925_;
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3936_);
                        crate::leanh::lean_dec(v___x_3925_);
                        v___x_3938_ = crate::leanh::lean_box(0);
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3929_ = lean_st_ref_get(v___x_3924_);
                crate::leanh::lean_dec(v___x_3924_);
                v_values_3930_ = crate::leanh::lean_ctor_get(v___x_3929_, 0);
                crate::leanh::lean_inc_ref(v_values_3930_);
                crate::leanh::lean_dec(v___x_3929_);
                if v_isShared_3928_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3927_, 0, v_values_3930_);
                    v___x_3932_ = v___x_3927_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_values_3930_);
                    v___x_3932_ = v_reuseFailAlloc_3933_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3932_;
            }
            3 => {
                if v_isShared_3939_ == 0 {
                    v___x_3941_ = v___x_3938_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows___boxed(
    mut v_decl_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
    mut v_a_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
    mut v_a_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3950_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(
        v_decl_3944_,
        v_a_3945_,
        v_a_3946_,
        v_a_3947_,
        v_a_3948_,
    );
    crate::leanh::lean_dec(v_a_3948_);
    crate::leanh::lean_dec_ref(v_a_3947_);
    crate::leanh::lean_dec(v_a_3946_);
    crate::leanh::lean_dec_ref(v_a_3945_);
    return v_res_3950_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow(
    mut v_x_3957_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3957_ {
        0 => {
            let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3958_ = crate::leanh::lean_box(0);
            return v___x_3958_;
        }
        1 => {
            let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3959_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__0;
            return v___x_3959_;
        }
        _ => {
            let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3960_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__1;
            return v___x_3960_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___boxed(
    mut v_x_3961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_41__boxed_3962_: u8 = 0;
    let mut v_res_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_41__boxed_3962_ = (crate::leanh::lean_unbox(v_x_3961_) as u8);
    v_res_3963_ =
        l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow(
            v_x_41__boxed_3962_,
        );
    return v_res_3963_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0_spec__1(
    mut v_msg_3964_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    v___x_3965_ = 0;
    v___x_3966_ = crate::leanh::lean_box((v___x_3965_) as usize);
    v___x_3967_ = lean_panic_fn_borrowed(v___x_3966_, v_msg_3964_);
    crate::leanh::lean_dec(v___x_3966_);
    v___x_3968_ = (crate::leanh::lean_unbox(v___x_3967_) as u8);
    crate::leanh::lean_dec(v___x_3967_);
    return v___x_3968_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0_spec__1___boxed(
    mut v_msg_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3970_: u8 = 0;
    let mut v_r_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0_spec__1(v_msg_3969_);
    v_r_3971_ = crate::leanh::lean_box((v_res_3970_) as usize);
    return v_r_3971_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3975_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__2;
    v___x_3976_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_3977_ = crate::leanh::lean_unsigned_to_nat(163);
    v___x_3978_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__1;
    v___x_3979_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__0;
    v___x_3980_ = l_mkPanicMessageWithDecl(
        v___x_3979_,
        v___x_3978_,
        v___x_3977_,
        v___x_3976_,
        v___x_3975_,
    );
    return v___x_3980_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0(
    mut v_a_3981_: *mut crate::leanh::LeanObject,
    mut v_x_3982_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v_key_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: u8 = 0;
    let mut v___x_3990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3982_) == 0 {
                    v___x_3983_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3);
                    v___x_3984_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0_spec__1(v___x_3983_);
                    return v___x_3984_;
                } else {
                    v_key_3985_ = crate::leanh::lean_ctor_get(v_x_3982_, 0);
                    v_value_3986_ = crate::leanh::lean_ctor_get(v_x_3982_, 1);
                    v_tail_3987_ = crate::leanh::lean_ctor_get(v_x_3982_, 2);
                    v___x_3988_ = l_Lean_instBEqFVarId_beq(v_key_3985_, v_a_3981_);
                    if v___x_3988_ == 0 {
                        v_x_3982_ = v_tail_3987_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3990_ = (crate::leanh::lean_unbox(v_value_3986_) as u8);
                        return v___x_3990_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___boxed(
    mut v_a_3991_: *mut crate::leanh::LeanObject,
    mut v_x_3992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3993_: u8 = 0;
    let mut v_r_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3993_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0(v_a_3991_, v_x_3992_);
    crate::leanh::lean_dec(v_x_3992_);
    crate::leanh::lean_dec(v_a_3991_);
    v_r_3994_ = crate::leanh::lean_box((v_res_3993_) as usize);
    return v_r_3994_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0(
    mut v_m_3995_: *mut crate::leanh::LeanObject,
    mut v_a_3996_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: u64 = 0;
    let mut v___x_4000_: u64 = 0;
    let mut v___x_4001_: u64 = 0;
    let mut v_fold_4002_: u64 = 0;
    let mut v___x_4003_: u64 = 0;
    let mut v___x_4004_: u64 = 0;
    let mut v___x_4005_: u64 = 0;
    let mut v___x_4006_: usize = 0;
    let mut v___x_4007_: usize = 0;
    let mut v___x_4008_: usize = 0;
    let mut v___x_4009_: usize = 0;
    let mut v___x_4010_: usize = 0;
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: u8 = 0;
    v_buckets_3997_ = crate::leanh::lean_ctor_get(v_m_3995_, 1);
    v___x_3998_ = lean_array_get_size(v_buckets_3997_);
    v___x_3999_ = l_Lean_instHashableFVarId_hash(v_a_3996_);
    v___x_4000_ = 32u64;
    v___x_4001_ = lean_uint64_shift_right(v___x_3999_, v___x_4000_);
    v_fold_4002_ = lean_uint64_xor(v___x_3999_, v___x_4001_);
    v___x_4003_ = 16u64;
    v___x_4004_ = lean_uint64_shift_right(v_fold_4002_, v___x_4003_);
    v___x_4005_ = lean_uint64_xor(v_fold_4002_, v___x_4004_);
    v___x_4006_ = lean_uint64_to_usize(v___x_4005_);
    v___x_4007_ = lean_usize_of_nat(v___x_3998_);
    v___x_4008_ = 1usize;
    v___x_4009_ = lean_usize_sub(v___x_4007_, v___x_4008_);
    v___x_4010_ = lean_usize_land(v___x_4006_, v___x_4009_);
    v___x_4011_ = lean_array_uget_borrowed(v_buckets_3997_, v___x_4010_);
    v___x_4012_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0(v_a_3996_, v___x_4011_);
    return v___x_4012_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0___boxed(
    mut v_m_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4015_: u8 = 0;
    let mut v_r_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0(v_m_4013_, v_a_4014_);
    crate::leanh::lean_dec(v_a_4014_);
    crate::leanh::lean_dec_ref(v_m_4013_);
    v_r_4016_ = crate::leanh::lean_box((v_res_4015_) as usize);
    return v_r_4016_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg(
    mut v_values_4017_: *mut crate::leanh::LeanObject,
    mut v_sz_4018_: usize,
    mut v_i_4019_: usize,
    mut v_bs_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4023_: u8 = 0;
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: usize = 0;
    let mut v___x_4032_: usize = 0;
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: u8 = 0;
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4045_: u8 = 0;
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4023_ = lean_usize_dec_lt(v_i_4019_, v_sz_4018_);
                if v___x_4023_ == 0 {
                    v___x_4024_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4024_, 0, v_bs_4020_);
                    return v___x_4024_;
                } else {
                    v_v_4025_ = lean_array_uget(v_bs_4020_, v_i_4019_);
                    v_fvarId_4026_ = crate::leanh::lean_ctor_get(v_v_4025_, 0);
                    v___x_4027_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4028_ = lean_array_uset(v_bs_4020_, v_i_4019_, v___x_4027_);
                    v___x_4035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0(v_values_4017_, v_fvarId_4026_);
                    v___x_4036_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow(v___x_4035_);
                    if crate::leanh::lean_obj_tag(v___x_4036_) == 0 {
                        v_a_4030_ = v_v_4025_;
                        state = 1;
                        continue;
                    } else {
                        v_val_4037_ = crate::leanh::lean_ctor_get(v___x_4036_, 0);
                        crate::leanh::lean_inc(v_val_4037_);
                        crate::leanh::lean_dec_ref_known(v___x_4036_, 1);
                        v___x_4038_ = 1;
                        v___x_4039_ = (crate::leanh::lean_unbox(v_val_4037_) as u8);
                        crate::leanh::lean_dec(v_val_4037_);
                        v___x_4040_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_4038_, v_v_4025_, v___x_4039_, v___y_4021_);
                        if crate::leanh::lean_obj_tag(v___x_4040_) == 0 {
                            v_a_4041_ = crate::leanh::lean_ctor_get(v___x_4040_, 0);
                            crate::leanh::lean_inc(v_a_4041_);
                            crate::leanh::lean_dec_ref_known(v___x_4040_, 1);
                            v_a_4030_ = v_a_4041_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_bs_x27_4028_);
                            v_a_4042_ = crate::leanh::lean_ctor_get(v___x_4040_, 0);
                            v_isSharedCheck_4049_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4040_)) as u8;
                            if v_isSharedCheck_4049_ == 0 {
                                v___x_4044_ = v___x_4040_;
                                v_isShared_4045_ = v_isSharedCheck_4049_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4042_);
                                crate::leanh::lean_dec(v___x_4040_);
                                v___x_4044_ = crate::leanh::lean_box(0);
                                v_isShared_4045_ = v_isSharedCheck_4049_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4031_ = 1usize;
                v___x_4032_ = lean_usize_add(v_i_4019_, v___x_4031_);
                v___x_4033_ = lean_array_uset(v_bs_x27_4028_, v_i_4019_, v_a_4030_);
                v_i_4019_ = v___x_4032_;
                v_bs_4020_ = v___x_4033_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4045_ == 0 {
                    v___x_4047_ = v___x_4044_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
                    v___x_4047_ = v_reuseFailAlloc_4048_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg___boxed(
    mut v_values_4050_: *mut crate::leanh::LeanObject,
    mut v_sz_4051_: *mut crate::leanh::LeanObject,
    mut v_i_4052_: *mut crate::leanh::LeanObject,
    mut v_bs_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4056_: usize = 0;
    let mut v_i_boxed_4057_: usize = 0;
    let mut v_res_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4056_ = crate::leanh::lean_unbox_usize(v_sz_4051_);
    crate::leanh::lean_dec(v_sz_4051_);
    v_i_boxed_4057_ = crate::leanh::lean_unbox_usize(v_i_4052_);
    crate::leanh::lean_dec(v_i_4052_);
    v_res_4058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg(v_values_4050_, v_sz_boxed_4056_, v_i_boxed_4057_, v_bs_4053_, v___y_4054_);
    crate::leanh::lean_dec(v___y_4054_);
    crate::leanh::lean_dec_ref(v_values_4050_);
    return v_res_4058_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams(
    mut v_values_4059_: *mut crate::leanh::LeanObject,
    mut v_ps_4060_: *mut crate::leanh::LeanObject,
    mut v_a_4061_: *mut crate::leanh::LeanObject,
    mut v_a_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_a_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4066_: usize = 0;
    let mut v___x_4067_: usize = 0;
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4066_ = lean_array_size(v_ps_4060_);
    v___x_4067_ = 0usize;
    v___x_4068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg(v_values_4059_, v_sz_4066_, v___x_4067_, v_ps_4060_, v_a_4062_);
    return v___x_4068_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams___boxed(
    mut v_values_4069_: *mut crate::leanh::LeanObject,
    mut v_ps_4070_: *mut crate::leanh::LeanObject,
    mut v_a_4071_: *mut crate::leanh::LeanObject,
    mut v_a_4072_: *mut crate::leanh::LeanObject,
    mut v_a_4073_: *mut crate::leanh::LeanObject,
    mut v_a_4074_: *mut crate::leanh::LeanObject,
    mut v_a_4075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4076_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams(v_values_4069_, v_ps_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
    crate::leanh::lean_dec(v_a_4074_);
    crate::leanh::lean_dec_ref(v_a_4073_);
    crate::leanh::lean_dec(v_a_4072_);
    crate::leanh::lean_dec_ref(v_a_4071_);
    crate::leanh::lean_dec_ref(v_values_4069_);
    return v_res_4076_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1(
    mut v_values_4077_: *mut crate::leanh::LeanObject,
    mut v_sz_4078_: usize,
    mut v_i_4079_: usize,
    mut v_bs_4080_: *mut crate::leanh::LeanObject,
    mut v___y_4081_: *mut crate::leanh::LeanObject,
    mut v___y_4082_: *mut crate::leanh::LeanObject,
    mut v___y_4083_: *mut crate::leanh::LeanObject,
    mut v___y_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg(v_values_4077_, v_sz_4078_, v_i_4079_, v_bs_4080_, v___y_4082_);
    return v___x_4086_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___boxed(
    mut v_values_4087_: *mut crate::leanh::LeanObject,
    mut v_sz_4088_: *mut crate::leanh::LeanObject,
    mut v_i_4089_: *mut crate::leanh::LeanObject,
    mut v_bs_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4096_: usize = 0;
    let mut v_i_boxed_4097_: usize = 0;
    let mut v_res_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4096_ = crate::leanh::lean_unbox_usize(v_sz_4088_);
    crate::leanh::lean_dec(v_sz_4088_);
    v_i_boxed_4097_ = crate::leanh::lean_unbox_usize(v_i_4089_);
    crate::leanh::lean_dec(v_i_4089_);
    v_res_4098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1(v_values_4087_, v_sz_boxed_4096_, v_i_boxed_4097_, v_bs_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
    crate::leanh::lean_dec(v___y_4094_);
    crate::leanh::lean_dec_ref(v___y_4093_);
    crate::leanh::lean_dec(v___y_4092_);
    crate::leanh::lean_dec_ref(v___y_4091_);
    crate::leanh::lean_dec_ref(v_values_4087_);
    return v_res_4098_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg(
    mut v_alt_4099_: *mut crate::leanh::LeanObject,
    mut v_f_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_a_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4125_: u8 = 0;
    let mut v_code_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_alt_4099_) {
                0 => {
                    v_code_4126_ = crate::leanh::lean_ctor_get(v_alt_4099_, 2);
                    crate::leanh::lean_inc_ref(v_code_4126_);
                    v___y_4107_ = v_code_4126_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_4127_ = crate::leanh::lean_ctor_get(v_alt_4099_, 1);
                    crate::leanh::lean_inc_ref(v_code_4127_);
                    v___y_4107_ = v_code_4127_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_4128_ = crate::leanh::lean_ctor_get(v_alt_4099_, 0);
                    crate::leanh::lean_inc_ref(v_code_4128_);
                    v___y_4107_ = v_code_4128_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                crate::leanh::lean_inc(v___y_4104_);
                crate::leanh::lean_inc_ref(v___y_4103_);
                crate::leanh::lean_inc(v___y_4102_);
                crate::leanh::lean_inc_ref(v___y_4101_);
                v___x_4108_ = crate::leanh::lean_apply_6(
                    v_f_4100_,
                    v___y_4107_,
                    v___y_4101_,
                    v___y_4102_,
                    v___y_4103_,
                    v___y_4104_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4108_) == 0 {
                    v_a_4109_ = crate::leanh::lean_ctor_get(v___x_4108_, 0);
                    v_isSharedCheck_4117_ = (!crate::leanh::lean_is_exclusive(v___x_4108_)) as u8;
                    if v_isSharedCheck_4117_ == 0 {
                        v___x_4111_ = v___x_4108_;
                        v_isShared_4112_ = v_isSharedCheck_4117_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4109_);
                        crate::leanh::lean_dec(v___x_4108_);
                        v___x_4111_ = crate::leanh::lean_box(0);
                        v_isShared_4112_ = v_isSharedCheck_4117_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_alt_4099_);
                    v_a_4118_ = crate::leanh::lean_ctor_get(v___x_4108_, 0);
                    v_isSharedCheck_4125_ = (!crate::leanh::lean_is_exclusive(v___x_4108_)) as u8;
                    if v_isSharedCheck_4125_ == 0 {
                        v___x_4120_ = v___x_4108_;
                        v_isShared_4121_ = v_isSharedCheck_4125_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4118_);
                        crate::leanh::lean_dec(v___x_4108_);
                        v___x_4120_ = crate::leanh::lean_box(0);
                        v_isShared_4121_ = v_isSharedCheck_4125_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4113_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_4099_, v_a_4109_);
                if v_isShared_4112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4111_, 0, v___x_4113_);
                    v___x_4115_ = v___x_4111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4116_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
                    v___x_4115_ = v_reuseFailAlloc_4116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4115_;
            }
            4 => {
                if v_isShared_4121_ == 0 {
                    v___x_4123_ = v___x_4120_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
                    v___x_4123_ = v_reuseFailAlloc_4124_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg___boxed(
    mut v_alt_4129_: *mut crate::leanh::LeanObject,
    mut v_f_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg(v_alt_4129_, v_f_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
    crate::leanh::lean_dec(v___y_4134_);
    crate::leanh::lean_dec_ref(v___y_4133_);
    crate::leanh::lean_dec(v___y_4132_);
    crate::leanh::lean_dec_ref(v___y_4131_);
    return v_res_4136_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0(
    mut v_pu_4137_: u8,
    mut v_alt_4138_: *mut crate::leanh::LeanObject,
    mut v_f_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
    mut v___y_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4145_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg(v_alt_4138_, v_f_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
    return v___x_4145_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___boxed(
    mut v_pu_4146_: *mut crate::leanh::LeanObject,
    mut v_alt_4147_: *mut crate::leanh::LeanObject,
    mut v_f_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4154_: u8 = 0;
    let mut v_res_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4154_ = (crate::leanh::lean_unbox(v_pu_4146_) as u8);
    v_res_4155_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0(v_pu_boxed_4154_, v_alt_4147_, v_f_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
    crate::leanh::lean_dec(v___y_4152_);
    crate::leanh::lean_dec_ref(v___y_4151_);
    crate::leanh::lean_dec(v___y_4150_);
    crate::leanh::lean_dec_ref(v___y_4149_);
    return v_res_4155_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: u8 = 0;
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = 1;
    v___x_4157_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2(
    mut v_msg_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v_toFunctor_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___f_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360__overap_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut v_unused_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4199_: u8 = 0;
    let mut v_unused_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4164_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0);
                v___x_4165_ = l_StateRefT_x27_instMonad___redArg(v___x_4164_);
                v_toApplicative_4166_ = crate::leanh::lean_ctor_get(v___x_4165_, 0);
                v_isSharedCheck_4199_ = (!crate::leanh::lean_is_exclusive(v___x_4165_)) as u8;
                if v_isSharedCheck_4199_ == 0 {
                    v_unused_4200_ = crate::leanh::lean_ctor_get(v___x_4165_, 1);
                    crate::leanh::lean_dec(v_unused_4200_);
                    v___x_4168_ = v___x_4165_;
                    v_isShared_4169_ = v_isSharedCheck_4199_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4166_);
                    crate::leanh::lean_dec(v___x_4165_);
                    v___x_4168_ = crate::leanh::lean_box(0);
                    v_isShared_4169_ = v_isSharedCheck_4199_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4170_ = crate::leanh::lean_ctor_get(v_toApplicative_4166_, 0);
                v_toSeq_4171_ = crate::leanh::lean_ctor_get(v_toApplicative_4166_, 2);
                v_toSeqLeft_4172_ = crate::leanh::lean_ctor_get(v_toApplicative_4166_, 3);
                v_toSeqRight_4173_ = crate::leanh::lean_ctor_get(v_toApplicative_4166_, 4);
                v_isSharedCheck_4197_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4166_)) as u8;
                if v_isSharedCheck_4197_ == 0 {
                    v_unused_4198_ = crate::leanh::lean_ctor_get(v_toApplicative_4166_, 1);
                    crate::leanh::lean_dec(v_unused_4198_);
                    v___x_4175_ = v_toApplicative_4166_;
                    v_isShared_4176_ = v_isSharedCheck_4197_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4173_);
                    crate::leanh::lean_inc(v_toSeqLeft_4172_);
                    crate::leanh::lean_inc(v_toSeq_4171_);
                    crate::leanh::lean_inc(v_toFunctor_4170_);
                    crate::leanh::lean_dec(v_toApplicative_4166_);
                    v___x_4175_ = crate::leanh::lean_box(0);
                    v_isShared_4176_ = v_isSharedCheck_4197_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4177_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1;
                v___f_4178_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_4170_);
                v___f_4179_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4179_, 0, v_toFunctor_4170_);
                v___f_4180_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4180_, 0, v_toFunctor_4170_);
                v___x_4181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4181_, 0, v___f_4179_);
                crate::leanh::lean_ctor_set(v___x_4181_, 1, v___f_4180_);
                v___f_4182_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4182_, 0, v_toSeqRight_4173_);
                v___f_4183_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4183_, 0, v_toSeqLeft_4172_);
                v___f_4184_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4184_, 0, v_toSeq_4171_);
                if v_isShared_4176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4175_, 4, v___f_4182_);
                    crate::leanh::lean_ctor_set(v___x_4175_, 3, v___f_4183_);
                    crate::leanh::lean_ctor_set(v___x_4175_, 2, v___f_4184_);
                    crate::leanh::lean_ctor_set(v___x_4175_, 1, v___f_4177_);
                    crate::leanh::lean_ctor_set(v___x_4175_, 0, v___x_4181_);
                    v___x_4186_ = v___x_4175_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4196_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4196_, 1, v___f_4177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4196_, 2, v___f_4184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4196_, 3, v___f_4183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4196_, 4, v___f_4182_);
                    v___x_4186_ = v_reuseFailAlloc_4196_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4169_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4168_, 1, v___f_4178_);
                    crate::leanh::lean_ctor_set(v___x_4168_, 0, v___x_4186_);
                    v___x_4188_ = v___x_4168_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4195_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4195_, 1, v___f_4178_);
                    v___x_4188_ = v_reuseFailAlloc_4195_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4189_ = l_StateRefT_x27_instMonad___redArg(v___x_4188_);
                v___x_4190_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0);
                v___x_4191_ = l_instInhabitedOfMonad___redArg(v___x_4189_, v___x_4190_);
                v___f_4192_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4192_, 0, v___x_4191_);
                v___x_3360__overap_4193_ = lean_panic_fn_borrowed(v___f_4192_, v_msg_4158_);
                crate::leanh::lean_dec_ref(v___f_4192_);
                crate::leanh::lean_inc(v___y_4162_);
                crate::leanh::lean_inc_ref(v___y_4161_);
                crate::leanh::lean_inc(v___y_4160_);
                crate::leanh::lean_inc_ref(v___y_4159_);
                v___x_4194_ = crate::leanh::lean_apply_5(
                    v___x_3360__overap_4193_,
                    v___y_4159_,
                    v___y_4160_,
                    v___y_4161_,
                    v___y_4162_,
                    crate::leanh::lean_box(0),
                );
                return v___x_4194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___boxed(
    mut v_msg_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2(v_msg_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
    crate::leanh::lean_dec(v___y_4205_);
    crate::leanh::lean_dec_ref(v___y_4204_);
    crate::leanh::lean_dec(v___y_4203_);
    crate::leanh::lean_dec_ref(v___y_4202_);
    return v_res_4207_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_4210_ = crate::leanh::lean_unsigned_to_nat(61);
    v___x_4211_ = crate::leanh::lean_unsigned_to_nat(167);
    v___x_4212_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__0;
    v___x_4213_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0;
    v___x_4214_ = l_mkPanicMessageWithDecl(
        v___x_4213_,
        v___x_4212_,
        v___x_4211_,
        v___x_4210_,
        v___x_4209_,
    );
    return v___x_4214_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(
    mut v_values_4215_: *mut crate::leanh::LeanObject,
    mut v_code_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v___x_4229_: usize = 0;
    let mut v___x_4230_: usize = 0;
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v_unused_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v_decl_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4264_: u8 = 0;
    let mut v___y_4266_: u8 = 0;
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4269_: u8 = 0;
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4276_: u8 = 0;
    let mut v_unused_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: usize = 0;
    let mut v___x_4284_: u8 = 0;
    let mut v___x_4285_: usize = 0;
    let mut v___x_4286_: usize = 0;
    let mut v___x_4287_: u8 = 0;
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_a_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut v_a_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4300_: u8 = 0;
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4304_: u8 = 0;
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4313_: u8 = 0;
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4320_: usize = 0;
    let mut v___x_4321_: usize = 0;
    let mut v___x_4322_: u8 = 0;
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4335_: u8 = 0;
    let mut v_unused_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut v_a_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4344_: u8 = 0;
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4348_: u8 = 0;
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v___x_4361_: usize = 0;
    let mut v___x_4362_: usize = 0;
    let mut v___x_4363_: u8 = 0;
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4373_: u8 = 0;
    let mut v_unused_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut v_fvarId_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4393_: usize = 0;
    let mut v___x_4394_: usize = 0;
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4405_: u8 = 0;
    let mut v_unused_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4415_: u8 = 0;
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_4216_) {
                0 => {
                    v_decl_4222_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                    v_k_4223_ = crate::leanh::lean_ctor_get(v_code_4216_, 1);
                    crate::leanh::lean_inc_ref(v_k_4223_);
                    v___x_4224_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_k_4223_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if crate::leanh::lean_obj_tag(v___x_4224_) == 0 {
                        v_a_4225_ = crate::leanh::lean_ctor_get(v___x_4224_, 0);
                        v_isSharedCheck_4247_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4224_)) as u8;
                        if v_isSharedCheck_4247_ == 0 {
                            v___x_4227_ = v___x_4224_;
                            v_isShared_4228_ = v_isSharedCheck_4247_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4225_);
                            crate::leanh::lean_dec(v___x_4224_);
                            v___x_4227_ = crate::leanh::lean_box(0);
                            v_isShared_4228_ = v_isSharedCheck_4247_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_4216_, 2);
                        return v___x_4224_;
                    }
                }
                2 => {
                    v_decl_4248_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                    v_k_4249_ = crate::leanh::lean_ctor_get(v_code_4216_, 1);
                    v_params_4250_ = crate::leanh::lean_ctor_get(v_decl_4248_, 2);
                    v_type_4251_ = crate::leanh::lean_ctor_get(v_decl_4248_, 3);
                    v_value_4252_ = crate::leanh::lean_ctor_get(v_decl_4248_, 4);
                    crate::leanh::lean_inc_ref(v_params_4250_);
                    v___x_4253_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams(v_values_4215_, v_params_4250_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if crate::leanh::lean_obj_tag(v___x_4253_) == 0 {
                        v_a_4254_ = crate::leanh::lean_ctor_get(v___x_4253_, 0);
                        crate::leanh::lean_inc(v_a_4254_);
                        crate::leanh::lean_dec_ref_known(v___x_4253_, 1);
                        crate::leanh::lean_inc_ref(v_value_4252_);
                        crate::leanh::lean_inc_ref(v_values_4215_);
                        v___x_4255_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_value_4252_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                        if crate::leanh::lean_obj_tag(v___x_4255_) == 0 {
                            v_a_4256_ = crate::leanh::lean_ctor_get(v___x_4255_, 0);
                            crate::leanh::lean_inc(v_a_4256_);
                            crate::leanh::lean_dec_ref_known(v___x_4255_, 1);
                            v___x_4257_ = 1;
                            crate::leanh::lean_inc_ref(v_type_4251_);
                            crate::leanh::lean_inc_ref(v_decl_4248_);
                            v___x_4258_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4257_, v_decl_4248_, v_type_4251_, v_a_4254_, v_a_4256_, v_a_4218_);
                            if crate::leanh::lean_obj_tag(v___x_4258_) == 0 {
                                v_a_4259_ = crate::leanh::lean_ctor_get(v___x_4258_, 0);
                                crate::leanh::lean_inc(v_a_4259_);
                                crate::leanh::lean_dec_ref_known(v___x_4258_, 1);
                                crate::leanh::lean_inc_ref(v_k_4249_);
                                v___x_4260_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_k_4249_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                                if crate::leanh::lean_obj_tag(v___x_4260_) == 0 {
                                    v_a_4261_ = crate::leanh::lean_ctor_get(v___x_4260_, 0);
                                    v_isSharedCheck_4288_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4260_)) as u8;
                                    if v_isSharedCheck_4288_ == 0 {
                                        v___x_4263_ = v___x_4260_;
                                        v_isShared_4264_ = v_isSharedCheck_4288_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4261_);
                                        crate::leanh::lean_dec(v___x_4260_);
                                        v___x_4263_ = crate::leanh::lean_box(0);
                                        v_isShared_4264_ = v_isSharedCheck_4288_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4259_);
                                    crate::leanh::lean_dec_ref_known(v_code_4216_, 2);
                                    return v___x_4260_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_code_4216_, 2);
                                crate::leanh::lean_dec_ref(v_values_4215_);
                                v_a_4289_ = crate::leanh::lean_ctor_get(v___x_4258_, 0);
                                v_isSharedCheck_4296_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4258_)) as u8;
                                if v_isSharedCheck_4296_ == 0 {
                                    v___x_4291_ = v___x_4258_;
                                    v_isShared_4292_ = v_isSharedCheck_4296_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4289_);
                                    crate::leanh::lean_dec(v___x_4258_);
                                    v___x_4291_ = crate::leanh::lean_box(0);
                                    v_isShared_4292_ = v_isSharedCheck_4296_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4254_);
                            crate::leanh::lean_dec_ref_known(v_code_4216_, 2);
                            crate::leanh::lean_dec_ref(v_values_4215_);
                            return v___x_4255_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_4216_, 2);
                        crate::leanh::lean_dec_ref(v_values_4215_);
                        v_a_4297_ = crate::leanh::lean_ctor_get(v___x_4253_, 0);
                        v_isSharedCheck_4304_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4253_)) as u8;
                        if v_isSharedCheck_4304_ == 0 {
                            v___x_4299_ = v___x_4253_;
                            v_isShared_4300_ = v_isSharedCheck_4304_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4297_);
                            crate::leanh::lean_dec(v___x_4253_);
                            v___x_4299_ = crate::leanh::lean_box(0);
                            v_isShared_4300_ = v_isSharedCheck_4304_;
                            state = 14;
                            continue;
                        }
                    }
                }
                3 => {
                    crate::leanh::lean_dec_ref(v_values_4215_);
                    v___x_4305_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4305_, 0, v_code_4216_);
                    return v___x_4305_;
                }
                4 => {
                    v_cases_4306_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                    crate::leanh::lean_inc_ref(v_cases_4306_);
                    v_typeName_4307_ = crate::leanh::lean_ctor_get(v_cases_4306_, 0);
                    v_resultType_4308_ = crate::leanh::lean_ctor_get(v_cases_4306_, 1);
                    v_discr_4309_ = crate::leanh::lean_ctor_get(v_cases_4306_, 2);
                    v_alts_4310_ = crate::leanh::lean_ctor_get(v_cases_4306_, 3);
                    v_isSharedCheck_4349_ = (!crate::leanh::lean_is_exclusive(v_cases_4306_)) as u8;
                    if v_isSharedCheck_4349_ == 0 {
                        v___x_4312_ = v_cases_4306_;
                        v_isShared_4313_ = v_isSharedCheck_4349_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_4310_);
                        crate::leanh::lean_inc(v_discr_4309_);
                        crate::leanh::lean_inc(v_resultType_4308_);
                        crate::leanh::lean_inc(v_typeName_4307_);
                        crate::leanh::lean_dec(v_cases_4306_);
                        v___x_4312_ = crate::leanh::lean_box(0);
                        v_isShared_4313_ = v_isSharedCheck_4349_;
                        state = 16;
                        continue;
                    }
                }
                5 => {
                    crate::leanh::lean_dec_ref(v_values_4215_);
                    v___x_4350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4350_, 0, v_code_4216_);
                    return v___x_4350_;
                }
                6 => {
                    crate::leanh::lean_dec_ref(v_values_4215_);
                    v___x_4351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4351_, 0, v_code_4216_);
                    return v___x_4351_;
                }
                8 => {
                    v_fvarId_4352_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                    v_i_4353_ = crate::leanh::lean_ctor_get(v_code_4216_, 1);
                    v_y_4354_ = crate::leanh::lean_ctor_get(v_code_4216_, 2);
                    v_k_4355_ = crate::leanh::lean_ctor_get(v_code_4216_, 3);
                    crate::leanh::lean_inc_ref(v_k_4355_);
                    v___x_4356_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_k_4355_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if crate::leanh::lean_obj_tag(v___x_4356_) == 0 {
                        v_a_4357_ = crate::leanh::lean_ctor_get(v___x_4356_, 0);
                        v_isSharedCheck_4381_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4356_)) as u8;
                        if v_isSharedCheck_4381_ == 0 {
                            v___x_4359_ = v___x_4356_;
                            v_isShared_4360_ = v_isSharedCheck_4381_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4357_);
                            crate::leanh::lean_dec(v___x_4356_);
                            v___x_4359_ = crate::leanh::lean_box(0);
                            v_isShared_4360_ = v_isSharedCheck_4381_;
                            state = 25;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_4216_, 4);
                        return v___x_4356_;
                    }
                }
                9 => {
                    v_fvarId_4382_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                    v_i_4383_ = crate::leanh::lean_ctor_get(v_code_4216_, 1);
                    v_offset_4384_ = crate::leanh::lean_ctor_get(v_code_4216_, 2);
                    v_y_4385_ = crate::leanh::lean_ctor_get(v_code_4216_, 3);
                    v_ty_4386_ = crate::leanh::lean_ctor_get(v_code_4216_, 4);
                    v_k_4387_ = crate::leanh::lean_ctor_get(v_code_4216_, 5);
                    crate::leanh::lean_inc_ref(v_k_4387_);
                    v___x_4388_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_k_4387_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if crate::leanh::lean_obj_tag(v___x_4388_) == 0 {
                        v_a_4389_ = crate::leanh::lean_ctor_get(v___x_4388_, 0);
                        v_isSharedCheck_4415_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4388_)) as u8;
                        if v_isSharedCheck_4415_ == 0 {
                            v___x_4391_ = v___x_4388_;
                            v_isShared_4392_ = v_isSharedCheck_4415_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4389_);
                            crate::leanh::lean_dec(v___x_4388_);
                            v___x_4391_ = crate::leanh::lean_box(0);
                            v_isShared_4392_ = v_isSharedCheck_4415_;
                            state = 30;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_4216_, 6);
                        return v___x_4388_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_code_4216_);
                    crate::leanh::lean_dec_ref(v_values_4215_);
                    v___x_4416_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1);
                    v___x_4417_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2(v___x_4416_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    return v___x_4417_;
                }
            },
            1 => {
                v___x_4229_ = lean_ptr_addr(v_k_4223_);
                v___x_4230_ = lean_ptr_addr(v_a_4225_);
                v___x_4231_ = lean_usize_dec_eq(v___x_4229_, v___x_4230_);
                if v___x_4231_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_4222_);
                    v_isSharedCheck_4241_ = (!crate::leanh::lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4241_ == 0 {
                        v_unused_4242_ = crate::leanh::lean_ctor_get(v_code_4216_, 1);
                        crate::leanh::lean_dec(v_unused_4242_);
                        v_unused_4243_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                        crate::leanh::lean_dec(v_unused_4243_);
                        v___x_4233_ = v_code_4216_;
                        v_isShared_4234_ = v_isSharedCheck_4241_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_4216_);
                        v___x_4233_ = crate::leanh::lean_box(0);
                        v_isShared_4234_ = v_isSharedCheck_4241_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4225_);
                    if v_isShared_4228_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4227_, 0, v_code_4216_);
                        v___x_4245_ = v___x_4227_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_code_4216_);
                        v___x_4245_ = v_reuseFailAlloc_4246_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4233_, 1, v_a_4225_);
                    v___x_4236_ = v___x_4233_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_decl_4222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_a_4225_);
                    v___x_4236_ = v_reuseFailAlloc_4240_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4228_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4236_);
                    v___x_4238_ = v___x_4227_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4236_);
                    v___x_4238_ = v_reuseFailAlloc_4239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4238_;
            }
            5 => {
                return v___x_4245_;
            }
            6 => {
                v___x_4282_ = lean_ptr_addr(v_k_4249_);
                v___x_4283_ = lean_ptr_addr(v_a_4261_);
                v___x_4284_ = lean_usize_dec_eq(v___x_4282_, v___x_4283_);
                if v___x_4284_ == 0 {
                    v___y_4266_ = v___x_4284_;
                    state = 7;
                    continue;
                } else {
                    v___x_4285_ = lean_ptr_addr(v_decl_4248_);
                    v___x_4286_ = lean_ptr_addr(v_a_4259_);
                    v___x_4287_ = lean_usize_dec_eq(v___x_4285_, v___x_4286_);
                    v___y_4266_ = v___x_4287_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_4266_ == 0 {
                    v_isSharedCheck_4276_ = (!crate::leanh::lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4276_ == 0 {
                        v_unused_4277_ = crate::leanh::lean_ctor_get(v_code_4216_, 1);
                        crate::leanh::lean_dec(v_unused_4277_);
                        v_unused_4278_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                        crate::leanh::lean_dec(v_unused_4278_);
                        v___x_4268_ = v_code_4216_;
                        v_isShared_4269_ = v_isSharedCheck_4276_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_4216_);
                        v___x_4268_ = crate::leanh::lean_box(0);
                        v_isShared_4269_ = v_isSharedCheck_4276_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4261_);
                    crate::leanh::lean_dec(v_a_4259_);
                    if v_isShared_4264_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4263_, 0, v_code_4216_);
                        v___x_4280_ = v___x_4263_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4281_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_code_4216_);
                        v___x_4280_ = v_reuseFailAlloc_4281_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4269_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4268_, 1, v_a_4261_);
                    crate::leanh::lean_ctor_set(v___x_4268_, 0, v_a_4259_);
                    v___x_4271_ = v___x_4268_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4275_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4275_, 1, v_a_4261_);
                    v___x_4271_ = v_reuseFailAlloc_4275_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4264_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4263_, 0, v___x_4271_);
                    v___x_4273_ = v___x_4263_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
                    v___x_4273_ = v_reuseFailAlloc_4274_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4273_;
            }
            11 => {
                return v___x_4280_;
            }
            12 => {
                if v_isShared_4292_ == 0 {
                    v___x_4294_ = v___x_4291_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
                    v___x_4294_ = v_reuseFailAlloc_4295_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4294_;
            }
            14 => {
                if v_isShared_4300_ == 0 {
                    v___x_4302_ = v___x_4299_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
                    v___x_4302_ = v_reuseFailAlloc_4303_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4302_;
            }
            16 => {
                v___x_4314_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_4310_);
                v___x_4315_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__1(v_values_4215_, v___x_4314_, v_alts_4310_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                if crate::leanh::lean_obj_tag(v___x_4315_) == 0 {
                    v_a_4316_ = crate::leanh::lean_ctor_get(v___x_4315_, 0);
                    v_isSharedCheck_4340_ = (!crate::leanh::lean_is_exclusive(v___x_4315_)) as u8;
                    if v_isSharedCheck_4340_ == 0 {
                        v___x_4318_ = v___x_4315_;
                        v_isShared_4319_ = v_isSharedCheck_4340_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4316_);
                        crate::leanh::lean_dec(v___x_4315_);
                        v___x_4318_ = crate::leanh::lean_box(0);
                        v_isShared_4319_ = v_isSharedCheck_4340_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4312_);
                    crate::leanh::lean_dec_ref(v_alts_4310_);
                    crate::leanh::lean_dec(v_discr_4309_);
                    crate::leanh::lean_dec_ref(v_resultType_4308_);
                    crate::leanh::lean_dec(v_typeName_4307_);
                    crate::leanh::lean_dec_ref_known(v_code_4216_, 1);
                    v_a_4341_ = crate::leanh::lean_ctor_get(v___x_4315_, 0);
                    v_isSharedCheck_4348_ = (!crate::leanh::lean_is_exclusive(v___x_4315_)) as u8;
                    if v_isSharedCheck_4348_ == 0 {
                        v___x_4343_ = v___x_4315_;
                        v_isShared_4344_ = v_isSharedCheck_4348_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4341_);
                        crate::leanh::lean_dec(v___x_4315_);
                        v___x_4343_ = crate::leanh::lean_box(0);
                        v_isShared_4344_ = v_isSharedCheck_4348_;
                        state = 23;
                        continue;
                    }
                }
            }
            17 => {
                v___x_4320_ = lean_ptr_addr(v_alts_4310_);
                crate::leanh::lean_dec_ref(v_alts_4310_);
                v___x_4321_ = lean_ptr_addr(v_a_4316_);
                v___x_4322_ = lean_usize_dec_eq(v___x_4320_, v___x_4321_);
                if v___x_4322_ == 0 {
                    v_isSharedCheck_4335_ = (!crate::leanh::lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4335_ == 0 {
                        v_unused_4336_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                        crate::leanh::lean_dec(v_unused_4336_);
                        v___x_4324_ = v_code_4216_;
                        v_isShared_4325_ = v_isSharedCheck_4335_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_4216_);
                        v___x_4324_ = crate::leanh::lean_box(0);
                        v_isShared_4325_ = v_isSharedCheck_4335_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4316_);
                    crate::leanh::lean_del_object(v___x_4312_);
                    crate::leanh::lean_dec(v_discr_4309_);
                    crate::leanh::lean_dec_ref(v_resultType_4308_);
                    crate::leanh::lean_dec(v_typeName_4307_);
                    if v_isShared_4319_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4318_, 0, v_code_4216_);
                        v___x_4338_ = v___x_4318_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_4339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_code_4216_);
                        v___x_4338_ = v_reuseFailAlloc_4339_;
                        state = 22;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4312_, 3, v_a_4316_);
                    v___x_4327_ = v___x_4312_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4334_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_typeName_4307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_resultType_4308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 2, v_discr_4309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 3, v_a_4316_);
                    v___x_4327_ = v_reuseFailAlloc_4334_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4325_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4324_, 0, v___x_4327_);
                    v___x_4329_ = v___x_4324_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4333_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4327_);
                    v___x_4329_ = v_reuseFailAlloc_4333_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_4319_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4318_, 0, v___x_4329_);
                    v___x_4331_ = v___x_4318_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
                    v___x_4331_ = v_reuseFailAlloc_4332_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4331_;
            }
            22 => {
                return v___x_4338_;
            }
            23 => {
                if v_isShared_4344_ == 0 {
                    v___x_4346_ = v___x_4343_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
                    v___x_4346_ = v_reuseFailAlloc_4347_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4346_;
            }
            25 => {
                v___x_4361_ = lean_ptr_addr(v_k_4355_);
                v___x_4362_ = lean_ptr_addr(v_a_4357_);
                v___x_4363_ = lean_usize_dec_eq(v___x_4361_, v___x_4362_);
                if v___x_4363_ == 0 {
                    crate::leanh::lean_inc(v_y_4354_);
                    crate::leanh::lean_inc(v_i_4353_);
                    crate::leanh::lean_inc(v_fvarId_4352_);
                    v_isSharedCheck_4373_ = (!crate::leanh::lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4373_ == 0 {
                        v_unused_4374_ = crate::leanh::lean_ctor_get(v_code_4216_, 3);
                        crate::leanh::lean_dec(v_unused_4374_);
                        v_unused_4375_ = crate::leanh::lean_ctor_get(v_code_4216_, 2);
                        crate::leanh::lean_dec(v_unused_4375_);
                        v_unused_4376_ = crate::leanh::lean_ctor_get(v_code_4216_, 1);
                        crate::leanh::lean_dec(v_unused_4376_);
                        v_unused_4377_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                        crate::leanh::lean_dec(v_unused_4377_);
                        v___x_4365_ = v_code_4216_;
                        v_isShared_4366_ = v_isSharedCheck_4373_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_4216_);
                        v___x_4365_ = crate::leanh::lean_box(0);
                        v_isShared_4366_ = v_isSharedCheck_4373_;
                        state = 26;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4357_);
                    if v_isShared_4360_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4359_, 0, v_code_4216_);
                        v___x_4379_ = v___x_4359_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_4380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_code_4216_);
                        v___x_4379_ = v_reuseFailAlloc_4380_;
                        state = 29;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_4366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4365_, 3, v_a_4357_);
                    v___x_4368_ = v___x_4365_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4372_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_fvarId_4352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4372_, 1, v_i_4353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4372_, 2, v_y_4354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4372_, 3, v_a_4357_);
                    v___x_4368_ = v_reuseFailAlloc_4372_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_4360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4359_, 0, v___x_4368_);
                    v___x_4370_ = v___x_4359_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
                    v___x_4370_ = v_reuseFailAlloc_4371_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4370_;
            }
            29 => {
                return v___x_4379_;
            }
            30 => {
                v___x_4393_ = lean_ptr_addr(v_k_4387_);
                v___x_4394_ = lean_ptr_addr(v_a_4389_);
                v___x_4395_ = lean_usize_dec_eq(v___x_4393_, v___x_4394_);
                if v___x_4395_ == 0 {
                    crate::leanh::lean_inc_ref(v_ty_4386_);
                    crate::leanh::lean_inc(v_y_4385_);
                    crate::leanh::lean_inc(v_offset_4384_);
                    crate::leanh::lean_inc(v_i_4383_);
                    crate::leanh::lean_inc(v_fvarId_4382_);
                    v_isSharedCheck_4405_ = (!crate::leanh::lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4405_ == 0 {
                        v_unused_4406_ = crate::leanh::lean_ctor_get(v_code_4216_, 5);
                        crate::leanh::lean_dec(v_unused_4406_);
                        v_unused_4407_ = crate::leanh::lean_ctor_get(v_code_4216_, 4);
                        crate::leanh::lean_dec(v_unused_4407_);
                        v_unused_4408_ = crate::leanh::lean_ctor_get(v_code_4216_, 3);
                        crate::leanh::lean_dec(v_unused_4408_);
                        v_unused_4409_ = crate::leanh::lean_ctor_get(v_code_4216_, 2);
                        crate::leanh::lean_dec(v_unused_4409_);
                        v_unused_4410_ = crate::leanh::lean_ctor_get(v_code_4216_, 1);
                        crate::leanh::lean_dec(v_unused_4410_);
                        v_unused_4411_ = crate::leanh::lean_ctor_get(v_code_4216_, 0);
                        crate::leanh::lean_dec(v_unused_4411_);
                        v___x_4397_ = v_code_4216_;
                        v_isShared_4398_ = v_isSharedCheck_4405_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_4216_);
                        v___x_4397_ = crate::leanh::lean_box(0);
                        v_isShared_4398_ = v_isSharedCheck_4405_;
                        state = 31;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4389_);
                    if v_isShared_4392_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4391_, 0, v_code_4216_);
                        v___x_4413_ = v___x_4391_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_4414_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_code_4216_);
                        v___x_4413_ = v_reuseFailAlloc_4414_;
                        state = 34;
                        continue;
                    }
                }
            }
            31 => {
                if v_isShared_4398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4397_, 5, v_a_4389_);
                    v___x_4400_ = v___x_4397_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4404_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_fvarId_4382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_i_4383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_offset_4384_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 3, v_y_4385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 4, v_ty_4386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 5, v_a_4389_);
                    v___x_4400_ = v_reuseFailAlloc_4404_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_4392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4391_, 0, v___x_4400_);
                    v___x_4402_ = v___x_4391_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
                    v___x_4402_ = v_reuseFailAlloc_4403_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4402_;
            }
            34 => {
                return v___x_4413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___boxed(
    mut v_values_4418_: *mut crate::leanh::LeanObject,
    mut v_code_4419_: *mut crate::leanh::LeanObject,
    mut v_a_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4425_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4418_, v_code_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_);
    crate::leanh::lean_dec(v_a_4423_);
    crate::leanh::lean_dec_ref(v_a_4422_);
    crate::leanh::lean_dec(v_a_4421_);
    crate::leanh::lean_dec_ref(v_a_4420_);
    return v_res_4425_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__1(
    mut v_values_4426_: *mut crate::leanh::LeanObject,
    mut v_i_4427_: *mut crate::leanh::LeanObject,
    mut v_as_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: u8 = 0;
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: usize = 0;
    let mut v___x_4442_: usize = 0;
    let mut v___x_4443_: u8 = 0;
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4434_ = lean_array_get_size(v_as_4428_);
                v___x_4435_ = lean_nat_dec_lt(v_i_4427_, v___x_4434_);
                if v___x_4435_ == 0 {
                    crate::leanh::lean_dec(v_i_4427_);
                    crate::leanh::lean_dec_ref(v_values_4426_);
                    v___x_4436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4436_, 0, v_as_4428_);
                    return v___x_4436_;
                } else {
                    v_a_4437_ = lean_array_fget_borrowed(v_as_4428_, v_i_4427_);
                    crate::leanh::lean_inc_ref(v_values_4426_);
                    v___x_4438_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___x_4438_, 0, v_values_4426_);
                    crate::leanh::lean_inc(v_a_4437_);
                    v___x_4439_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg(v_a_4437_, v___x_4438_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
                    if crate::leanh::lean_obj_tag(v___x_4439_) == 0 {
                        v_a_4440_ = crate::leanh::lean_ctor_get(v___x_4439_, 0);
                        crate::leanh::lean_inc(v_a_4440_);
                        crate::leanh::lean_dec_ref_known(v___x_4439_, 1);
                        v___x_4441_ = lean_ptr_addr(v_a_4437_);
                        v___x_4442_ = lean_ptr_addr(v_a_4440_);
                        v___x_4443_ = lean_usize_dec_eq(v___x_4441_, v___x_4442_);
                        if v___x_4443_ == 0 {
                            v___x_4444_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4445_ = lean_nat_add(v_i_4427_, v___x_4444_);
                            v___x_4446_ = lean_array_fset(v_as_4428_, v_i_4427_, v_a_4440_);
                            crate::leanh::lean_dec(v_i_4427_);
                            v_i_4427_ = v___x_4445_;
                            v_as_4428_ = v___x_4446_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4440_);
                            v___x_4448_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4449_ = lean_nat_add(v_i_4427_, v___x_4448_);
                            crate::leanh::lean_dec(v_i_4427_);
                            v_i_4427_ = v___x_4449_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_as_4428_);
                        crate::leanh::lean_dec(v_i_4427_);
                        crate::leanh::lean_dec_ref(v_values_4426_);
                        v_a_4451_ = crate::leanh::lean_ctor_get(v___x_4439_, 0);
                        v_isSharedCheck_4458_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4439_)) as u8;
                        if v_isSharedCheck_4458_ == 0 {
                            v___x_4453_ = v___x_4439_;
                            v_isShared_4454_ = v_isSharedCheck_4458_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4451_);
                            crate::leanh::lean_dec(v___x_4439_);
                            v___x_4453_ = crate::leanh::lean_box(0);
                            v_isShared_4454_ = v_isSharedCheck_4458_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4454_ == 0 {
                    v___x_4456_ = v___x_4453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
                    v___x_4456_ = v_reuseFailAlloc_4457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__1___boxed(
    mut v_values_4459_: *mut crate::leanh::LeanObject,
    mut v_i_4460_: *mut crate::leanh::LeanObject,
    mut v_as_4461_: *mut crate::leanh::LeanObject,
    mut v___y_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
    mut v___y_4465_: *mut crate::leanh::LeanObject,
    mut v___y_4466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4467_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__1(v_values_4459_, v_i_4460_, v_as_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
    crate::leanh::lean_dec(v___y_4465_);
    crate::leanh::lean_dec_ref(v___y_4464_);
    crate::leanh::lean_dec(v___y_4463_);
    crate::leanh::lean_dec_ref(v___y_4462_);
    return v_res_4467_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_applyOwnedness(
    mut v_decl_4468_: *mut crate::leanh::LeanObject,
    mut v_values_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
    mut v_a_4473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_value_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_4477_: u8 = 0;
    let mut v_inlineAttr_x3f_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v_code_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4485_: u8 = 0;
    let mut v_name_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_4490_: u8 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_a_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4521_: u8 = 0;
    let mut v_a_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v_unused_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_4475_ = crate::leanh::lean_ctor_get(v_decl_4468_, 1);
                crate::leanh::lean_inc_ref(v_value_4475_);
                if crate::leanh::lean_obj_tag(v_value_4475_) == 0 {
                    v_toSignature_4476_ = crate::leanh::lean_ctor_get(v_decl_4468_, 0);
                    v_recursive_4477_ = crate::leanh::lean_ctor_get_uint8(
                        v_decl_4468_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_4478_ = crate::leanh::lean_ctor_get(v_decl_4468_, 2);
                    v_isSharedCheck_4532_ = (!crate::leanh::lean_is_exclusive(v_decl_4468_)) as u8;
                    if v_isSharedCheck_4532_ == 0 {
                        v_unused_4533_ = crate::leanh::lean_ctor_get(v_decl_4468_, 1);
                        crate::leanh::lean_dec(v_unused_4533_);
                        v___x_4480_ = v_decl_4468_;
                        v_isShared_4481_ = v_isSharedCheck_4532_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_inlineAttr_x3f_4478_);
                        crate::leanh::lean_inc(v_toSignature_4476_);
                        crate::leanh::lean_dec(v_decl_4468_);
                        v___x_4480_ = crate::leanh::lean_box(0);
                        v_isShared_4481_ = v_isSharedCheck_4532_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_4475_);
                    crate::leanh::lean_dec_ref(v_values_4469_);
                    v___x_4534_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4534_, 0, v_decl_4468_);
                    return v___x_4534_;
                }
            }
            1 => {
                v_code_4482_ = crate::leanh::lean_ctor_get(v_value_4475_, 0);
                v_isSharedCheck_4531_ = (!crate::leanh::lean_is_exclusive(v_value_4475_)) as u8;
                if v_isSharedCheck_4531_ == 0 {
                    v___x_4484_ = v_value_4475_;
                    v_isShared_4485_ = v_isSharedCheck_4531_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_code_4482_);
                    crate::leanh::lean_dec(v_value_4475_);
                    v___x_4484_ = crate::leanh::lean_box(0);
                    v_isShared_4485_ = v_isSharedCheck_4531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_name_4486_ = crate::leanh::lean_ctor_get(v_toSignature_4476_, 0);
                v_levelParams_4487_ = crate::leanh::lean_ctor_get(v_toSignature_4476_, 1);
                v_type_4488_ = crate::leanh::lean_ctor_get(v_toSignature_4476_, 2);
                v_params_4489_ = crate::leanh::lean_ctor_get(v_toSignature_4476_, 3);
                v_safe_4490_ = crate::leanh::lean_ctor_get_uint8(
                    v_toSignature_4476_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_4530_ =
                    (!crate::leanh::lean_is_exclusive(v_toSignature_4476_)) as u8;
                if v_isSharedCheck_4530_ == 0 {
                    v___x_4492_ = v_toSignature_4476_;
                    v_isShared_4493_ = v_isSharedCheck_4530_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_4489_);
                    crate::leanh::lean_inc(v_type_4488_);
                    crate::leanh::lean_inc(v_levelParams_4487_);
                    crate::leanh::lean_inc(v_name_4486_);
                    crate::leanh::lean_dec(v_toSignature_4476_);
                    v___x_4492_ = crate::leanh::lean_box(0);
                    v_isShared_4493_ = v_isSharedCheck_4530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4494_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams(v_values_4469_, v_params_4489_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_);
                if crate::leanh::lean_obj_tag(v___x_4494_) == 0 {
                    v_a_4495_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
                    crate::leanh::lean_inc(v_a_4495_);
                    crate::leanh::lean_dec_ref_known(v___x_4494_, 1);
                    v___x_4496_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4469_, v_code_4482_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_);
                    if crate::leanh::lean_obj_tag(v___x_4496_) == 0 {
                        v_a_4497_ = crate::leanh::lean_ctor_get(v___x_4496_, 0);
                        v_isSharedCheck_4513_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4496_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v___x_4499_ = v___x_4496_;
                            v_isShared_4500_ = v_isSharedCheck_4513_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4497_);
                            crate::leanh::lean_dec(v___x_4496_);
                            v___x_4499_ = crate::leanh::lean_box(0);
                            v_isShared_4500_ = v_isSharedCheck_4513_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4495_);
                        crate::leanh::lean_del_object(v___x_4492_);
                        crate::leanh::lean_dec_ref(v_type_4488_);
                        crate::leanh::lean_dec(v_levelParams_4487_);
                        crate::leanh::lean_dec(v_name_4486_);
                        crate::leanh::lean_del_object(v___x_4484_);
                        crate::leanh::lean_del_object(v___x_4480_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_4478_);
                        v_a_4514_ = crate::leanh::lean_ctor_get(v___x_4496_, 0);
                        v_isSharedCheck_4521_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4496_)) as u8;
                        if v_isSharedCheck_4521_ == 0 {
                            v___x_4516_ = v___x_4496_;
                            v_isShared_4517_ = v_isSharedCheck_4521_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4514_);
                            crate::leanh::lean_dec(v___x_4496_);
                            v___x_4516_ = crate::leanh::lean_box(0);
                            v_isShared_4517_ = v_isSharedCheck_4521_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4492_);
                    crate::leanh::lean_dec_ref(v_type_4488_);
                    crate::leanh::lean_dec(v_levelParams_4487_);
                    crate::leanh::lean_dec(v_name_4486_);
                    crate::leanh::lean_del_object(v___x_4484_);
                    crate::leanh::lean_dec_ref(v_code_4482_);
                    crate::leanh::lean_del_object(v___x_4480_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_4478_);
                    crate::leanh::lean_dec_ref(v_values_4469_);
                    v_a_4522_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
                    v_isSharedCheck_4529_ = (!crate::leanh::lean_is_exclusive(v___x_4494_)) as u8;
                    if v_isSharedCheck_4529_ == 0 {
                        v___x_4524_ = v___x_4494_;
                        v_isShared_4525_ = v_isSharedCheck_4529_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4522_);
                        crate::leanh::lean_dec(v___x_4494_);
                        v___x_4524_ = crate::leanh::lean_box(0);
                        v_isShared_4525_ = v_isSharedCheck_4529_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4492_, 3, v_a_4495_);
                    v___x_4502_ = v___x_4492_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_name_4486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_levelParams_4487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 2, v_type_4488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 3, v_a_4495_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4512_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_safe_4490_,
                    );
                    v___x_4502_ = v_reuseFailAlloc_4512_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4485_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4484_, 0, v_a_4497_);
                    v___x_4504_ = v___x_4484_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4497_);
                    v___x_4504_ = v_reuseFailAlloc_4511_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4480_, 1, v___x_4504_);
                    crate::leanh::lean_ctor_set(v___x_4480_, 0, v___x_4502_);
                    v___x_4506_ = v___x_4480_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4510_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 1, v___x_4504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 2, v_inlineAttr_x3f_4478_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4510_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_4477_,
                    );
                    v___x_4506_ = v_reuseFailAlloc_4510_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4499_, 0, v___x_4506_);
                    v___x_4508_ = v___x_4499_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4508_;
            }
            9 => {
                if v_isShared_4517_ == 0 {
                    v___x_4519_ = v___x_4516_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
                    v___x_4519_ = v_reuseFailAlloc_4520_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4519_;
            }
            11 => {
                if v_isShared_4525_ == 0 {
                    v___x_4527_ = v___x_4524_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
                    v___x_4527_ = v_reuseFailAlloc_4528_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_applyOwnedness___boxed(
    mut v_decl_4535_: *mut crate::leanh::LeanObject,
    mut v_values_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(
        v_decl_4535_,
        v_values_4536_,
        v_a_4537_,
        v_a_4538_,
        v_a_4539_,
        v_a_4540_,
    );
    crate::leanh::lean_dec(v_a_4540_);
    crate::leanh::lean_dec_ref(v_a_4539_);
    crate::leanh::lean_dec(v_a_4538_);
    crate::leanh::lean_dec_ref(v_a_4537_);
    return v_res_4542_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedOwnedness_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedOwnedness_default();
    l_Lean_Compiler_LCNF_instInhabitedOwnedness =
        _init_l_Lean_Compiler_LCNF_instInhabitedOwnedness();
    l_Lean_Compiler_LCNF_instInhabitedState_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedState_default);
    l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState = _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PropagateBorrow(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_PropagateBorrow(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
}
