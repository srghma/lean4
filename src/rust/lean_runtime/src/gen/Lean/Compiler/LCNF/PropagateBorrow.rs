// Lean compiler output
// Module: Lean.Compiler.LCNF.PropagateBorrow
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PhaseExt
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
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static mut l_Lean_Compiler_LCNF_instInhabitedOwnedness_default: u8 = 0;
pub static mut l_Lean_Compiler_LCNF_instInhabitedOwnedness: u8 = 0;
pub static l_Lean_Compiler_LCNF_instBEqOwnedness___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instBEqOwnedness_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instBEqOwnedness___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instBEqOwnedness___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instBEqOwnedness: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instBEqOwnedness___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__1_value: LeanStringObject<105> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 105, m_capacity: 105, m_length: 104, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 97, 110, 97, 108, 121, 122, 101, 80, 114, 111, 112, 97, 103, 97, 116, 101, 100, 66, 111, 114, 114, 111, 119, 115, 46, 103, 101, 116, 80, 97, 114, 97, 109, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [103, 101, 116, 73, 110, 116, 101, 114, 110, 97, 108, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [103, 101, 116, 33, 73, 110, 116, 101, 114, 110, 97, 108, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 103, 101, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__4_value: LeanStringObject<111> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 111, m_capacity: 111, m_length: 110, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 97, 110, 97, 108, 121, 122, 101, 80, 114, 111, 112, 97, 103, 97, 116, 101, 100, 66, 111, 114, 114, 111, 119, 115, 46, 99, 111, 108, 108, 101, 99, 116, 76, 101, 116, 86, 97, 108, 117, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__0_value: LeanStringObject<107> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 107, m_capacity: 107, m_length: 106, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 97, 110, 97, 108, 121, 122, 101, 80, 114, 111, 112, 97, 103, 97, 116, 101, 100, 66, 111, 114, 114, 111, 119, 115, 46, 99, 111, 108, 108, 101, 99, 116, 67, 111, 100, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__1_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__0_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__0_value: LeanStringObject<92> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 66, 111, 114, 114, 111, 119, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 97, 112, 112, 108, 121, 79, 119, 110, 101, 100, 110, 101, 115, 115, 46, 103, 111, 67, 111, 100, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorIdx(mut v_x_2272_: u8) -> *mut LeanObject {
    match v_x_2272_ {
        0 => {
            let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
            v___x_2273_ = lean_unsigned_to_nat(0);
            return v___x_2273_;
        }
        1 => {
            let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
            v___x_2274_ = lean_unsigned_to_nat(1);
            return v___x_2274_;
        }
        2 => {
            let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
            v___x_2275_ = lean_unsigned_to_nat(2);
            return v___x_2275_;
        }
        _ => {
            let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
            v___x_2276_ = lean_unsigned_to_nat(3);
            return v___x_2276_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorIdx___boxed(
    mut v_x_2277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2278_: u8 = 0;
    let mut v_res_2279_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2278_ = (lean_unbox(v_x_2277_) as u8);
    v_res_2279_ = l_Lean_Compiler_LCNF_Ownedness_ctorIdx(v_x_boxed_2278_);
    return v_res_2279_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_toCtorIdx(mut v_x_2280_: u8) -> *mut LeanObject {
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_Lean_Compiler_LCNF_Ownedness_ctorIdx(v_x_2280_);
    return v___x_2281_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_toCtorIdx___boxed(
    mut v_x_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_2283_: u8 = 0;
    let mut v_res_2284_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2283_ = (lean_unbox(v_x_2282_) as u8);
    v_res_2284_ = l_Lean_Compiler_LCNF_Ownedness_toCtorIdx(v_x_4__boxed_2283_);
    return v_res_2284_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorElim___redArg(
    mut v_k_2285_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2285_);
    return v_k_2285_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorElim___redArg___boxed(
    mut v_k_2286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2287_: *mut LeanObject = core::ptr::null_mut();
    v_res_2287_ = l_Lean_Compiler_LCNF_Ownedness_ctorElim___redArg(v_k_2286_);
    lean_dec(v_k_2286_);
    return v_res_2287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorElim(
    mut v_motive_2288_: *mut LeanObject,
    mut v_ctorIdx_2289_: *mut LeanObject,
    mut v_t_2290_: u8,
    mut v_h_2291_: *mut LeanObject,
    mut v_k_2292_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2292_);
    return v_k_2292_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_ctorElim___boxed(
    mut v_motive_2293_: *mut LeanObject,
    mut v_ctorIdx_2294_: *mut LeanObject,
    mut v_t_2295_: *mut LeanObject,
    mut v_h_2296_: *mut LeanObject,
    mut v_k_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2298_: u8 = 0;
    let mut v_res_2299_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2298_ = (lean_unbox(v_t_2295_) as u8);
    v_res_2299_ = l_Lean_Compiler_LCNF_Ownedness_ctorElim(
        v_motive_2293_,
        v_ctorIdx_2294_,
        v_t_boxed_2298_,
        v_h_2296_,
        v_k_2297_,
    );
    lean_dec(v_k_2297_);
    lean_dec(v_ctorIdx_2294_);
    return v_res_2299_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_bot_elim___redArg(
    mut v_bot_2300_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_bot_2300_);
    return v_bot_2300_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_bot_elim___redArg___boxed(
    mut v_bot_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2302_: *mut LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Lean_Compiler_LCNF_Ownedness_bot_elim___redArg(v_bot_2301_);
    lean_dec(v_bot_2301_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_bot_elim(
    mut v_motive_2303_: *mut LeanObject,
    mut v_t_2304_: u8,
    mut v_h_2305_: *mut LeanObject,
    mut v_bot_2306_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_bot_2306_);
    return v_bot_2306_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_bot_elim___boxed(
    mut v_motive_2307_: *mut LeanObject,
    mut v_t_2308_: *mut LeanObject,
    mut v_h_2309_: *mut LeanObject,
    mut v_bot_2310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2311_: u8 = 0;
    let mut v_res_2312_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2311_ = (lean_unbox(v_t_2308_) as u8);
    v_res_2312_ = l_Lean_Compiler_LCNF_Ownedness_bot_elim(
        v_motive_2307_,
        v_t_boxed_2311_,
        v_h_2309_,
        v_bot_2310_,
    );
    lean_dec(v_bot_2310_);
    return v_res_2312_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_borrow_elim___redArg(
    mut v_borrow_2313_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_borrow_2313_);
    return v_borrow_2313_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_borrow_elim___redArg___boxed(
    mut v_borrow_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2315_: *mut LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Lean_Compiler_LCNF_Ownedness_borrow_elim___redArg(v_borrow_2314_);
    lean_dec(v_borrow_2314_);
    return v_res_2315_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_borrow_elim(
    mut v_motive_2316_: *mut LeanObject,
    mut v_t_2317_: u8,
    mut v_h_2318_: *mut LeanObject,
    mut v_borrow_2319_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_borrow_2319_);
    return v_borrow_2319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_borrow_elim___boxed(
    mut v_motive_2320_: *mut LeanObject,
    mut v_t_2321_: *mut LeanObject,
    mut v_h_2322_: *mut LeanObject,
    mut v_borrow_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2324_: u8 = 0;
    let mut v_res_2325_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2324_ = (lean_unbox(v_t_2321_) as u8);
    v_res_2325_ = l_Lean_Compiler_LCNF_Ownedness_borrow_elim(
        v_motive_2320_,
        v_t_boxed_2324_,
        v_h_2322_,
        v_borrow_2323_,
    );
    lean_dec(v_borrow_2323_);
    return v_res_2325_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_own_elim___redArg(
    mut v_own_2326_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_own_2326_);
    return v_own_2326_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_own_elim___redArg___boxed(
    mut v_own_2327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2328_: *mut LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_Compiler_LCNF_Ownedness_own_elim___redArg(v_own_2327_);
    lean_dec(v_own_2327_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_own_elim(
    mut v_motive_2329_: *mut LeanObject,
    mut v_t_2330_: u8,
    mut v_h_2331_: *mut LeanObject,
    mut v_own_2332_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_own_2332_);
    return v_own_2332_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_own_elim___boxed(
    mut v_motive_2333_: *mut LeanObject,
    mut v_t_2334_: *mut LeanObject,
    mut v_h_2335_: *mut LeanObject,
    mut v_own_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2337_: u8 = 0;
    let mut v_res_2338_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2337_ = (lean_unbox(v_t_2334_) as u8);
    v_res_2338_ = l_Lean_Compiler_LCNF_Ownedness_own_elim(
        v_motive_2333_,
        v_t_boxed_2337_,
        v_h_2335_,
        v_own_2336_,
    );
    lean_dec(v_own_2336_);
    return v_res_2338_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_top_elim___redArg(
    mut v_top_2339_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_top_2339_);
    return v_top_2339_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_top_elim___redArg___boxed(
    mut v_top_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2341_: *mut LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Lean_Compiler_LCNF_Ownedness_top_elim___redArg(v_top_2340_);
    lean_dec(v_top_2340_);
    return v_res_2341_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_top_elim(
    mut v_motive_2342_: *mut LeanObject,
    mut v_t_2343_: u8,
    mut v_h_2344_: *mut LeanObject,
    mut v_top_2345_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_top_2345_);
    return v_top_2345_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Ownedness_top_elim___boxed(
    mut v_motive_2346_: *mut LeanObject,
    mut v_t_2347_: *mut LeanObject,
    mut v_h_2348_: *mut LeanObject,
    mut v_top_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2350_: u8 = 0;
    let mut v_res_2351_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2350_ = (lean_unbox(v_t_2347_) as u8);
    v_res_2351_ = l_Lean_Compiler_LCNF_Ownedness_top_elim(
        v_motive_2346_,
        v_t_boxed_2350_,
        v_h_2348_,
        v_top_2349_,
    );
    lean_dec(v_top_2349_);
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
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u8 = 0;
    v___x_2356_ = l_Lean_Compiler_LCNF_Ownedness_ctorIdx(v_x_2354_);
    v___x_2357_ = l_Lean_Compiler_LCNF_Ownedness_ctorIdx(v_y_2355_);
    v___x_2358_ = lean_nat_dec_eq(v___x_2356_, v___x_2357_);
    lean_dec(v___x_2357_);
    lean_dec(v___x_2356_);
    return v___x_2358_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instBEqOwnedness_beq___boxed(
    mut v_x_2359_: *mut LeanObject,
    mut v_y_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_2361_: u8 = 0;
    let mut v_y_18__boxed_2362_: u8 = 0;
    let mut v_res_2363_: u8 = 0;
    let mut v_r_2364_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2361_ = (lean_unbox(v_x_2359_) as u8);
    v_y_18__boxed_2362_ = (lean_unbox(v_y_2360_) as u8);
    v_res_2363_ =
        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v_x_17__boxed_2361_, v_y_18__boxed_2362_);
    v_r_2364_ = lean_box((v_res_2363_) as usize);
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
    mut v_x_2372_: *mut LeanObject,
    mut v_x_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_2374_: u8 = 0;
    let mut v_x_52__boxed_2375_: u8 = 0;
    let mut v_res_2376_: u8 = 0;
    let mut v_r_2377_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_2374_ = (lean_unbox(v_x_2372_) as u8);
    v_x_52__boxed_2375_ = (lean_unbox(v_x_2373_) as u8);
    v_res_2376_ =
        l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(
            v_x_51__boxed_2374_,
            v_x_52__boxed_2375_,
        );
    v_r_2377_ = lean_box((v_res_2376_) as usize);
    return v_r_2377_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0() -> *mut LeanObject
{
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    v___x_2378_ = lean_box(0);
    v___x_2379_ = lean_unsigned_to_nat(16);
    v___x_2380_ = lean_mk_array(v___x_2379_, v___x_2378_);
    return v___x_2380_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1() -> *mut LeanObject
{
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    v___x_2381_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__0,
    );
    v___x_2382_ = lean_unsigned_to_nat(0);
    v___x_2383_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2383_, 0, v___x_2382_);
    lean_ctor_set(v___x_2383_, 1, v___x_2381_);
    return v___x_2383_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2() -> *mut LeanObject
{
    let mut v___x_2384_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384_ = 0;
    v___x_2385_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__1,
    );
    v___x_2386_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_2386_, 0, v___x_2385_);
    lean_ctor_set_uint8(
        v___x_2386_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2384_,
    );
    return v___x_2386_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedState_default() -> *mut LeanObject {
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    v___x_2387_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedState_default___closed__2,
    );
    return v___x_2387_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState()
-> *mut LeanObject {
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    v___x_2388_ = l_Lean_Compiler_LCNF_instInhabitedState_default;
    return v___x_2388_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg(
    mut v_fvarId_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    v___x_2394_ = lean_st_ref_get(v_a_2392_);
    v_values_2395_ = lean_ctor_get(v___x_2394_, 0);
    lean_inc_ref(v_values_2395_);
    lean_dec(v___x_2394_);
    v___x_2396_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0;
    v___x_2397_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1;
    v___x_2398_ = 0;
    v___x_2399_ = lean_box((v___x_2398_) as usize);
    v___x_2400_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v___x_2396_,
        v___x_2397_,
        v_values_2395_,
        v_fvarId_2391_,
        v___x_2399_,
    );
    lean_dec(v___x_2399_);
    lean_dec_ref(v_values_2395_);
    v___x_2401_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2401_, 0, v___x_2400_);
    return v___x_2401_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___boxed(
    mut v_fvarId_2402_: *mut LeanObject,
    mut v_a_2403_: *mut LeanObject,
    mut v_a_2404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2405_: *mut LeanObject = core::ptr::null_mut();
    v_res_2405_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg(v_fvarId_2402_, v_a_2403_);
    lean_dec(v_a_2403_);
    return v_res_2405_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness(
    mut v_fvarId_2406_: *mut LeanObject,
    mut v_a_2407_: *mut LeanObject,
    mut v_a_2408_: *mut LeanObject,
    mut v_a_2409_: *mut LeanObject,
    mut v_a_2410_: *mut LeanObject,
    mut v_a_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    v___x_2413_ = lean_st_ref_get(v_a_2407_);
    v_values_2414_ = lean_ctor_get(v___x_2413_, 0);
    lean_inc_ref(v_values_2414_);
    lean_dec(v___x_2413_);
    v___x_2415_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0;
    v___x_2416_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1;
    v___x_2417_ = 0;
    v___x_2418_ = lean_box((v___x_2417_) as usize);
    v___x_2419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v___x_2415_,
        v___x_2416_,
        v_values_2414_,
        v_fvarId_2406_,
        v___x_2418_,
    );
    lean_dec(v___x_2418_);
    lean_dec_ref(v_values_2414_);
    v___x_2420_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2420_, 0, v___x_2419_);
    return v___x_2420_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___boxed(
    mut v_fvarId_2421_: *mut LeanObject,
    mut v_a_2422_: *mut LeanObject,
    mut v_a_2423_: *mut LeanObject,
    mut v_a_2424_: *mut LeanObject,
    mut v_a_2425_: *mut LeanObject,
    mut v_a_2426_: *mut LeanObject,
    mut v_a_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2428_: *mut LeanObject = core::ptr::null_mut();
    v_res_2428_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness(v_fvarId_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
    lean_dec(v_a_2426_);
    lean_dec_ref(v_a_2425_);
    lean_dec(v_a_2424_);
    lean_dec_ref(v_a_2423_);
    lean_dec(v_a_2422_);
    return v_res_2428_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join___redArg(
    mut v_fvarId_2429_: *mut LeanObject,
    mut v_v_2430_: u8,
    mut v_a_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: u8 = 0;
    let mut v_new_2447_: u8 = 0;
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: u8 = 0;
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2452_: u8 = 0;
    let mut v___x_2453_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_unused_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2433_ = lean_st_ref_take(v_a_2431_);
                v_values_2439_ = lean_ctor_get(v___x_2433_, 0);
                lean_inc_ref(v_values_2439_);
                v___x_2440_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0;
                v___x_2441_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1;
                v___x_2442_ = lean_box(0);
                v___x_2443_ = 0;
                v___x_2444_ = lean_box((v___x_2443_) as usize);
                lean_inc(v_fvarId_2429_);
                v_old_2445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
                    v___x_2440_,
                    v___x_2441_,
                    v_values_2439_,
                    v_fvarId_2429_,
                    v___x_2444_,
                );
                lean_dec(v___x_2444_);
                v___x_2446_ = (lean_unbox(v_old_2445_) as u8);
                v_new_2447_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2446_, v_v_2430_);
                v___x_2448_ = (lean_unbox(v_old_2445_) as u8);
                lean_dec(v_old_2445_);
                v___x_2449_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2448_, v_new_2447_);
                if v___x_2449_ == 0 {
                    v_isSharedCheck_2459_ = (!lean_is_exclusive(v___x_2433_)) as u8;
                    if v_isSharedCheck_2459_ == 0 {
                        v_unused_2460_ = lean_ctor_get(v___x_2433_, 0);
                        lean_dec(v_unused_2460_);
                        v___x_2451_ = v___x_2433_;
                        v_isShared_2452_ = v_isSharedCheck_2459_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2433_);
                        v___x_2451_ = lean_box(0);
                        v_isShared_2452_ = v_isSharedCheck_2459_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_values_2439_);
                    lean_dec(v_fvarId_2429_);
                    v_fst_2435_ = v___x_2442_;
                    v_snd_2436_ = v___x_2433_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2437_ = lean_st_ref_set(v_a_2431_, v_snd_2436_);
                v___x_2438_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2438_, 0, v_fst_2435_);
                return v___x_2438_;
            }
            2 => {
                v___x_2453_ = 1;
                v___x_2454_ = lean_box((v_new_2447_) as usize);
                v___x_2455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_2440_,
                    v___x_2441_,
                    v_values_2439_,
                    v_fvarId_2429_,
                    v___x_2454_,
                );
                if v_isShared_2452_ == 0 {
                    lean_ctor_set(v___x_2451_, 0, v___x_2455_);
                    v___x_2457_ = v___x_2451_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
                    v___x_2457_ = v_reuseFailAlloc_2458_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_2457_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_fvarId_2461_: *mut LeanObject,
    mut v_v_2462_: *mut LeanObject,
    mut v_a_2463_: *mut LeanObject,
    mut v_a_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_2465_: u8 = 0;
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_2465_ = (lean_unbox(v_v_2462_) as u8);
    v_res_2466_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join___redArg(v_fvarId_2461_, v_v_boxed_2465_, v_a_2463_);
    lean_dec(v_a_2463_);
    return v_res_2466_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join(
    mut v_fvarId_2467_: *mut LeanObject,
    mut v_v_2468_: u8,
    mut v_a_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
    mut v_a_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
    mut v_a_2473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: u8 = 0;
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v_new_2489_: u8 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_unused_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2475_ = lean_st_ref_take(v_a_2469_);
                v_values_2481_ = lean_ctor_get(v___x_2475_, 0);
                lean_inc_ref(v_values_2481_);
                v___x_2482_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__0;
                v___x_2483_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getOwnedness___redArg___closed__1;
                v___x_2484_ = lean_box(0);
                v___x_2485_ = 0;
                v___x_2486_ = lean_box((v___x_2485_) as usize);
                lean_inc(v_fvarId_2467_);
                v_old_2487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
                    v___x_2482_,
                    v___x_2483_,
                    v_values_2481_,
                    v_fvarId_2467_,
                    v___x_2486_,
                );
                lean_dec(v___x_2486_);
                v___x_2488_ = (lean_unbox(v_old_2487_) as u8);
                v_new_2489_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2488_, v_v_2468_);
                v___x_2490_ = (lean_unbox(v_old_2487_) as u8);
                lean_dec(v_old_2487_);
                v___x_2491_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2490_, v_new_2489_);
                if v___x_2491_ == 0 {
                    v_isSharedCheck_2501_ = (!lean_is_exclusive(v___x_2475_)) as u8;
                    if v_isSharedCheck_2501_ == 0 {
                        v_unused_2502_ = lean_ctor_get(v___x_2475_, 0);
                        lean_dec(v_unused_2502_);
                        v___x_2493_ = v___x_2475_;
                        v_isShared_2494_ = v_isSharedCheck_2501_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2475_);
                        v___x_2493_ = lean_box(0);
                        v_isShared_2494_ = v_isSharedCheck_2501_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_values_2481_);
                    lean_dec(v_fvarId_2467_);
                    v_fst_2477_ = v___x_2484_;
                    v_snd_2478_ = v___x_2475_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2479_ = lean_st_ref_set(v_a_2469_, v_snd_2478_);
                v___x_2480_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2480_, 0, v_fst_2477_);
                return v___x_2480_;
            }
            2 => {
                v___x_2495_ = 1;
                v___x_2496_ = lean_box((v_new_2489_) as usize);
                v___x_2497_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_2482_,
                    v___x_2483_,
                    v_values_2481_,
                    v_fvarId_2467_,
                    v___x_2496_,
                );
                if v_isShared_2494_ == 0 {
                    lean_ctor_set(v___x_2493_, 0, v___x_2497_);
                    v___x_2499_ = v___x_2493_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_2499_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_fvarId_2503_: *mut LeanObject,
    mut v_v_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
    mut v_a_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_2511_: u8 = 0;
    let mut v_res_2512_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_2511_ = (lean_unbox(v_v_2504_) as u8);
    v_res_2512_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_join(v_fvarId_2503_, v_v_boxed_2511_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
    lean_dec(v_a_2509_);
    lean_dec_ref(v_a_2508_);
    lean_dec(v_a_2507_);
    lean_dec_ref(v_a_2506_);
    lean_dec(v_a_2505_);
    return v_res_2512_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_instMonadEIO(lean_box(0));
    return v___x_2513_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    v___x_2518_ = l_Array_instInhabited(lean_box(0));
    return v___x_2518_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0(
    mut v_msg_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
    mut v___y_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v_toFunctor_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v___f_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v_toFunctor_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___f_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405__overap_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut v_unused_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut v_unused_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_unused_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v_unused_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2526_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0);
                v___x_2527_ = l_StateRefT_x27_instMonad___redArg(v___x_2526_);
                v_toApplicative_2528_ = lean_ctor_get(v___x_2527_, 0);
                v_isSharedCheck_2590_ = (!lean_is_exclusive(v___x_2527_)) as u8;
                if v_isSharedCheck_2590_ == 0 {
                    v_unused_2591_ = lean_ctor_get(v___x_2527_, 1);
                    lean_dec(v_unused_2591_);
                    v___x_2530_ = v___x_2527_;
                    v_isShared_2531_ = v_isSharedCheck_2590_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2528_);
                    lean_dec(v___x_2527_);
                    v___x_2530_ = lean_box(0);
                    v_isShared_2531_ = v_isSharedCheck_2590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2532_ = lean_ctor_get(v_toApplicative_2528_, 0);
                v_toSeq_2533_ = lean_ctor_get(v_toApplicative_2528_, 2);
                v_toSeqLeft_2534_ = lean_ctor_get(v_toApplicative_2528_, 3);
                v_toSeqRight_2535_ = lean_ctor_get(v_toApplicative_2528_, 4);
                v_isSharedCheck_2588_ = (!lean_is_exclusive(v_toApplicative_2528_)) as u8;
                if v_isSharedCheck_2588_ == 0 {
                    v_unused_2589_ = lean_ctor_get(v_toApplicative_2528_, 1);
                    lean_dec(v_unused_2589_);
                    v___x_2537_ = v_toApplicative_2528_;
                    v_isShared_2538_ = v_isSharedCheck_2588_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2535_);
                    lean_inc(v_toSeqLeft_2534_);
                    lean_inc(v_toSeq_2533_);
                    lean_inc(v_toFunctor_2532_);
                    lean_dec(v_toApplicative_2528_);
                    v___x_2537_ = lean_box(0);
                    v_isShared_2538_ = v_isSharedCheck_2588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2539_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1;
                v___f_2540_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_2532_);
                v___f_2541_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2541_, 0, v_toFunctor_2532_);
                v___f_2542_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2542_, 0, v_toFunctor_2532_);
                v___x_2543_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2543_, 0, v___f_2541_);
                lean_ctor_set(v___x_2543_, 1, v___f_2542_);
                v___f_2544_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2544_, 0, v_toSeqRight_2535_);
                v___f_2545_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2545_, 0, v_toSeqLeft_2534_);
                v___f_2546_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2546_, 0, v_toSeq_2533_);
                if v_isShared_2538_ == 0 {
                    lean_ctor_set(v___x_2537_, 4, v___f_2544_);
                    lean_ctor_set(v___x_2537_, 3, v___f_2545_);
                    lean_ctor_set(v___x_2537_, 2, v___f_2546_);
                    lean_ctor_set(v___x_2537_, 1, v___f_2539_);
                    lean_ctor_set(v___x_2537_, 0, v___x_2543_);
                    v___x_2548_ = v___x_2537_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2543_);
                    lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___f_2539_);
                    lean_ctor_set(v_reuseFailAlloc_2587_, 2, v___f_2546_);
                    lean_ctor_set(v_reuseFailAlloc_2587_, 3, v___f_2545_);
                    lean_ctor_set(v_reuseFailAlloc_2587_, 4, v___f_2544_);
                    v___x_2548_ = v_reuseFailAlloc_2587_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2531_ == 0 {
                    lean_ctor_set(v___x_2530_, 1, v___f_2540_);
                    lean_ctor_set(v___x_2530_, 0, v___x_2548_);
                    v___x_2550_ = v___x_2530_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2548_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___f_2540_);
                    v___x_2550_ = v_reuseFailAlloc_2586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2551_ = l_StateRefT_x27_instMonad___redArg(v___x_2550_);
                v_toApplicative_2552_ = lean_ctor_get(v___x_2551_, 0);
                v_isSharedCheck_2584_ = (!lean_is_exclusive(v___x_2551_)) as u8;
                if v_isSharedCheck_2584_ == 0 {
                    v_unused_2585_ = lean_ctor_get(v___x_2551_, 1);
                    lean_dec(v_unused_2585_);
                    v___x_2554_ = v___x_2551_;
                    v_isShared_2555_ = v_isSharedCheck_2584_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2552_);
                    lean_dec(v___x_2551_);
                    v___x_2554_ = lean_box(0);
                    v_isShared_2555_ = v_isSharedCheck_2584_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2556_ = lean_ctor_get(v_toApplicative_2552_, 0);
                v_toSeq_2557_ = lean_ctor_get(v_toApplicative_2552_, 2);
                v_toSeqLeft_2558_ = lean_ctor_get(v_toApplicative_2552_, 3);
                v_toSeqRight_2559_ = lean_ctor_get(v_toApplicative_2552_, 4);
                v_isSharedCheck_2582_ = (!lean_is_exclusive(v_toApplicative_2552_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v_unused_2583_ = lean_ctor_get(v_toApplicative_2552_, 1);
                    lean_dec(v_unused_2583_);
                    v___x_2561_ = v_toApplicative_2552_;
                    v_isShared_2562_ = v_isSharedCheck_2582_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2559_);
                    lean_inc(v_toSeqLeft_2558_);
                    lean_inc(v_toSeq_2557_);
                    lean_inc(v_toFunctor_2556_);
                    lean_dec(v_toApplicative_2552_);
                    v___x_2561_ = lean_box(0);
                    v_isShared_2562_ = v_isSharedCheck_2582_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2563_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3;
                v___f_2564_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4;
                lean_inc_ref(v_toFunctor_2556_);
                v___f_2565_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2565_, 0, v_toFunctor_2556_);
                v___f_2566_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2566_, 0, v_toFunctor_2556_);
                v___x_2567_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2567_, 0, v___f_2565_);
                lean_ctor_set(v___x_2567_, 1, v___f_2566_);
                v___f_2568_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2568_, 0, v_toSeqRight_2559_);
                v___f_2569_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2569_, 0, v_toSeqLeft_2558_);
                v___f_2570_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2570_, 0, v_toSeq_2557_);
                if v_isShared_2562_ == 0 {
                    lean_ctor_set(v___x_2561_, 4, v___f_2568_);
                    lean_ctor_set(v___x_2561_, 3, v___f_2569_);
                    lean_ctor_set(v___x_2561_, 2, v___f_2570_);
                    lean_ctor_set(v___x_2561_, 1, v___f_2563_);
                    lean_ctor_set(v___x_2561_, 0, v___x_2567_);
                    v___x_2572_ = v___x_2561_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2567_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___f_2563_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 2, v___f_2570_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 3, v___f_2569_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 4, v___f_2568_);
                    v___x_2572_ = v_reuseFailAlloc_2581_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2555_ == 0 {
                    lean_ctor_set(v___x_2554_, 1, v___f_2564_);
                    lean_ctor_set(v___x_2554_, 0, v___x_2572_);
                    v___x_2574_ = v___x_2554_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2572_);
                    lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___f_2564_);
                    v___x_2574_ = v_reuseFailAlloc_2580_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2575_ = l_StateRefT_x27_instMonad___redArg(v___x_2574_);
                v___x_2576_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__5);
                v___x_2577_ = l_instInhabitedOfMonad___redArg(v___x_2575_, v___x_2576_);
                v___x_405__overap_2578_ = lean_panic_fn_borrowed(v___x_2577_, v_msg_2519_);
                lean_dec(v___x_2577_);
                lean_inc(v___y_2524_);
                lean_inc_ref(v___y_2523_);
                lean_inc(v___y_2522_);
                lean_inc_ref(v___y_2521_);
                lean_inc(v___y_2520_);
                v___x_2579_ = lean_apply_6(
                    v___x_405__overap_2578_,
                    v___y_2520_,
                    v___y_2521_,
                    v___y_2522_,
                    v___y_2523_,
                    v___y_2524_,
                    lean_box(0),
                );
                return v___x_2579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___boxed(
    mut v_msg_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
    mut v___y_2595_: *mut LeanObject,
    mut v___y_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
    mut v___y_2598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2599_: *mut LeanObject = core::ptr::null_mut();
    v_res_2599_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0(v_msg_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
    lean_dec(v___y_2597_);
    lean_dec_ref(v___y_2596_);
    lean_dec(v___y_2595_);
    lean_dec_ref(v___y_2594_);
    lean_dec(v___y_2593_);
    return v_res_2599_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3()
-> *mut LeanObject {
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    v___x_2603_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_2604_ = lean_unsigned_to_nat(43);
    v___x_2605_ = lean_unsigned_to_nat(61);
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
    mut v_f_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v_val_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2628_: u8 = 0;
    let mut v_a_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2616_ =
                    l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_f_2609_, v_a_2614_);
                if lean_obj_tag(v___x_2616_) == 0 {
                    v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2628_ = (!lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2628_ == 0 {
                        v___x_2619_ = v___x_2616_;
                        v_isShared_2620_ = v_isSharedCheck_2628_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2617_);
                        lean_dec(v___x_2616_);
                        v___x_2619_ = lean_box(0);
                        v_isShared_2620_ = v_isSharedCheck_2628_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2629_ = lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2636_ = (!lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2636_ == 0 {
                        v___x_2631_ = v___x_2616_;
                        v_isShared_2632_ = v_isSharedCheck_2636_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2629_);
                        lean_dec(v___x_2616_);
                        v___x_2631_ = lean_box(0);
                        v_isShared_2632_ = v_isSharedCheck_2636_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2617_) == 1 {
                    v_val_2621_ = lean_ctor_get(v_a_2617_, 0);
                    lean_inc(v_val_2621_);
                    lean_dec_ref_known(v_a_2617_, 1);
                    v_params_2622_ = lean_ctor_get(v_val_2621_, 3);
                    lean_inc_ref(v_params_2622_);
                    lean_dec(v_val_2621_);
                    if v_isShared_2620_ == 0 {
                        lean_ctor_set(v___x_2619_, 0, v_params_2622_);
                        v___x_2624_ = v___x_2619_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_params_2622_);
                        v___x_2624_ = v_reuseFailAlloc_2625_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2619_);
                    lean_dec(v_a_2617_);
                    v___x_2626_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__3);
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
                    v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
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
    mut v_f_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_a_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2644_: *mut LeanObject = core::ptr::null_mut();
    v_res_2644_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams(v_f_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
    lean_dec(v_a_2642_);
    lean_dec_ref(v_a_2641_);
    lean_dec(v_a_2640_);
    lean_dec_ref(v_a_2639_);
    lean_dec(v_a_2638_);
    return v_res_2644_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(
    mut v_msg_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v_toFunctor_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___f_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v_toFunctor_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___f_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397__overap_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2708_: u8 = 0;
    let mut v_unused_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut v_unused_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_unused_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2716_: u8 = 0;
    let mut v_unused_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0);
                v___x_2653_ = l_StateRefT_x27_instMonad___redArg(v___x_2652_);
                v_toApplicative_2654_ = lean_ctor_get(v___x_2653_, 0);
                v_isSharedCheck_2716_ = (!lean_is_exclusive(v___x_2653_)) as u8;
                if v_isSharedCheck_2716_ == 0 {
                    v_unused_2717_ = lean_ctor_get(v___x_2653_, 1);
                    lean_dec(v_unused_2717_);
                    v___x_2656_ = v___x_2653_;
                    v_isShared_2657_ = v_isSharedCheck_2716_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2654_);
                    lean_dec(v___x_2653_);
                    v___x_2656_ = lean_box(0);
                    v_isShared_2657_ = v_isSharedCheck_2716_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2658_ = lean_ctor_get(v_toApplicative_2654_, 0);
                v_toSeq_2659_ = lean_ctor_get(v_toApplicative_2654_, 2);
                v_toSeqLeft_2660_ = lean_ctor_get(v_toApplicative_2654_, 3);
                v_toSeqRight_2661_ = lean_ctor_get(v_toApplicative_2654_, 4);
                v_isSharedCheck_2714_ = (!lean_is_exclusive(v_toApplicative_2654_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v_unused_2715_ = lean_ctor_get(v_toApplicative_2654_, 1);
                    lean_dec(v_unused_2715_);
                    v___x_2663_ = v_toApplicative_2654_;
                    v_isShared_2664_ = v_isSharedCheck_2714_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2661_);
                    lean_inc(v_toSeqLeft_2660_);
                    lean_inc(v_toSeq_2659_);
                    lean_inc(v_toFunctor_2658_);
                    lean_dec(v_toApplicative_2654_);
                    v___x_2663_ = lean_box(0);
                    v_isShared_2664_ = v_isSharedCheck_2714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2665_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1;
                v___f_2666_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_2658_);
                v___f_2667_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2667_, 0, v_toFunctor_2658_);
                v___f_2668_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2668_, 0, v_toFunctor_2658_);
                v___x_2669_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2669_, 0, v___f_2667_);
                lean_ctor_set(v___x_2669_, 1, v___f_2668_);
                v___f_2670_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2670_, 0, v_toSeqRight_2661_);
                v___f_2671_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2671_, 0, v_toSeqLeft_2660_);
                v___f_2672_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2672_, 0, v_toSeq_2659_);
                if v_isShared_2664_ == 0 {
                    lean_ctor_set(v___x_2663_, 4, v___f_2670_);
                    lean_ctor_set(v___x_2663_, 3, v___f_2671_);
                    lean_ctor_set(v___x_2663_, 2, v___f_2672_);
                    lean_ctor_set(v___x_2663_, 1, v___f_2665_);
                    lean_ctor_set(v___x_2663_, 0, v___x_2669_);
                    v___x_2674_ = v___x_2663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2669_);
                    lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___f_2665_);
                    lean_ctor_set(v_reuseFailAlloc_2713_, 2, v___f_2672_);
                    lean_ctor_set(v_reuseFailAlloc_2713_, 3, v___f_2671_);
                    lean_ctor_set(v_reuseFailAlloc_2713_, 4, v___f_2670_);
                    v___x_2674_ = v_reuseFailAlloc_2713_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2657_ == 0 {
                    lean_ctor_set(v___x_2656_, 1, v___f_2666_);
                    lean_ctor_set(v___x_2656_, 0, v___x_2674_);
                    v___x_2676_ = v___x_2656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2674_);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___f_2666_);
                    v___x_2676_ = v_reuseFailAlloc_2712_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2677_ = l_StateRefT_x27_instMonad___redArg(v___x_2676_);
                v_toApplicative_2678_ = lean_ctor_get(v___x_2677_, 0);
                v_isSharedCheck_2710_ = (!lean_is_exclusive(v___x_2677_)) as u8;
                if v_isSharedCheck_2710_ == 0 {
                    v_unused_2711_ = lean_ctor_get(v___x_2677_, 1);
                    lean_dec(v_unused_2711_);
                    v___x_2680_ = v___x_2677_;
                    v_isShared_2681_ = v_isSharedCheck_2710_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2678_);
                    lean_dec(v___x_2677_);
                    v___x_2680_ = lean_box(0);
                    v_isShared_2681_ = v_isSharedCheck_2710_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2682_ = lean_ctor_get(v_toApplicative_2678_, 0);
                v_toSeq_2683_ = lean_ctor_get(v_toApplicative_2678_, 2);
                v_toSeqLeft_2684_ = lean_ctor_get(v_toApplicative_2678_, 3);
                v_toSeqRight_2685_ = lean_ctor_get(v_toApplicative_2678_, 4);
                v_isSharedCheck_2708_ = (!lean_is_exclusive(v_toApplicative_2678_)) as u8;
                if v_isSharedCheck_2708_ == 0 {
                    v_unused_2709_ = lean_ctor_get(v_toApplicative_2678_, 1);
                    lean_dec(v_unused_2709_);
                    v___x_2687_ = v_toApplicative_2678_;
                    v_isShared_2688_ = v_isSharedCheck_2708_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2685_);
                    lean_inc(v_toSeqLeft_2684_);
                    lean_inc(v_toSeq_2683_);
                    lean_inc(v_toFunctor_2682_);
                    lean_dec(v_toApplicative_2678_);
                    v___x_2687_ = lean_box(0);
                    v_isShared_2688_ = v_isSharedCheck_2708_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2689_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__3;
                v___f_2690_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__4;
                lean_inc_ref(v_toFunctor_2682_);
                v___f_2691_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2691_, 0, v_toFunctor_2682_);
                v___f_2692_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2692_, 0, v_toFunctor_2682_);
                v___x_2693_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2693_, 0, v___f_2691_);
                lean_ctor_set(v___x_2693_, 1, v___f_2692_);
                v___f_2694_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2694_, 0, v_toSeqRight_2685_);
                v___f_2695_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2695_, 0, v_toSeqLeft_2684_);
                v___f_2696_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2696_, 0, v_toSeq_2683_);
                if v_isShared_2688_ == 0 {
                    lean_ctor_set(v___x_2687_, 4, v___f_2694_);
                    lean_ctor_set(v___x_2687_, 3, v___f_2695_);
                    lean_ctor_set(v___x_2687_, 2, v___f_2696_);
                    lean_ctor_set(v___x_2687_, 1, v___f_2689_);
                    lean_ctor_set(v___x_2687_, 0, v___x_2693_);
                    v___x_2698_ = v___x_2687_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2693_);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___f_2689_);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 2, v___f_2696_);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 3, v___f_2695_);
                    lean_ctor_set(v_reuseFailAlloc_2707_, 4, v___f_2694_);
                    v___x_2698_ = v_reuseFailAlloc_2707_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2681_ == 0 {
                    lean_ctor_set(v___x_2680_, 1, v___f_2690_);
                    lean_ctor_set(v___x_2680_, 0, v___x_2698_);
                    v___x_2700_ = v___x_2680_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2698_);
                    lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___f_2690_);
                    v___x_2700_ = v_reuseFailAlloc_2706_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2701_ = l_StateRefT_x27_instMonad___redArg(v___x_2700_);
                v___x_2702_ = lean_box(0);
                v___x_2703_ = l_instInhabitedOfMonad___redArg(v___x_2701_, v___x_2702_);
                v___x_3397__overap_2704_ = lean_panic_fn_borrowed(v___x_2703_, v_msg_2645_);
                lean_dec(v___x_2703_);
                lean_inc(v___y_2650_);
                lean_inc_ref(v___y_2649_);
                lean_inc(v___y_2648_);
                lean_inc_ref(v___y_2647_);
                lean_inc(v___y_2646_);
                v___x_2705_ = lean_apply_6(
                    v___x_3397__overap_2704_,
                    v___y_2646_,
                    v___y_2647_,
                    v___y_2648_,
                    v___y_2649_,
                    v___y_2650_,
                    lean_box(0),
                );
                return v___x_2705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2___boxed(
    mut v_msg_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
    mut v___y_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2725_: *mut LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(v_msg_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
    lean_dec(v___y_2723_);
    lean_dec_ref(v___y_2722_);
    lean_dec(v___y_2721_);
    lean_dec_ref(v___y_2720_);
    lean_dec(v___y_2719_);
    return v_res_2725_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4___redArg(
    mut v_a_2726_: *mut LeanObject,
    mut v_b_2727_: *mut LeanObject,
    mut v_x_2728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2735_: u8 = 0;
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2728_) == 0 {
                    lean_dec(v_b_2727_);
                    lean_dec(v_a_2726_);
                    return v_x_2728_;
                } else {
                    v_key_2729_ = lean_ctor_get(v_x_2728_, 0);
                    v_value_2730_ = lean_ctor_get(v_x_2728_, 1);
                    v_tail_2731_ = lean_ctor_get(v_x_2728_, 2);
                    v_isSharedCheck_2743_ = (!lean_is_exclusive(v_x_2728_)) as u8;
                    if v_isSharedCheck_2743_ == 0 {
                        v___x_2733_ = v_x_2728_;
                        v_isShared_2734_ = v_isSharedCheck_2743_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2731_);
                        lean_inc(v_value_2730_);
                        lean_inc(v_key_2729_);
                        lean_dec(v_x_2728_);
                        v___x_2733_ = lean_box(0);
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
                        lean_ctor_set(v___x_2733_, 2, v___x_2736_);
                        v___x_2738_ = v___x_2733_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_key_2729_);
                        lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_value_2730_);
                        lean_ctor_set(v_reuseFailAlloc_2739_, 2, v___x_2736_);
                        v___x_2738_ = v_reuseFailAlloc_2739_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2730_);
                    lean_dec(v_key_2729_);
                    if v_isShared_2734_ == 0 {
                        lean_ctor_set(v___x_2733_, 1, v_b_2727_);
                        lean_ctor_set(v___x_2733_, 0, v_a_2726_);
                        v___x_2741_ = v___x_2733_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2726_);
                        lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_b_2727_);
                        lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_tail_2731_);
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
    mut v_x_2744_: *mut LeanObject,
    mut v_x_2745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2745_) == 0 {
                    return v_x_2744_;
                } else {
                    v_key_2746_ = lean_ctor_get(v_x_2745_, 0);
                    v_value_2747_ = lean_ctor_get(v_x_2745_, 1);
                    v_tail_2748_ = lean_ctor_get(v_x_2745_, 2);
                    v_isSharedCheck_2771_ = (!lean_is_exclusive(v_x_2745_)) as u8;
                    if v_isSharedCheck_2771_ == 0 {
                        v___x_2750_ = v_x_2745_;
                        v_isShared_2751_ = v_isSharedCheck_2771_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2748_);
                        lean_inc(v_value_2747_);
                        lean_inc(v_key_2746_);
                        lean_dec(v_x_2745_);
                        v___x_2750_ = lean_box(0);
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
                lean_inc(v___x_2765_);
                if v_isShared_2751_ == 0 {
                    lean_ctor_set(v___x_2750_, 2, v___x_2765_);
                    v___x_2767_ = v___x_2750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_key_2746_);
                    lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_value_2747_);
                    lean_ctor_set(v_reuseFailAlloc_2770_, 2, v___x_2765_);
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
    mut v_i_2772_: *mut LeanObject,
    mut v_source_2773_: *mut LeanObject,
    mut v_target_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: u8 = 0;
    let mut v_es_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2775_ = lean_array_get_size(v_source_2773_);
                v___x_2776_ = lean_nat_dec_lt(v_i_2772_, v___x_2775_);
                if v___x_2776_ == 0 {
                    lean_dec_ref(v_source_2773_);
                    lean_dec(v_i_2772_);
                    return v_target_2774_;
                } else {
                    v_es_2777_ = lean_array_fget(v_source_2773_, v_i_2772_);
                    v___x_2778_ = lean_box(0);
                    v_source_2779_ = lean_array_fset(v_source_2773_, v_i_2772_, v___x_2778_);
                    v_target_2780_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5_spec__6___redArg(v_target_2774_, v_es_2777_);
                    v___x_2781_ = lean_unsigned_to_nat(1);
                    v___x_2782_ = lean_nat_add(v_i_2772_, v___x_2781_);
                    lean_dec(v_i_2772_);
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
    mut v_data_2784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    v___x_2785_ = lean_array_get_size(v_data_2784_);
    v___x_2786_ = lean_unsigned_to_nat(2);
    v_nbuckets_2787_ = lean_nat_mul(v___x_2785_, v___x_2786_);
    v___x_2788_ = lean_unsigned_to_nat(0);
    v___x_2789_ = lean_box(0);
    v___x_2790_ = lean_mk_array(v_nbuckets_2787_, v___x_2789_);
    v___x_2791_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5___redArg(v___x_2788_, v_data_2784_, v___x_2790_);
    return v___x_2791_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg(
    mut v_a_2792_: *mut LeanObject,
    mut v_x_2793_: *mut LeanObject,
) -> u8 {
    let mut v___x_2794_: u8 = 0;
    let mut v_key_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2793_) == 0 {
                    v___x_2794_ = 0;
                    return v___x_2794_;
                } else {
                    v_key_2795_ = lean_ctor_get(v_x_2793_, 0);
                    v_tail_2796_ = lean_ctor_get(v_x_2793_, 2);
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
    mut v_a_2799_: *mut LeanObject,
    mut v_x_2800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2801_: u8 = 0;
    let mut v_r_2802_: *mut LeanObject = core::ptr::null_mut();
    v_res_2801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg(v_a_2799_, v_x_2800_);
    lean_dec(v_x_2800_);
    lean_dec(v_a_2799_);
    v_r_2802_ = lean_box((v_res_2801_) as usize);
    return v_r_2802_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(
    mut v_m_2803_: *mut LeanObject,
    mut v_a_2804_: *mut LeanObject,
    mut v_b_2805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v_val_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2806_ = lean_ctor_get(v_m_2803_, 0);
                v_buckets_2807_ = lean_ctor_get(v_m_2803_, 1);
                v_isSharedCheck_2850_ = (!lean_is_exclusive(v_m_2803_)) as u8;
                if v_isSharedCheck_2850_ == 0 {
                    v___x_2809_ = v_m_2803_;
                    v_isShared_2810_ = v_isSharedCheck_2850_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2807_);
                    lean_inc(v_size_2806_);
                    lean_dec(v_m_2803_);
                    v___x_2809_ = lean_box(0);
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
                    v___x_2826_ = lean_unsigned_to_nat(1);
                    v_size_x27_2827_ = lean_nat_add(v_size_2806_, v___x_2826_);
                    lean_dec(v_size_2806_);
                    lean_inc(v_bkt_2824_);
                    v___x_2828_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2828_, 0, v_a_2804_);
                    lean_ctor_set(v___x_2828_, 1, v_b_2805_);
                    lean_ctor_set(v___x_2828_, 2, v_bkt_2824_);
                    v_buckets_x27_2829_ =
                        lean_array_uset(v_buckets_2807_, v___x_2823_, v___x_2828_);
                    v___x_2830_ = lean_unsigned_to_nat(4);
                    v___x_2831_ = lean_nat_mul(v_size_x27_2827_, v___x_2830_);
                    v___x_2832_ = lean_unsigned_to_nat(3);
                    v___x_2833_ = lean_nat_div(v___x_2831_, v___x_2832_);
                    lean_dec(v___x_2831_);
                    v___x_2834_ = lean_array_get_size(v_buckets_x27_2829_);
                    v___x_2835_ = lean_nat_dec_le(v___x_2833_, v___x_2834_);
                    lean_dec(v___x_2833_);
                    if v___x_2835_ == 0 {
                        v_val_2836_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3___redArg(v_buckets_x27_2829_);
                        if v_isShared_2810_ == 0 {
                            lean_ctor_set(v___x_2809_, 1, v_val_2836_);
                            lean_ctor_set(v___x_2809_, 0, v_size_x27_2827_);
                            v___x_2838_ = v___x_2809_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_size_x27_2827_);
                            lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_val_2836_);
                            v___x_2838_ = v_reuseFailAlloc_2839_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2810_ == 0 {
                            lean_ctor_set(v___x_2809_, 1, v_buckets_x27_2829_);
                            lean_ctor_set(v___x_2809_, 0, v_size_x27_2827_);
                            v___x_2841_ = v___x_2809_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_size_x27_2827_);
                            lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_buckets_x27_2829_);
                            v___x_2841_ = v_reuseFailAlloc_2842_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2824_);
                    v___x_2843_ = lean_box(0);
                    v_buckets_x27_2844_ =
                        lean_array_uset(v_buckets_2807_, v___x_2823_, v___x_2843_);
                    v___x_2845_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4___redArg(v_a_2804_, v_b_2805_, v_bkt_2824_);
                    v___x_2846_ = lean_array_uset(v_buckets_x27_2844_, v___x_2823_, v___x_2845_);
                    if v_isShared_2810_ == 0 {
                        lean_ctor_set(v___x_2809_, 1, v___x_2846_);
                        v___x_2848_ = v___x_2809_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_size_2806_);
                        lean_ctor_set(v_reuseFailAlloc_2849_, 1, v___x_2846_);
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
    mut v_a_2851_: *mut LeanObject,
    mut v_fallback_2852_: *mut LeanObject,
    mut v_x_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2853_) == 0 {
                    lean_inc(v_fallback_2852_);
                    return v_fallback_2852_;
                } else {
                    v_key_2854_ = lean_ctor_get(v_x_2853_, 0);
                    v_value_2855_ = lean_ctor_get(v_x_2853_, 1);
                    v_tail_2856_ = lean_ctor_get(v_x_2853_, 2);
                    v___x_2857_ = l_Lean_instBEqFVarId_beq(v_key_2854_, v_a_2851_);
                    if v___x_2857_ == 0 {
                        v_x_2853_ = v_tail_2856_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2855_);
                        return v_value_2855_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___redArg___boxed(
    mut v_a_2859_: *mut LeanObject,
    mut v_fallback_2860_: *mut LeanObject,
    mut v_x_2861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2862_: *mut LeanObject = core::ptr::null_mut();
    v_res_2862_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___redArg(v_a_2859_, v_fallback_2860_, v_x_2861_);
    lean_dec(v_x_2861_);
    lean_dec(v_fallback_2860_);
    lean_dec(v_a_2859_);
    return v_res_2862_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(
    mut v_m_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_fallback_2865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2866_ = lean_ctor_get(v_m_2863_, 1);
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
    mut v_m_2882_: *mut LeanObject,
    mut v_a_2883_: *mut LeanObject,
    mut v_fallback_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2885_: *mut LeanObject = core::ptr::null_mut();
    v_res_2885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_m_2882_, v_a_2883_, v_fallback_2884_);
    lean_dec(v_fallback_2884_);
    lean_dec(v_a_2883_);
    lean_dec_ref(v_m_2882_);
    return v_res_2885_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5()
-> *mut LeanObject {
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    v___x_2891_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_2892_ = lean_unsigned_to_nat(11);
    v___x_2893_ = lean_unsigned_to_nat(135);
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
    mut v_z_2897_: *mut LeanObject,
    mut v_v_2898_: *mut LeanObject,
    mut v_a_2899_: *mut LeanObject,
    mut v_a_2900_: *mut LeanObject,
    mut v_a_2901_: *mut LeanObject,
    mut v_a_2902_: *mut LeanObject,
    mut v_a_2903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2913_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v_new_2921_: u8 = 0;
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_unused_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2953_: u8 = 0;
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v_new_2961_: u8 = 0;
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2967_: u8 = 0;
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2973_: u8 = 0;
    let mut v_unused_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: u8 = 0;
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: u8 = 0;
    let mut v_new_2993_: u8 = 0;
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: u8 = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_unused_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: u8 = 0;
    let mut v___x_3015_: u8 = 0;
    let mut v_pre_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v_args_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: u8 = 0;
    let mut v_new_3041_: u8 = 0;
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3052_: u8 = 0;
    let mut v_unused_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v___y_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: u8 = 0;
    let mut v_new_3078_: u8 = 0;
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_unused_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: u8 = 0;
    let mut v_new_3113_: u8 = 0;
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3118_: u8 = 0;
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_unused_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: u8 = 0;
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: u8 = 0;
    let mut v_new_3143_: u8 = 0;
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3149_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut v_unused_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: u8 = 0;
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: u8 = 0;
    let mut v_new_3170_: u8 = 0;
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3175_: u8 = 0;
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut v_unused_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: u8 = 0;
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: u8 = 0;
    let mut v_new_3197_: u8 = 0;
    let mut v___x_3198_: u8 = 0;
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3202_: u8 = 0;
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut v_unused_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v_new_3224_: u8 = 0;
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3226_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3229_: u8 = 0;
    let mut v___x_3230_: u8 = 0;
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_unused_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: u8 = 0;
    let mut v_new_3251_: u8 = 0;
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_unused_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3267_: u8 = 0;
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v_new_3283_: u8 = 0;
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3289_: u8 = 0;
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v_unused_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_unused_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_v_2898_) {
                6 => {
                    v_var_2975_ = lean_ctor_get(v_v_2898_, 1);
                    lean_inc(v_var_2975_);
                    lean_dec_ref_known(v_v_2898_, 2);
                    v___x_2976_ = lean_st_ref_get(v_a_2899_);
                    v___x_2977_ = lean_st_ref_take(v_a_2899_);
                    v_values_2983_ = lean_ctor_get(v___x_2976_, 0);
                    lean_inc_ref(v_values_2983_);
                    lean_dec(v___x_2976_);
                    v_values_2984_ = lean_ctor_get(v___x_2977_, 0);
                    lean_inc_ref(v_values_2984_);
                    v___x_2985_ = 0;
                    v___x_2986_ = lean_box((v___x_2985_) as usize);
                    v___x_2987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_2983_, v_var_2975_, v___x_2986_);
                    lean_dec(v___x_2986_);
                    lean_dec(v_var_2975_);
                    lean_dec_ref(v_values_2983_);
                    v___x_2988_ = lean_box(0);
                    v___x_2989_ = lean_box((v___x_2985_) as usize);
                    v_old_2990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_2984_, v_z_2897_, v___x_2989_);
                    lean_dec(v___x_2989_);
                    v___x_2991_ = (lean_unbox(v_old_2990_) as u8);
                    v___x_2992_ = (lean_unbox(v___x_2987_) as u8);
                    lean_dec(v___x_2987_);
                    v_new_2993_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2991_, v___x_2992_);
                    v___x_2994_ = (lean_unbox(v_old_2990_) as u8);
                    lean_dec(v_old_2990_);
                    v___x_2995_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2994_, v_new_2993_);
                    if v___x_2995_ == 0 {
                        v_isSharedCheck_3005_ = (!lean_is_exclusive(v___x_2977_)) as u8;
                        if v_isSharedCheck_3005_ == 0 {
                            v_unused_3006_ = lean_ctor_get(v___x_2977_, 0);
                            lean_dec(v_unused_3006_);
                            v___x_2997_ = v___x_2977_;
                            v_isShared_2998_ = v_isSharedCheck_3005_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v___x_2977_);
                            v___x_2997_ = lean_box(0);
                            v_isShared_2998_ = v_isSharedCheck_3005_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_2984_);
                        lean_dec(v_z_2897_);
                        v_fst_2979_ = v___x_2988_;
                        v_snd_2980_ = v___x_2977_;
                        state = 11;
                        continue;
                    }
                }
                9 => {
                    v_fn_3007_ = lean_ctor_get(v_v_2898_, 0);
                    lean_inc(v_fn_3007_);
                    v_args_3008_ = lean_ctor_get(v_v_2898_, 1);
                    lean_inc_ref(v_args_3008_);
                    lean_dec_ref_known(v_v_2898_, 2);
                    if lean_obj_tag(v_fn_3007_) == 1 {
                        v_pre_3016_ = lean_ctor_get(v_fn_3007_, 0);
                        lean_inc(v_pre_3016_);
                        if lean_obj_tag(v_pre_3016_) == 1 {
                            v_pre_3017_ = lean_ctor_get(v_pre_3016_, 0);
                            if lean_obj_tag(v_pre_3017_) == 0 {
                                v_str_3018_ = lean_ctor_get(v_fn_3007_, 1);
                                lean_inc_ref(v_str_3018_);
                                lean_dec_ref_known(v_fn_3007_, 2);
                                v_str_3019_ = lean_ctor_get(v_pre_3016_, 1);
                                lean_inc_ref(v_str_3019_);
                                lean_dec_ref_known(v_pre_3016_, 2);
                                v___x_3020_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__0;
                                v___x_3021_ = lean_string_dec_eq(v_str_3019_, v___x_3020_);
                                lean_dec_ref(v_str_3019_);
                                if v___x_3021_ == 0 {
                                    lean_dec_ref(v_str_3018_);
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
                                            lean_dec_ref(v_str_3018_);
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
                                            lean_dec_ref(v_str_3018_);
                                            v___x_3095_ = lean_box(0);
                                            v___x_3096_ = lean_unsigned_to_nat(1);
                                            v___x_3097_ = lean_array_get_borrowed(
                                                v___x_3095_,
                                                v_args_3008_,
                                                v___x_3096_,
                                            );
                                            if lean_obj_tag(v___x_3097_) == 1 {
                                                v_fvarId_3098_ = lean_ctor_get(v___x_3097_, 0);
                                                v___x_3099_ = lean_st_ref_get(v_a_2899_);
                                                v___x_3100_ = lean_st_ref_take(v_a_2899_);
                                                v_values_3104_ = lean_ctor_get(v___x_3099_, 0);
                                                lean_inc_ref(v_values_3104_);
                                                lean_dec(v___x_3099_);
                                                v_values_3105_ = lean_ctor_get(v___x_3100_, 0);
                                                lean_inc_ref(v_values_3105_);
                                                v___x_3106_ = 0;
                                                v___x_3107_ = lean_box((v___x_3106_) as usize);
                                                v___x_3108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3104_, v_fvarId_3098_, v___x_3107_);
                                                lean_dec(v___x_3107_);
                                                lean_dec_ref(v_values_3104_);
                                                v___x_3109_ = lean_box((v___x_3106_) as usize);
                                                v_old_3110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3105_, v_z_2897_, v___x_3109_);
                                                lean_dec(v___x_3109_);
                                                v___x_3111_ = (lean_unbox(v_old_3110_) as u8);
                                                v___x_3112_ = (lean_unbox(v___x_3108_) as u8);
                                                lean_dec(v___x_3108_);
                                                v_new_3113_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3111_, v___x_3112_);
                                                v___x_3114_ = (lean_unbox(v_old_3110_) as u8);
                                                lean_dec(v_old_3110_);
                                                v___x_3115_ =
                                                    l_Lean_Compiler_LCNF_instBEqOwnedness_beq(
                                                        v___x_3114_,
                                                        v_new_3113_,
                                                    );
                                                if v___x_3115_ == 0 {
                                                    v_isSharedCheck_3124_ =
                                                        (!lean_is_exclusive(v___x_3100_)) as u8;
                                                    if v_isSharedCheck_3124_ == 0 {
                                                        v_unused_3125_ =
                                                            lean_ctor_get(v___x_3100_, 0);
                                                        lean_dec(v_unused_3125_);
                                                        v___x_3117_ = v___x_3100_;
                                                        v_isShared_3118_ = v_isSharedCheck_3124_;
                                                        state = 22;
                                                        continue;
                                                    } else {
                                                        lean_dec(v___x_3100_);
                                                        v___x_3117_ = lean_box(0);
                                                        v_isShared_3118_ = v_isSharedCheck_3124_;
                                                        state = 22;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_values_3105_);
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
                                        lean_dec_ref(v_str_3018_);
                                        v_args_3023_ = v_args_3008_;
                                        v___y_3024_ = v_a_2899_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref_known(v_pre_3016_, 2);
                                lean_dec_ref_known(v_fn_3007_, 2);
                                v___y_3010_ = v_a_2899_;
                                state = 14;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_fn_3007_, 2);
                            lean_dec(v_pre_3016_);
                            v___y_3010_ = v_a_2899_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_dec(v_fn_3007_);
                        v___y_3010_ = v_a_2899_;
                        state = 14;
                        continue;
                    }
                }
                5 => {
                    v_i_3126_ = lean_ctor_get(v_v_2898_, 0);
                    lean_inc_ref(v_i_3126_);
                    lean_dec_ref_known(v_v_2898_, 2);
                    v___x_3127_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_3126_);
                    lean_dec_ref(v_i_3126_);
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
                    lean_dec_ref_known(v_v_2898_, 2);
                    v___x_3130_ = lean_st_ref_take(v_a_2899_);
                    v_values_3136_ = lean_ctor_get(v___x_3130_, 0);
                    lean_inc_ref(v_values_3136_);
                    v___x_3137_ = 2;
                    v___x_3138_ = lean_box(0);
                    v___x_3139_ = 0;
                    v___x_3140_ = lean_box((v___x_3139_) as usize);
                    v_old_3141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3136_, v_z_2897_, v___x_3140_);
                    lean_dec(v___x_3140_);
                    v___x_3142_ = (lean_unbox(v_old_3141_) as u8);
                    v_new_3143_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3142_, v___x_3137_);
                    v___x_3144_ = (lean_unbox(v_old_3141_) as u8);
                    lean_dec(v_old_3141_);
                    v___x_3145_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3144_, v_new_3143_);
                    if v___x_3145_ == 0 {
                        v_isSharedCheck_3155_ = (!lean_is_exclusive(v___x_3130_)) as u8;
                        if v_isSharedCheck_3155_ == 0 {
                            v_unused_3156_ = lean_ctor_get(v___x_3130_, 0);
                            lean_dec(v_unused_3156_);
                            v___x_3147_ = v___x_3130_;
                            v_isShared_3148_ = v_isSharedCheck_3155_;
                            state = 25;
                            continue;
                        } else {
                            lean_dec(v___x_3130_);
                            v___x_3147_ = lean_box(0);
                            v_isShared_3148_ = v_isSharedCheck_3155_;
                            state = 25;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_3136_);
                        lean_dec(v_z_2897_);
                        v_fst_3132_ = v___x_3138_;
                        v_snd_3133_ = v___x_3130_;
                        state = 24;
                        continue;
                    }
                }
                10 => {
                    lean_dec_ref_known(v_v_2898_, 2);
                    v___x_3157_ = lean_st_ref_take(v_a_2899_);
                    v_values_3163_ = lean_ctor_get(v___x_3157_, 0);
                    lean_inc_ref(v_values_3163_);
                    v___x_3164_ = 2;
                    v___x_3165_ = lean_box(0);
                    v___x_3166_ = 0;
                    v___x_3167_ = lean_box((v___x_3166_) as usize);
                    v_old_3168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3163_, v_z_2897_, v___x_3167_);
                    lean_dec(v___x_3167_);
                    v___x_3169_ = (lean_unbox(v_old_3168_) as u8);
                    v_new_3170_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3169_, v___x_3164_);
                    v___x_3171_ = (lean_unbox(v_old_3168_) as u8);
                    lean_dec(v_old_3168_);
                    v___x_3172_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3171_, v_new_3170_);
                    if v___x_3172_ == 0 {
                        v_isSharedCheck_3182_ = (!lean_is_exclusive(v___x_3157_)) as u8;
                        if v_isSharedCheck_3182_ == 0 {
                            v_unused_3183_ = lean_ctor_get(v___x_3157_, 0);
                            lean_dec(v_unused_3183_);
                            v___x_3174_ = v___x_3157_;
                            v_isShared_3175_ = v_isSharedCheck_3182_;
                            state = 28;
                            continue;
                        } else {
                            lean_dec(v___x_3157_);
                            v___x_3174_ = lean_box(0);
                            v_isShared_3175_ = v_isSharedCheck_3182_;
                            state = 28;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_3163_);
                        lean_dec(v_z_2897_);
                        v_fst_3159_ = v___x_3165_;
                        v_snd_3160_ = v___x_3157_;
                        state = 27;
                        continue;
                    }
                }
                8 => {
                    lean_dec_ref_known(v_v_2898_, 3);
                    v___x_3184_ = lean_st_ref_take(v_a_2899_);
                    v_values_3190_ = lean_ctor_get(v___x_3184_, 0);
                    lean_inc_ref(v_values_3190_);
                    v___x_3191_ = 2;
                    v___x_3192_ = lean_box(0);
                    v___x_3193_ = 0;
                    v___x_3194_ = lean_box((v___x_3193_) as usize);
                    v_old_3195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3190_, v_z_2897_, v___x_3194_);
                    lean_dec(v___x_3194_);
                    v___x_3196_ = (lean_unbox(v_old_3195_) as u8);
                    v_new_3197_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3196_, v___x_3191_);
                    v___x_3198_ = (lean_unbox(v_old_3195_) as u8);
                    lean_dec(v_old_3195_);
                    v___x_3199_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3198_, v_new_3197_);
                    if v___x_3199_ == 0 {
                        v_isSharedCheck_3209_ = (!lean_is_exclusive(v___x_3184_)) as u8;
                        if v_isSharedCheck_3209_ == 0 {
                            v_unused_3210_ = lean_ctor_get(v___x_3184_, 0);
                            lean_dec(v_unused_3210_);
                            v___x_3201_ = v___x_3184_;
                            v_isShared_3202_ = v_isSharedCheck_3209_;
                            state = 31;
                            continue;
                        } else {
                            lean_dec(v___x_3184_);
                            v___x_3201_ = lean_box(0);
                            v_isShared_3202_ = v_isSharedCheck_3209_;
                            state = 31;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_3190_);
                        lean_dec(v_z_2897_);
                        v_fst_3186_ = v___x_3192_;
                        v_snd_3187_ = v___x_3184_;
                        state = 30;
                        continue;
                    }
                }
                7 => {
                    lean_dec_ref_known(v_v_2898_, 2);
                    v___x_3211_ = lean_st_ref_take(v_a_2899_);
                    v_values_3217_ = lean_ctor_get(v___x_3211_, 0);
                    lean_inc_ref(v_values_3217_);
                    v___x_3218_ = 2;
                    v___x_3219_ = lean_box(0);
                    v___x_3220_ = 0;
                    v___x_3221_ = lean_box((v___x_3220_) as usize);
                    v_old_3222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3217_, v_z_2897_, v___x_3221_);
                    lean_dec(v___x_3221_);
                    v___x_3223_ = (lean_unbox(v_old_3222_) as u8);
                    v_new_3224_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3223_, v___x_3218_);
                    v___x_3225_ = (lean_unbox(v_old_3222_) as u8);
                    lean_dec(v_old_3222_);
                    v___x_3226_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3225_, v_new_3224_);
                    if v___x_3226_ == 0 {
                        v_isSharedCheck_3236_ = (!lean_is_exclusive(v___x_3211_)) as u8;
                        if v_isSharedCheck_3236_ == 0 {
                            v_unused_3237_ = lean_ctor_get(v___x_3211_, 0);
                            lean_dec(v_unused_3237_);
                            v___x_3228_ = v___x_3211_;
                            v_isShared_3229_ = v_isSharedCheck_3236_;
                            state = 34;
                            continue;
                        } else {
                            lean_dec(v___x_3211_);
                            v___x_3228_ = lean_box(0);
                            v_isShared_3229_ = v_isSharedCheck_3236_;
                            state = 34;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_3217_);
                        lean_dec(v_z_2897_);
                        v_fst_3213_ = v___x_3219_;
                        v_snd_3214_ = v___x_3211_;
                        state = 33;
                        continue;
                    }
                }
                1 => {
                    v___x_3238_ = lean_st_ref_take(v_a_2899_);
                    v_values_3244_ = lean_ctor_get(v___x_3238_, 0);
                    lean_inc_ref(v_values_3244_);
                    v___x_3245_ = 2;
                    v___x_3246_ = lean_box(0);
                    v___x_3247_ = 0;
                    v___x_3248_ = lean_box((v___x_3247_) as usize);
                    v_old_3249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3244_, v_z_2897_, v___x_3248_);
                    lean_dec(v___x_3248_);
                    v___x_3250_ = (lean_unbox(v_old_3249_) as u8);
                    v_new_3251_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3250_, v___x_3245_);
                    v___x_3252_ = (lean_unbox(v_old_3249_) as u8);
                    lean_dec(v_old_3249_);
                    v___x_3253_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3252_, v_new_3251_);
                    if v___x_3253_ == 0 {
                        v_isSharedCheck_3263_ = (!lean_is_exclusive(v___x_3238_)) as u8;
                        if v_isSharedCheck_3263_ == 0 {
                            v_unused_3264_ = lean_ctor_get(v___x_3238_, 0);
                            lean_dec(v_unused_3264_);
                            v___x_3255_ = v___x_3238_;
                            v_isShared_3256_ = v_isSharedCheck_3263_;
                            state = 37;
                            continue;
                        } else {
                            lean_dec(v___x_3238_);
                            v___x_3255_ = lean_box(0);
                            v_isShared_3256_ = v_isSharedCheck_3263_;
                            state = 37;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_3244_);
                        lean_dec(v_z_2897_);
                        v_fst_3240_ = v___x_3246_;
                        v_snd_3241_ = v___x_3238_;
                        state = 36;
                        continue;
                    }
                }
                0 => {
                    v_isSharedCheck_3297_ = (!lean_is_exclusive(v_v_2898_)) as u8;
                    if v_isSharedCheck_3297_ == 0 {
                        v_unused_3298_ = lean_ctor_get(v_v_2898_, 0);
                        lean_dec(v_unused_3298_);
                        v___x_3266_ = v_v_2898_;
                        v_isShared_3267_ = v_isSharedCheck_3297_;
                        state = 39;
                        continue;
                    } else {
                        lean_dec(v_v_2898_);
                        v___x_3266_ = lean_box(0);
                        v_isShared_3267_ = v_isSharedCheck_3297_;
                        state = 39;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_v_2898_);
                    lean_dec(v_z_2897_);
                    v___x_3299_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue___closed__5);
                    v___x_3300_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(v___x_3299_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
                    return v___x_3300_;
                }
            },
            1 => {
                v___x_2909_ = lean_st_ref_set(v___y_2906_, v_snd_2908_);
                v___x_2910_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2910_, 0, v_fst_2907_);
                return v___x_2910_;
            }
            2 => {
                v___x_2914_ = lean_st_ref_take(v___y_2912_);
                v_values_2915_ = lean_ctor_get(v___x_2914_, 0);
                lean_inc_ref(v_values_2915_);
                v___x_2916_ = lean_box(0);
                v___x_2917_ = 0;
                v___x_2918_ = lean_box((v___x_2917_) as usize);
                v_old_2919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_2915_, v_z_2897_, v___x_2918_);
                lean_dec(v___x_2918_);
                v___x_2920_ = (lean_unbox(v_old_2919_) as u8);
                v_new_2921_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2920_, v___y_2913_);
                v___x_2922_ = (lean_unbox(v_old_2919_) as u8);
                lean_dec(v_old_2919_);
                v___x_2923_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2922_, v_new_2921_);
                if v___x_2923_ == 0 {
                    v_isSharedCheck_2933_ = (!lean_is_exclusive(v___x_2914_)) as u8;
                    if v_isSharedCheck_2933_ == 0 {
                        v_unused_2934_ = lean_ctor_get(v___x_2914_, 0);
                        lean_dec(v_unused_2934_);
                        v___x_2925_ = v___x_2914_;
                        v_isShared_2926_ = v_isSharedCheck_2933_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2914_);
                        v___x_2925_ = lean_box(0);
                        v_isShared_2926_ = v_isSharedCheck_2933_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_values_2915_);
                    lean_dec(v_z_2897_);
                    v___y_2906_ = v___y_2912_;
                    v_fst_2907_ = v___x_2916_;
                    v_snd_2908_ = v___x_2914_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2927_ = 1;
                v___x_2928_ = lean_box((v_new_2921_) as usize);
                v___x_2929_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_2915_, v_z_2897_, v___x_2928_);
                if v_isShared_2926_ == 0 {
                    lean_ctor_set(v___x_2925_, 0, v___x_2929_);
                    v___x_2931_ = v___x_2925_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2929_);
                    v___x_2931_ = v_reuseFailAlloc_2932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_2931_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                v___x_2940_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2940_, 0, v_fst_2937_);
                return v___x_2940_;
            }
            6 => {
                v___x_2945_ = lean_st_ref_set(v___y_2942_, v_snd_2944_);
                v___x_2946_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2946_, 0, v_fst_2943_);
                return v___x_2946_;
            }
            7 => {
                v___x_2950_ = lean_st_ref_set(v_a_2899_, v_snd_2949_);
                v___x_2951_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2951_, 0, v_fst_2948_);
                return v___x_2951_;
            }
            8 => {
                v___x_2954_ = lean_st_ref_take(v_a_2899_);
                v_values_2955_ = lean_ctor_get(v___x_2954_, 0);
                lean_inc_ref(v_values_2955_);
                v___x_2956_ = lean_box(0);
                v___x_2957_ = 0;
                v___x_2958_ = lean_box((v___x_2957_) as usize);
                v_old_2959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_2955_, v_z_2897_, v___x_2958_);
                lean_dec(v___x_2958_);
                v___x_2960_ = (lean_unbox(v_old_2959_) as u8);
                v_new_2961_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_2960_, v___y_2953_);
                v___x_2962_ = (lean_unbox(v_old_2959_) as u8);
                lean_dec(v_old_2959_);
                v___x_2963_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2962_, v_new_2961_);
                if v___x_2963_ == 0 {
                    v_isSharedCheck_2973_ = (!lean_is_exclusive(v___x_2954_)) as u8;
                    if v_isSharedCheck_2973_ == 0 {
                        v_unused_2974_ = lean_ctor_get(v___x_2954_, 0);
                        lean_dec(v_unused_2974_);
                        v___x_2965_ = v___x_2954_;
                        v_isShared_2966_ = v_isSharedCheck_2973_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_2954_);
                        v___x_2965_ = lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2973_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_values_2955_);
                    lean_dec(v_z_2897_);
                    v_fst_2948_ = v___x_2956_;
                    v_snd_2949_ = v___x_2954_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_2967_ = 1;
                v___x_2968_ = lean_box((v_new_2961_) as usize);
                v___x_2969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_2955_, v_z_2897_, v___x_2968_);
                if v_isShared_2966_ == 0 {
                    lean_ctor_set(v___x_2965_, 0, v___x_2969_);
                    v___x_2971_ = v___x_2965_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2969_);
                    v___x_2971_ = v_reuseFailAlloc_2972_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_ctor_set_uint8(
                    v___x_2971_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2967_,
                );
                v_fst_2948_ = v___x_2956_;
                v_snd_2949_ = v___x_2971_;
                state = 7;
                continue;
            }
            11 => {
                v___x_2981_ = lean_st_ref_set(v_a_2899_, v_snd_2980_);
                v___x_2982_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2982_, 0, v_fst_2979_);
                return v___x_2982_;
            }
            12 => {
                v___x_2999_ = 1;
                v___x_3000_ = lean_box((v_new_2993_) as usize);
                v___x_3001_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_2984_, v_z_2897_, v___x_3000_);
                if v_isShared_2998_ == 0 {
                    lean_ctor_set(v___x_2997_, 0, v___x_3001_);
                    v___x_3003_ = v___x_2997_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
                    v___x_3003_ = v_reuseFailAlloc_3004_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                lean_ctor_set_uint8(
                    v___x_3003_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2999_,
                );
                v_fst_2979_ = v___x_2988_;
                v_snd_2980_ = v___x_3003_;
                state = 11;
                continue;
            }
            14 => {
                v___x_3011_ = lean_array_get_size(v_args_3008_);
                lean_dec_ref(v_args_3008_);
                v___x_3012_ = lean_unsigned_to_nat(0);
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
                v___x_3025_ = lean_box(0);
                v___x_3026_ = lean_unsigned_to_nat(1);
                v___x_3027_ = lean_array_get(v___x_3025_, v_args_3023_, v___x_3026_);
                lean_dec_ref(v_args_3023_);
                if lean_obj_tag(v___x_3027_) == 1 {
                    v_fvarId_3028_ = lean_ctor_get(v___x_3027_, 0);
                    lean_inc(v_fvarId_3028_);
                    lean_dec_ref_known(v___x_3027_, 1);
                    v___x_3029_ = lean_st_ref_get(v___y_3024_);
                    v___x_3030_ = lean_st_ref_take(v___y_3024_);
                    v_values_3031_ = lean_ctor_get(v___x_3029_, 0);
                    lean_inc_ref(v_values_3031_);
                    lean_dec(v___x_3029_);
                    v_values_3032_ = lean_ctor_get(v___x_3030_, 0);
                    lean_inc_ref(v_values_3032_);
                    v___x_3033_ = 0;
                    v___x_3034_ = lean_box((v___x_3033_) as usize);
                    v___x_3035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3031_, v_fvarId_3028_, v___x_3034_);
                    lean_dec(v___x_3034_);
                    lean_dec(v_fvarId_3028_);
                    lean_dec_ref(v_values_3031_);
                    v___x_3036_ = lean_box(0);
                    v___x_3037_ = lean_box((v___x_3033_) as usize);
                    v_old_3038_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3032_, v_z_2897_, v___x_3037_);
                    lean_dec(v___x_3037_);
                    v___x_3039_ = (lean_unbox(v_old_3038_) as u8);
                    v___x_3040_ = (lean_unbox(v___x_3035_) as u8);
                    lean_dec(v___x_3035_);
                    v_new_3041_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3039_, v___x_3040_);
                    v___x_3042_ = (lean_unbox(v_old_3038_) as u8);
                    lean_dec(v_old_3038_);
                    v___x_3043_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3042_, v_new_3041_);
                    if v___x_3043_ == 0 {
                        v_isSharedCheck_3052_ = (!lean_is_exclusive(v___x_3030_)) as u8;
                        if v_isSharedCheck_3052_ == 0 {
                            v_unused_3053_ = lean_ctor_get(v___x_3030_, 0);
                            lean_dec(v_unused_3053_);
                            v___x_3045_ = v___x_3030_;
                            v_isShared_3046_ = v_isSharedCheck_3052_;
                            state = 16;
                            continue;
                        } else {
                            lean_dec(v___x_3030_);
                            v___x_3045_ = lean_box(0);
                            v_isShared_3046_ = v_isSharedCheck_3052_;
                            state = 16;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_3032_);
                        lean_dec(v_z_2897_);
                        v___y_2936_ = v___y_3024_;
                        v_fst_2937_ = v___x_3036_;
                        v_snd_2938_ = v___x_3030_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3027_);
                    lean_dec(v_z_2897_);
                    v___x_3054_ = lean_box(0);
                    v___x_3055_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3055_, 0, v___x_3054_);
                    return v___x_3055_;
                }
            }
            16 => {
                v___x_3047_ = lean_box((v_new_3041_) as usize);
                v___x_3048_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3032_, v_z_2897_, v___x_3047_);
                if v_isShared_3046_ == 0 {
                    lean_ctor_set(v___x_3045_, 0, v___x_3048_);
                    v___x_3050_ = v___x_3045_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
                    v___x_3050_ = v_reuseFailAlloc_3051_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                lean_ctor_set_uint8(
                    v___x_3050_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3021_,
                );
                v___y_2936_ = v___y_3024_;
                v_fst_2937_ = v___x_3036_;
                v_snd_2938_ = v___x_3050_;
                state = 5;
                continue;
            }
            18 => {
                v___x_3062_ = lean_box(0);
                v___x_3063_ = lean_unsigned_to_nat(2);
                v___x_3064_ = lean_array_get(v___x_3062_, v_args_3008_, v___x_3063_);
                lean_dec_ref(v_args_3008_);
                if lean_obj_tag(v___x_3064_) == 1 {
                    v_fvarId_3065_ = lean_ctor_get(v___x_3064_, 0);
                    lean_inc(v_fvarId_3065_);
                    lean_dec_ref_known(v___x_3064_, 1);
                    v___x_3066_ = lean_st_ref_get(v___y_3061_);
                    v___x_3067_ = lean_st_ref_take(v___y_3061_);
                    v_values_3068_ = lean_ctor_get(v___x_3066_, 0);
                    lean_inc_ref(v_values_3068_);
                    lean_dec(v___x_3066_);
                    v_values_3069_ = lean_ctor_get(v___x_3067_, 0);
                    lean_inc_ref(v_values_3069_);
                    v___x_3070_ = 0;
                    v___x_3071_ = lean_box((v___x_3070_) as usize);
                    v___x_3072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3068_, v_fvarId_3065_, v___x_3071_);
                    lean_dec(v___x_3071_);
                    lean_dec(v_fvarId_3065_);
                    lean_dec_ref(v_values_3068_);
                    v___x_3073_ = lean_box(0);
                    v___x_3074_ = lean_box((v___x_3070_) as usize);
                    v_old_3075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3069_, v_z_2897_, v___x_3074_);
                    lean_dec(v___x_3074_);
                    v___x_3076_ = (lean_unbox(v_old_3075_) as u8);
                    v___x_3077_ = (lean_unbox(v___x_3072_) as u8);
                    lean_dec(v___x_3072_);
                    v_new_3078_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3076_, v___x_3077_);
                    v___x_3079_ = (lean_unbox(v_old_3075_) as u8);
                    lean_dec(v_old_3075_);
                    v___x_3080_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3079_, v_new_3078_);
                    if v___x_3080_ == 0 {
                        v_isSharedCheck_3089_ = (!lean_is_exclusive(v___x_3067_)) as u8;
                        if v_isSharedCheck_3089_ == 0 {
                            v_unused_3090_ = lean_ctor_get(v___x_3067_, 0);
                            lean_dec(v_unused_3090_);
                            v___x_3082_ = v___x_3067_;
                            v_isShared_3083_ = v_isSharedCheck_3089_;
                            state = 19;
                            continue;
                        } else {
                            lean_dec(v___x_3067_);
                            v___x_3082_ = lean_box(0);
                            v_isShared_3083_ = v_isSharedCheck_3089_;
                            state = 19;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_3069_);
                        lean_dec(v_z_2897_);
                        v___y_2942_ = v___y_3061_;
                        v_fst_2943_ = v___x_3073_;
                        v_snd_2944_ = v___x_3067_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3064_);
                    lean_dec(v_z_2897_);
                    v___x_3091_ = lean_box(0);
                    v___x_3092_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3092_, 0, v___x_3091_);
                    return v___x_3092_;
                }
            }
            19 => {
                v___x_3084_ = lean_box((v_new_3078_) as usize);
                v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3069_, v_z_2897_, v___x_3084_);
                if v_isShared_3083_ == 0 {
                    lean_ctor_set(v___x_3082_, 0, v___x_3085_);
                    v___x_3087_ = v___x_3082_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
                    v___x_3087_ = v_reuseFailAlloc_3088_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                lean_ctor_set_uint8(
                    v___x_3087_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                v___x_3119_ = lean_box((v_new_3113_) as usize);
                lean_inc(v_z_2897_);
                v___x_3120_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3105_, v_z_2897_, v___x_3119_);
                if v_isShared_3118_ == 0 {
                    lean_ctor_set(v___x_3117_, 0, v___x_3120_);
                    v___x_3122_ = v___x_3117_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                lean_ctor_set_uint8(
                    v___x_3122_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3059_,
                );
                v_snd_3102_ = v___x_3122_;
                state = 21;
                continue;
            }
            24 => {
                v___x_3134_ = lean_st_ref_set(v_a_2899_, v_snd_3133_);
                v___x_3135_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3135_, 0, v_fst_3132_);
                return v___x_3135_;
            }
            25 => {
                v___x_3149_ = 1;
                v___x_3150_ = lean_box((v_new_3143_) as usize);
                v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3136_, v_z_2897_, v___x_3150_);
                if v_isShared_3148_ == 0 {
                    lean_ctor_set(v___x_3147_, 0, v___x_3151_);
                    v___x_3153_ = v___x_3147_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
                    v___x_3153_ = v_reuseFailAlloc_3154_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                lean_ctor_set_uint8(
                    v___x_3153_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3149_,
                );
                v_fst_3132_ = v___x_3138_;
                v_snd_3133_ = v___x_3153_;
                state = 24;
                continue;
            }
            27 => {
                v___x_3161_ = lean_st_ref_set(v_a_2899_, v_snd_3160_);
                v___x_3162_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3162_, 0, v_fst_3159_);
                return v___x_3162_;
            }
            28 => {
                v___x_3176_ = 1;
                v___x_3177_ = lean_box((v_new_3170_) as usize);
                v___x_3178_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3163_, v_z_2897_, v___x_3177_);
                if v_isShared_3175_ == 0 {
                    lean_ctor_set(v___x_3174_, 0, v___x_3178_);
                    v___x_3180_ = v___x_3174_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
                    v___x_3180_ = v_reuseFailAlloc_3181_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                lean_ctor_set_uint8(
                    v___x_3180_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3176_,
                );
                v_fst_3159_ = v___x_3165_;
                v_snd_3160_ = v___x_3180_;
                state = 27;
                continue;
            }
            30 => {
                v___x_3188_ = lean_st_ref_set(v_a_2899_, v_snd_3187_);
                v___x_3189_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3189_, 0, v_fst_3186_);
                return v___x_3189_;
            }
            31 => {
                v___x_3203_ = 1;
                v___x_3204_ = lean_box((v_new_3197_) as usize);
                v___x_3205_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3190_, v_z_2897_, v___x_3204_);
                if v_isShared_3202_ == 0 {
                    lean_ctor_set(v___x_3201_, 0, v___x_3205_);
                    v___x_3207_ = v___x_3201_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
                    v___x_3207_ = v_reuseFailAlloc_3208_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                lean_ctor_set_uint8(
                    v___x_3207_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3203_,
                );
                v_fst_3186_ = v___x_3192_;
                v_snd_3187_ = v___x_3207_;
                state = 30;
                continue;
            }
            33 => {
                v___x_3215_ = lean_st_ref_set(v_a_2899_, v_snd_3214_);
                v___x_3216_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3216_, 0, v_fst_3213_);
                return v___x_3216_;
            }
            34 => {
                v___x_3230_ = 1;
                v___x_3231_ = lean_box((v_new_3224_) as usize);
                v___x_3232_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3217_, v_z_2897_, v___x_3231_);
                if v_isShared_3229_ == 0 {
                    lean_ctor_set(v___x_3228_, 0, v___x_3232_);
                    v___x_3234_ = v___x_3228_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
                    v___x_3234_ = v_reuseFailAlloc_3235_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                lean_ctor_set_uint8(
                    v___x_3234_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3230_,
                );
                v_fst_3213_ = v___x_3219_;
                v_snd_3214_ = v___x_3234_;
                state = 33;
                continue;
            }
            36 => {
                v___x_3242_ = lean_st_ref_set(v_a_2899_, v_snd_3241_);
                v___x_3243_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3243_, 0, v_fst_3240_);
                return v___x_3243_;
            }
            37 => {
                v___x_3257_ = 1;
                v___x_3258_ = lean_box((v_new_3251_) as usize);
                v___x_3259_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3244_, v_z_2897_, v___x_3258_);
                if v_isShared_3256_ == 0 {
                    lean_ctor_set(v___x_3255_, 0, v___x_3259_);
                    v___x_3261_ = v___x_3255_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                lean_ctor_set_uint8(
                    v___x_3261_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3257_,
                );
                v_fst_3240_ = v___x_3246_;
                v_snd_3241_ = v___x_3261_;
                state = 36;
                continue;
            }
            39 => {
                v___x_3268_ = lean_st_ref_take(v_a_2899_);
                v_values_3276_ = lean_ctor_get(v___x_3268_, 0);
                lean_inc_ref(v_values_3276_);
                v___x_3277_ = 2;
                v___x_3278_ = lean_box(0);
                v___x_3279_ = 0;
                v___x_3280_ = lean_box((v___x_3279_) as usize);
                v_old_3281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3276_, v_z_2897_, v___x_3280_);
                lean_dec(v___x_3280_);
                v___x_3282_ = (lean_unbox(v_old_3281_) as u8);
                v_new_3283_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3282_, v___x_3277_);
                v___x_3284_ = (lean_unbox(v_old_3281_) as u8);
                lean_dec(v_old_3281_);
                v___x_3285_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3284_, v_new_3283_);
                if v___x_3285_ == 0 {
                    v_isSharedCheck_3295_ = (!lean_is_exclusive(v___x_3268_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v_unused_3296_ = lean_ctor_get(v___x_3268_, 0);
                        lean_dec(v_unused_3296_);
                        v___x_3287_ = v___x_3268_;
                        v_isShared_3288_ = v_isSharedCheck_3295_;
                        state = 42;
                        continue;
                    } else {
                        lean_dec(v___x_3268_);
                        v___x_3287_ = lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3295_;
                        state = 42;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_values_3276_);
                    lean_dec(v_z_2897_);
                    v_fst_3270_ = v___x_3278_;
                    v_snd_3271_ = v___x_3268_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v___x_3272_ = lean_st_ref_set(v_a_2899_, v_snd_3271_);
                if v_isShared_3267_ == 0 {
                    lean_ctor_set(v___x_3266_, 0, v_fst_3270_);
                    v___x_3274_ = v___x_3266_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_fst_3270_);
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
                v___x_3290_ = lean_box((v_new_3283_) as usize);
                v___x_3291_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3276_, v_z_2897_, v___x_3290_);
                if v_isShared_3288_ == 0 {
                    lean_ctor_set(v___x_3287_, 0, v___x_3291_);
                    v___x_3293_ = v___x_3287_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
                    v___x_3293_ = v_reuseFailAlloc_3294_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                lean_ctor_set_uint8(
                    v___x_3293_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_z_3301_: *mut LeanObject,
    mut v_v_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
    mut v_a_3304_: *mut LeanObject,
    mut v_a_3305_: *mut LeanObject,
    mut v_a_3306_: *mut LeanObject,
    mut v_a_3307_: *mut LeanObject,
    mut v_a_3308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3309_: *mut LeanObject = core::ptr::null_mut();
    v_res_3309_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue(v_z_3301_, v_v_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
    lean_dec(v_a_3307_);
    lean_dec_ref(v_a_3306_);
    lean_dec(v_a_3305_);
    lean_dec_ref(v_a_3304_);
    lean_dec(v_a_3303_);
    return v_res_3309_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0(
    mut v_00_u03b2_3310_: *mut LeanObject,
    mut v_m_3311_: *mut LeanObject,
    mut v_a_3312_: *mut LeanObject,
    mut v_fallback_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_m_3311_, v_a_3312_, v_fallback_3313_);
    return v___x_3314_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___boxed(
    mut v_00_u03b2_3315_: *mut LeanObject,
    mut v_m_3316_: *mut LeanObject,
    mut v_a_3317_: *mut LeanObject,
    mut v_fallback_3318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3319_: *mut LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0(v_00_u03b2_3315_, v_m_3316_, v_a_3317_, v_fallback_3318_);
    lean_dec(v_fallback_3318_);
    lean_dec(v_a_3317_);
    lean_dec_ref(v_m_3316_);
    return v_res_3319_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1(
    mut v_00_u03b2_3320_: *mut LeanObject,
    mut v_m_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
    mut v_b_3323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_m_3321_, v_a_3322_, v_b_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0(
    mut v_00_u03b2_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
    mut v_fallback_3327_: *mut LeanObject,
    mut v_x_3328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    v___x_3329_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___redArg(v_a_3326_, v_fallback_3327_, v_x_3328_);
    return v___x_3329_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0___boxed(
    mut v_00_u03b2_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
    mut v_fallback_3332_: *mut LeanObject,
    mut v_x_3333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3334_: *mut LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0_spec__0(v_00_u03b2_3330_, v_a_3331_, v_fallback_3332_, v_x_3333_);
    lean_dec(v_x_3333_);
    lean_dec(v_fallback_3332_);
    lean_dec(v_a_3331_);
    return v_res_3334_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2(
    mut v_00_u03b2_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
    mut v_x_3337_: *mut LeanObject,
) -> u8 {
    let mut v___x_3338_: u8 = 0;
    v___x_3338_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___redArg(v_a_3336_, v_x_3337_);
    return v___x_3338_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2___boxed(
    mut v_00_u03b2_3339_: *mut LeanObject,
    mut v_a_3340_: *mut LeanObject,
    mut v_x_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3342_: u8 = 0;
    let mut v_r_3343_: *mut LeanObject = core::ptr::null_mut();
    v_res_3342_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__2(v_00_u03b2_3339_, v_a_3340_, v_x_3341_);
    lean_dec(v_x_3341_);
    lean_dec(v_a_3340_);
    v_r_3343_ = lean_box((v_res_3342_) as usize);
    return v_r_3343_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3(
    mut v_00_u03b2_3344_: *mut LeanObject,
    mut v_data_3345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    v___x_3346_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3___redArg(v_data_3345_);
    return v___x_3346_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4(
    mut v_00_u03b2_3347_: *mut LeanObject,
    mut v_a_3348_: *mut LeanObject,
    mut v_b_3349_: *mut LeanObject,
    mut v_x_3350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    v___x_3351_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__4___redArg(v_a_3348_, v_b_3349_, v_x_3350_);
    return v___x_3351_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5(
    mut v_00_u03b2_3352_: *mut LeanObject,
    mut v_i_3353_: *mut LeanObject,
    mut v_source_3354_: *mut LeanObject,
    mut v_target_3355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    v___x_3356_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5___redArg(v_i_3353_, v_source_3354_, v_target_3355_);
    return v___x_3356_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5_spec__6(
    mut v_00_u03b2_3357_: *mut LeanObject,
    mut v_x_3358_: *mut LeanObject,
    mut v_x_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    v___x_3360_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1_spec__3_spec__5_spec__6___redArg(v_x_3358_, v_x_3359_);
    return v___x_3360_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg(
    mut v_alt_3361_: *mut LeanObject,
    mut v_f_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_alt_3361_) {
        0 => {
            let mut v_code_3369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
            v_code_3369_ = lean_ctor_get(v_alt_3361_, 2);
            lean_inc_ref(v_code_3369_);
            lean_dec_ref_known(v_alt_3361_, 3);
            lean_inc(v___y_3367_);
            lean_inc_ref(v___y_3366_);
            lean_inc(v___y_3365_);
            lean_inc_ref(v___y_3364_);
            lean_inc(v___y_3363_);
            v___x_3370_ = lean_apply_7(
                v_f_3362_,
                v_code_3369_,
                v___y_3363_,
                v___y_3364_,
                v___y_3365_,
                v___y_3366_,
                v___y_3367_,
                lean_box(0),
            );
            return v___x_3370_;
        }
        1 => {
            let mut v_code_3371_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
            v_code_3371_ = lean_ctor_get(v_alt_3361_, 1);
            lean_inc_ref(v_code_3371_);
            lean_dec_ref_known(v_alt_3361_, 2);
            lean_inc(v___y_3367_);
            lean_inc_ref(v___y_3366_);
            lean_inc(v___y_3365_);
            lean_inc_ref(v___y_3364_);
            lean_inc(v___y_3363_);
            v___x_3372_ = lean_apply_7(
                v_f_3362_,
                v_code_3371_,
                v___y_3363_,
                v___y_3364_,
                v___y_3365_,
                v___y_3366_,
                v___y_3367_,
                lean_box(0),
            );
            return v___x_3372_;
        }
        _ => {
            let mut v_code_3373_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
            v_code_3373_ = lean_ctor_get(v_alt_3361_, 0);
            lean_inc_ref(v_code_3373_);
            lean_dec_ref_known(v_alt_3361_, 1);
            lean_inc(v___y_3367_);
            lean_inc_ref(v___y_3366_);
            lean_inc(v___y_3365_);
            lean_inc_ref(v___y_3364_);
            lean_inc(v___y_3363_);
            v___x_3374_ = lean_apply_7(
                v_f_3362_,
                v_code_3373_,
                v___y_3363_,
                v___y_3364_,
                v___y_3365_,
                v___y_3366_,
                v___y_3367_,
                lean_box(0),
            );
            return v___x_3374_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg___boxed(
    mut v_alt_3375_: *mut LeanObject,
    mut v_f_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3383_: *mut LeanObject = core::ptr::null_mut();
    v_res_3383_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg(v_alt_3375_, v_f_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
    lean_dec(v___y_3381_);
    lean_dec_ref(v___y_3380_);
    lean_dec(v___y_3379_);
    lean_dec_ref(v___y_3378_);
    lean_dec(v___y_3377_);
    return v_res_3383_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0(
    mut v_pu_3384_: u8,
    mut v_alt_3385_: *mut LeanObject,
    mut v_f_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    v___x_3393_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg(v_alt_3385_, v_f_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    return v___x_3393_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___boxed(
    mut v_pu_3394_: *mut LeanObject,
    mut v_alt_3395_: *mut LeanObject,
    mut v_f_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3403_: u8 = 0;
    let mut v_res_3404_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3403_ = (lean_unbox(v_pu_3394_) as u8);
    v_res_3404_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0(v_pu_boxed_3403_, v_alt_3395_, v_f_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
    lean_dec(v___y_3401_);
    lean_dec_ref(v___y_3400_);
    lean_dec(v___y_3399_);
    lean_dec_ref(v___y_3398_);
    lean_dec(v___y_3397_);
    return v_res_3404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg(
    mut v_as_3405_: *mut LeanObject,
    mut v_sz_3406_: usize,
    mut v_i_3407_: usize,
    mut v_b_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: usize = 0;
    let mut v___x_3414_: usize = 0;
    let mut v___x_3416_: u8 = 0;
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: u8 = 0;
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v_a_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: u8 = 0;
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: u8 = 0;
    let mut v_new_3448_: u8 = 0;
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: u8 = 0;
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut v_unused_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_unused_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3416_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
                if v___x_3416_ == 0 {
                    v___x_3417_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3417_, 0, v_b_3408_);
                    return v___x_3417_;
                } else {
                    v_array_3418_ = lean_ctor_get(v_b_3408_, 0);
                    v_start_3419_ = lean_ctor_get(v_b_3408_, 1);
                    v_stop_3420_ = lean_ctor_get(v_b_3408_, 2);
                    v___x_3421_ = lean_nat_dec_lt(v_start_3419_, v_stop_3420_);
                    if v___x_3421_ == 0 {
                        v___x_3422_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3422_, 0, v_b_3408_);
                        return v___x_3422_;
                    } else {
                        lean_inc(v_stop_3420_);
                        lean_inc(v_start_3419_);
                        lean_inc_ref(v_array_3418_);
                        v_isSharedCheck_3462_ = (!lean_is_exclusive(v_b_3408_)) as u8;
                        if v_isSharedCheck_3462_ == 0 {
                            v_unused_3463_ = lean_ctor_get(v_b_3408_, 2);
                            lean_dec(v_unused_3463_);
                            v_unused_3464_ = lean_ctor_get(v_b_3408_, 1);
                            lean_dec(v_unused_3464_);
                            v_unused_3465_ = lean_ctor_get(v_b_3408_, 0);
                            lean_dec(v_unused_3465_);
                            v___x_3424_ = v_b_3408_;
                            v_isShared_3425_ = v_isSharedCheck_3462_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_b_3408_);
                            v___x_3424_ = lean_box(0);
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
                v___x_3428_ = lean_unsigned_to_nat(1);
                v___x_3429_ = lean_nat_add(v_start_3419_, v___x_3428_);
                lean_dec(v_start_3419_);
                if v_isShared_3425_ == 0 {
                    lean_ctor_set(v___x_3424_, 1, v___x_3429_);
                    v___x_3431_ = v___x_3424_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_array_3418_);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3429_);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_stop_3420_);
                    v___x_3431_ = v_reuseFailAlloc_3461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_a_3426_) == 1 {
                    v_fvarId_3432_ = lean_ctor_get(v_a_3426_, 0);
                    v___x_3433_ = lean_st_ref_get(v___y_3409_);
                    v___x_3434_ = lean_st_ref_take(v___y_3409_);
                    v_values_3438_ = lean_ctor_get(v___x_3433_, 0);
                    lean_inc_ref(v_values_3438_);
                    lean_dec(v___x_3433_);
                    v_fvarId_3439_ = lean_ctor_get(v___x_3427_, 0);
                    lean_inc(v_fvarId_3439_);
                    lean_dec(v___x_3427_);
                    v_values_3440_ = lean_ctor_get(v___x_3434_, 0);
                    lean_inc_ref(v_values_3440_);
                    v___x_3441_ = 0;
                    v___x_3442_ = lean_box((v___x_3441_) as usize);
                    v___x_3443_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3438_, v_fvarId_3432_, v___x_3442_);
                    lean_dec(v___x_3442_);
                    lean_dec_ref(v_values_3438_);
                    v___x_3444_ = lean_box((v___x_3441_) as usize);
                    v_old_3445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__0___redArg(v_values_3440_, v_fvarId_3439_, v___x_3444_);
                    lean_dec(v___x_3444_);
                    v___x_3446_ = (lean_unbox(v_old_3445_) as u8);
                    v___x_3447_ = (lean_unbox(v___x_3443_) as u8);
                    lean_dec(v___x_3443_);
                    v_new_3448_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_join(v___x_3446_, v___x_3447_);
                    v___x_3449_ = (lean_unbox(v_old_3445_) as u8);
                    lean_dec(v_old_3445_);
                    v___x_3450_ =
                        l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_3449_, v_new_3448_);
                    if v___x_3450_ == 0 {
                        v_isSharedCheck_3459_ = (!lean_is_exclusive(v___x_3434_)) as u8;
                        if v_isSharedCheck_3459_ == 0 {
                            v_unused_3460_ = lean_ctor_get(v___x_3434_, 0);
                            lean_dec(v_unused_3460_);
                            v___x_3452_ = v___x_3434_;
                            v_isShared_3453_ = v_isSharedCheck_3459_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_3434_);
                            v___x_3452_ = lean_box(0);
                            v_isShared_3453_ = v_isSharedCheck_3459_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_values_3440_);
                        lean_dec(v_fvarId_3439_);
                        v_snd_3436_ = v___x_3434_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3427_);
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
                v___x_3454_ = lean_box((v_new_3448_) as usize);
                v___x_3455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3440_, v_fvarId_3439_, v___x_3454_);
                if v_isShared_3453_ == 0 {
                    lean_ctor_set(v___x_3452_, 0, v___x_3455_);
                    v___x_3457_ = v___x_3452_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
                    v___x_3457_ = v_reuseFailAlloc_3458_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_ctor_set_uint8(
                    v___x_3457_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_as_3466_: *mut LeanObject,
    mut v_sz_3467_: *mut LeanObject,
    mut v_i_3468_: *mut LeanObject,
    mut v_b_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
    mut v___y_3471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3472_: usize = 0;
    let mut v_i_boxed_3473_: usize = 0;
    let mut v_res_3474_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3472_ = lean_unbox_usize(v_sz_3467_);
    lean_dec(v_sz_3467_);
    v_i_boxed_3473_ = lean_unbox_usize(v_i_3468_);
    lean_dec(v_i_3468_);
    v_res_3474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg(v_as_3466_, v_sz_boxed_3472_, v_i_boxed_3473_, v_b_3469_, v___y_3470_);
    lean_dec(v___y_3470_);
    lean_dec_ref(v_as_3466_);
    return v_res_3474_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg(
    mut v_m_3475_: *mut LeanObject,
    mut v_a_3476_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: u8 = 0;
    v_buckets_3477_ = lean_ctor_get(v_m_3475_, 1);
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
    mut v_m_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3495_: u8 = 0;
    let mut v_r_3496_: *mut LeanObject = core::ptr::null_mut();
    v_res_3495_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg(v_m_3493_, v_a_3494_);
    lean_dec(v_a_3494_);
    lean_dec_ref(v_m_3493_);
    v_r_3496_ = lean_box((v_res_3495_) as usize);
    return v_r_3496_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg(
    mut v_as_3497_: *mut LeanObject,
    mut v_sz_3498_: usize,
    mut v_i_3499_: usize,
    mut v_b_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: usize = 0;
    let mut v___x_3506_: usize = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_3514_: u8 = 0;
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: u8 = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modified_3520_: u8 = 0;
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut LeanObject = core::ptr::null_mut();
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
                    v___x_3509_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3509_, 0, v_b_3500_);
                    return v___x_3509_;
                } else {
                    v___x_3510_ = lean_st_ref_get(v___y_3501_);
                    v_values_3511_ = lean_ctor_get(v___x_3510_, 0);
                    lean_inc_ref(v_values_3511_);
                    lean_dec(v___x_3510_);
                    v_a_3512_ = lean_array_uget_borrowed(v_as_3497_, v_i_3499_);
                    v_fvarId_3513_ = lean_ctor_get(v_a_3512_, 0);
                    v_borrow_3514_ = lean_ctor_get_uint8(
                        v_a_3512_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v___x_3515_ = lean_box(0);
                    v___x_3531_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg(v_values_3511_, v_fvarId_3513_);
                    lean_dec_ref(v_values_3511_);
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
                v_values_3519_ = lean_ctor_get(v___x_3518_, 0);
                v_modified_3520_ = lean_ctor_get_uint8(
                    v___x_3518_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3530_ = (!lean_is_exclusive(v___x_3518_)) as u8;
                if v_isSharedCheck_3530_ == 0 {
                    v___x_3522_ = v___x_3518_;
                    v_isShared_3523_ = v_isSharedCheck_3530_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_values_3519_);
                    lean_dec(v___x_3518_);
                    v___x_3522_ = lean_box(0);
                    v_isShared_3523_ = v_isSharedCheck_3530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3524_ = lean_box((v___y_3517_) as usize);
                lean_inc(v_fvarId_3513_);
                v___x_3525_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3519_, v_fvarId_3513_, v___x_3524_);
                if v_isShared_3523_ == 0 {
                    lean_ctor_set(v___x_3522_, 0, v___x_3525_);
                    v___x_3527_ = v___x_3522_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3525_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3529_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_as_3534_: *mut LeanObject,
    mut v_sz_3535_: *mut LeanObject,
    mut v_i_3536_: *mut LeanObject,
    mut v_b_3537_: *mut LeanObject,
    mut v___y_3538_: *mut LeanObject,
    mut v___y_3539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3540_: usize = 0;
    let mut v_i_boxed_3541_: usize = 0;
    let mut v_res_3542_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3540_ = lean_unbox_usize(v_sz_3535_);
    lean_dec(v_sz_3535_);
    v_i_boxed_3541_ = lean_unbox_usize(v_i_3536_);
    lean_dec(v_i_3536_);
    v_res_3542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg(v_as_3534_, v_sz_boxed_3540_, v_i_boxed_3541_, v_b_3537_, v___y_3538_);
    lean_dec(v___y_3538_);
    lean_dec_ref(v_as_3534_);
    return v_res_3542_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1()
-> *mut LeanObject {
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    v___x_3544_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_3545_ = lean_unsigned_to_nat(58);
    v___x_3546_ = lean_unsigned_to_nat(96);
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
-> *mut LeanObject {
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    v___x_3550_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_3551_ = lean_unsigned_to_nat(61);
    v___x_3552_ = lean_unsigned_to_nat(104);
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
    mut v_code_3556_: *mut LeanObject,
    mut v_a_3557_: *mut LeanObject,
    mut v_a_3558_: *mut LeanObject,
    mut v_a_3559_: *mut LeanObject,
    mut v_a_3560_: *mut LeanObject,
    mut v_a_3561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3574_: usize = 0;
    let mut v___x_3575_: usize = 0;
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: u8 = 0;
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3589_: usize = 0;
    let mut v___x_3590_: usize = 0;
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3599_: u8 = 0;
    let mut v_unused_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v_cases_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v_alts_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: u8 = 0;
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: usize = 0;
    let mut v___x_3636_: usize = 0;
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: usize = 0;
    let mut v___x_3639_: usize = 0;
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v_unused_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3658_: u8 = 0;
    let mut v_unused_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_3556_) {
                0 => {
                    v_decl_3563_ = lean_ctor_get(v_code_3556_, 0);
                    lean_inc_ref(v_decl_3563_);
                    v_k_3564_ = lean_ctor_get(v_code_3556_, 1);
                    lean_inc_ref(v_k_3564_);
                    lean_dec_ref_known(v_code_3556_, 2);
                    v_fvarId_3565_ = lean_ctor_get(v_decl_3563_, 0);
                    lean_inc(v_fvarId_3565_);
                    v_value_3566_ = lean_ctor_get(v_decl_3563_, 3);
                    lean_inc(v_value_3566_);
                    lean_dec_ref(v_decl_3563_);
                    v___x_3567_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue(v_fvarId_3565_, v_value_3566_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                    if lean_obj_tag(v___x_3567_) == 0 {
                        lean_dec_ref_known(v___x_3567_, 1);
                        v_code_3556_ = v_k_3564_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_3564_);
                        return v___x_3567_;
                    }
                }
                2 => {
                    v_decl_3569_ = lean_ctor_get(v_code_3556_, 0);
                    lean_inc_ref(v_decl_3569_);
                    v_k_3570_ = lean_ctor_get(v_code_3556_, 1);
                    lean_inc_ref(v_k_3570_);
                    lean_dec_ref_known(v_code_3556_, 2);
                    v_params_3571_ = lean_ctor_get(v_decl_3569_, 2);
                    lean_inc_ref(v_params_3571_);
                    v_value_3572_ = lean_ctor_get(v_decl_3569_, 4);
                    lean_inc_ref(v_value_3572_);
                    lean_dec_ref(v_decl_3569_);
                    v___x_3573_ = lean_box(0);
                    v_sz_3574_ = lean_array_size(v_params_3571_);
                    v___x_3575_ = 0usize;
                    v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg(v_params_3571_, v_sz_3574_, v___x_3575_, v___x_3573_, v_a_3557_);
                    lean_dec_ref(v_params_3571_);
                    if lean_obj_tag(v___x_3576_) == 0 {
                        lean_dec_ref_known(v___x_3576_, 1);
                        v___x_3577_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode(v_k_3570_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                        if lean_obj_tag(v___x_3577_) == 0 {
                            lean_dec_ref_known(v___x_3577_, 1);
                            v_code_3556_ = v_value_3572_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_value_3572_);
                            return v___x_3577_;
                        }
                    } else {
                        lean_dec_ref(v_value_3572_);
                        lean_dec_ref(v_k_3570_);
                        return v___x_3576_;
                    }
                }
                3 => {
                    v_fvarId_3579_ = lean_ctor_get(v_code_3556_, 0);
                    lean_inc(v_fvarId_3579_);
                    v_args_3580_ = lean_ctor_get(v_code_3556_, 1);
                    lean_inc_ref(v_args_3580_);
                    lean_dec_ref_known(v_code_3556_, 2);
                    v___x_3581_ = 1;
                    v___x_3582_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
                        v___x_3581_,
                        v_fvarId_3579_,
                        v_a_3559_,
                    );
                    lean_dec(v_fvarId_3579_);
                    if lean_obj_tag(v___x_3582_) == 0 {
                        v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
                        lean_inc(v_a_3583_);
                        lean_dec_ref_known(v___x_3582_, 1);
                        if lean_obj_tag(v_a_3583_) == 1 {
                            v_val_3584_ = lean_ctor_get(v_a_3583_, 0);
                            lean_inc(v_val_3584_);
                            lean_dec_ref_known(v_a_3583_, 1);
                            v_params_3585_ = lean_ctor_get(v_val_3584_, 2);
                            lean_inc_ref(v_params_3585_);
                            lean_dec(v_val_3584_);
                            v___x_3586_ = lean_unsigned_to_nat(0);
                            v___x_3587_ = lean_array_get_size(v_params_3585_);
                            v___x_3588_ = l_Array_toSubarray___redArg(
                                v_params_3585_,
                                v___x_3586_,
                                v___x_3587_,
                            );
                            v_sz_3589_ = lean_array_size(v_args_3580_);
                            v___x_3590_ = 0usize;
                            v___x_3591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg(v_args_3580_, v_sz_3589_, v___x_3590_, v___x_3588_, v_a_3557_);
                            lean_dec_ref(v_args_3580_);
                            if lean_obj_tag(v___x_3591_) == 0 {
                                v_isSharedCheck_3599_ = (!lean_is_exclusive(v___x_3591_)) as u8;
                                if v_isSharedCheck_3599_ == 0 {
                                    v_unused_3600_ = lean_ctor_get(v___x_3591_, 0);
                                    lean_dec(v_unused_3600_);
                                    v___x_3593_ = v___x_3591_;
                                    v_isShared_3594_ = v_isSharedCheck_3599_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_3591_);
                                    v___x_3593_ = lean_box(0);
                                    v_isShared_3594_ = v_isSharedCheck_3599_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3601_ = lean_ctor_get(v___x_3591_, 0);
                                v_isSharedCheck_3608_ = (!lean_is_exclusive(v___x_3591_)) as u8;
                                if v_isSharedCheck_3608_ == 0 {
                                    v___x_3603_ = v___x_3591_;
                                    v_isShared_3604_ = v_isSharedCheck_3608_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_3601_);
                                    lean_dec(v___x_3591_);
                                    v___x_3603_ = lean_box(0);
                                    v_isShared_3604_ = v_isSharedCheck_3608_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3583_);
                            lean_dec_ref(v_args_3580_);
                            v___x_3609_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__1);
                            v___x_3610_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(v___x_3609_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                            return v___x_3610_;
                        }
                    } else {
                        lean_dec_ref(v_args_3580_);
                        v_a_3611_ = lean_ctor_get(v___x_3582_, 0);
                        v_isSharedCheck_3618_ = (!lean_is_exclusive(v___x_3582_)) as u8;
                        if v_isSharedCheck_3618_ == 0 {
                            v___x_3613_ = v___x_3582_;
                            v_isShared_3614_ = v_isSharedCheck_3618_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3611_);
                            lean_dec(v___x_3582_);
                            v___x_3613_ = lean_box(0);
                            v_isShared_3614_ = v_isSharedCheck_3618_;
                            state = 5;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_3619_ = lean_ctor_get(v_code_3556_, 0);
                    v_isSharedCheck_3641_ = (!lean_is_exclusive(v_code_3556_)) as u8;
                    if v_isSharedCheck_3641_ == 0 {
                        v___x_3621_ = v_code_3556_;
                        v_isShared_3622_ = v_isSharedCheck_3641_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_cases_3619_);
                        lean_dec(v_code_3556_);
                        v___x_3621_ = lean_box(0);
                        v_isShared_3622_ = v_isSharedCheck_3641_;
                        state = 7;
                        continue;
                    }
                }
                5 => {
                    v_isSharedCheck_3649_ = (!lean_is_exclusive(v_code_3556_)) as u8;
                    if v_isSharedCheck_3649_ == 0 {
                        v_unused_3650_ = lean_ctor_get(v_code_3556_, 0);
                        lean_dec(v_unused_3650_);
                        v___x_3643_ = v_code_3556_;
                        v_isShared_3644_ = v_isSharedCheck_3649_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec(v_code_3556_);
                        v___x_3643_ = lean_box(0);
                        v_isShared_3644_ = v_isSharedCheck_3649_;
                        state = 10;
                        continue;
                    }
                }
                6 => {
                    v_isSharedCheck_3658_ = (!lean_is_exclusive(v_code_3556_)) as u8;
                    if v_isSharedCheck_3658_ == 0 {
                        v_unused_3659_ = lean_ctor_get(v_code_3556_, 0);
                        lean_dec(v_unused_3659_);
                        v___x_3652_ = v_code_3556_;
                        v_isShared_3653_ = v_isSharedCheck_3658_;
                        state = 12;
                        continue;
                    } else {
                        lean_dec(v_code_3556_);
                        v___x_3652_ = lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3658_;
                        state = 12;
                        continue;
                    }
                }
                8 => {
                    v_k_3660_ = lean_ctor_get(v_code_3556_, 3);
                    lean_inc_ref(v_k_3660_);
                    lean_dec_ref_known(v_code_3556_, 4);
                    v_code_3556_ = v_k_3660_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_3662_ = lean_ctor_get(v_code_3556_, 5);
                    lean_inc_ref(v_k_3662_);
                    lean_dec_ref_known(v_code_3556_, 6);
                    v_code_3556_ = v_k_3662_;
                    state = 0;
                    continue;
                }
                _ => {
                    lean_dec_ref(v_code_3556_);
                    v___x_3664_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___closed__2);
                    v___x_3665_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__2(v___x_3664_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                    return v___x_3665_;
                }
            },
            1 => {
                v___x_3595_ = lean_box(0);
                if v_isShared_3594_ == 0 {
                    lean_ctor_set(v___x_3593_, 0, v___x_3595_);
                    v___x_3597_ = v___x_3593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3595_);
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
                    v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
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
                    v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
                    v___x_3616_ = v_reuseFailAlloc_3617_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3616_;
            }
            7 => {
                v_alts_3623_ = lean_ctor_get(v_cases_3619_, 3);
                lean_inc_ref(v_alts_3623_);
                lean_dec_ref(v_cases_3619_);
                v___x_3624_ = lean_unsigned_to_nat(0);
                v___x_3625_ = lean_array_get_size(v_alts_3623_);
                v___x_3626_ = lean_box(0);
                v___x_3627_ = lean_nat_dec_lt(v___x_3624_, v___x_3625_);
                if v___x_3627_ == 0 {
                    lean_dec_ref(v_alts_3623_);
                    if v_isShared_3622_ == 0 {
                        lean_ctor_set_tag(v___x_3621_, 0);
                        lean_ctor_set(v___x_3621_, 0, v___x_3626_);
                        v___x_3629_ = v___x_3621_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3626_);
                        v___x_3629_ = v_reuseFailAlloc_3630_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___x_3631_ = lean_nat_dec_le(v___x_3625_, v___x_3625_);
                    if v___x_3631_ == 0 {
                        if v___x_3627_ == 0 {
                            lean_dec_ref(v_alts_3623_);
                            if v_isShared_3622_ == 0 {
                                lean_ctor_set_tag(v___x_3621_, 0);
                                lean_ctor_set(v___x_3621_, 0, v___x_3626_);
                                v___x_3633_ = v___x_3621_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3626_);
                                v___x_3633_ = v_reuseFailAlloc_3634_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3621_);
                            v___x_3635_ = 0usize;
                            v___x_3636_ = lean_usize_of_nat(v___x_3625_);
                            v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4(v_alts_3623_, v___x_3635_, v___x_3636_, v___x_3626_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                            lean_dec_ref(v_alts_3623_);
                            return v___x_3637_;
                        }
                    } else {
                        lean_del_object(v___x_3621_);
                        v___x_3638_ = 0usize;
                        v___x_3639_ = lean_usize_of_nat(v___x_3625_);
                        v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4(v_alts_3623_, v___x_3638_, v___x_3639_, v___x_3626_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
                        lean_dec_ref(v_alts_3623_);
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
                v___x_3645_ = lean_box(0);
                if v_isShared_3644_ == 0 {
                    lean_ctor_set_tag(v___x_3643_, 0);
                    lean_ctor_set(v___x_3643_, 0, v___x_3645_);
                    v___x_3647_ = v___x_3643_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
                    v___x_3647_ = v_reuseFailAlloc_3648_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3647_;
            }
            12 => {
                v___x_3654_ = lean_box(0);
                if v_isShared_3653_ == 0 {
                    lean_ctor_set_tag(v___x_3652_, 0);
                    lean_ctor_set(v___x_3652_, 0, v___x_3654_);
                    v___x_3656_ = v___x_3652_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
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
    mut v_code_3666_: *mut LeanObject,
    mut v_a_3667_: *mut LeanObject,
    mut v_a_3668_: *mut LeanObject,
    mut v_a_3669_: *mut LeanObject,
    mut v_a_3670_: *mut LeanObject,
    mut v_a_3671_: *mut LeanObject,
    mut v_a_3672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3673_: *mut LeanObject = core::ptr::null_mut();
    v_res_3673_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode(v_code_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_);
    lean_dec(v_a_3671_);
    lean_dec_ref(v_a_3670_);
    lean_dec(v_a_3669_);
    lean_dec_ref(v_a_3668_);
    lean_dec(v_a_3667_);
    return v_res_3673_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4(
    mut v_as_3674_: *mut LeanObject,
    mut v_i_3675_: usize,
    mut v_stop_3676_: usize,
    mut v_b_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
    mut v___y_3681_: *mut LeanObject,
    mut v___y_3682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: usize = 0;
    let mut v___x_3690_: usize = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3684_ = lean_usize_dec_eq(v_i_3675_, v_stop_3676_);
                if v___x_3684_ == 0 {
                    v___x_3685_ = lean_array_uget_borrowed(v_as_3674_, v_i_3675_);
                    v___x_3686_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode___boxed as *mut core::ffi::c_void, 7, 0);
                    lean_inc(v___x_3685_);
                    v___x_3687_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__0___redArg(v___x_3685_, v___x_3686_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
                    if lean_obj_tag(v___x_3687_) == 0 {
                        v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
                        lean_inc(v_a_3688_);
                        lean_dec_ref_known(v___x_3687_, 1);
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
                    v___x_3692_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3692_, 0, v_b_3677_);
                    return v___x_3692_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4___boxed(
    mut v_as_3693_: *mut LeanObject,
    mut v_i_3694_: *mut LeanObject,
    mut v_stop_3695_: *mut LeanObject,
    mut v_b_3696_: *mut LeanObject,
    mut v___y_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
    mut v___y_3700_: *mut LeanObject,
    mut v___y_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3703_: usize = 0;
    let mut v_stop_boxed_3704_: usize = 0;
    let mut v_res_3705_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3703_ = lean_unbox_usize(v_i_3694_);
    lean_dec(v_i_3694_);
    v_stop_boxed_3704_ = lean_unbox_usize(v_stop_3695_);
    lean_dec(v_stop_3695_);
    v_res_3705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__4(v_as_3693_, v_i_boxed_3703_, v_stop_boxed_3704_, v_b_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
    lean_dec(v___y_3701_);
    lean_dec_ref(v___y_3700_);
    lean_dec(v___y_3699_);
    lean_dec_ref(v___y_3698_);
    lean_dec(v___y_3697_);
    lean_dec_ref(v_as_3693_);
    return v_res_3705_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1(
    mut v_00_u03b2_3706_: *mut LeanObject,
    mut v_m_3707_: *mut LeanObject,
    mut v_a_3708_: *mut LeanObject,
) -> u8 {
    let mut v___x_3709_: u8 = 0;
    v___x_3709_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___redArg(v_m_3707_, v_a_3708_);
    return v___x_3709_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1___boxed(
    mut v_00_u03b2_3710_: *mut LeanObject,
    mut v_m_3711_: *mut LeanObject,
    mut v_a_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3713_: u8 = 0;
    let mut v_r_3714_: *mut LeanObject = core::ptr::null_mut();
    v_res_3713_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__1(v_00_u03b2_3710_, v_m_3711_, v_a_3712_);
    lean_dec(v_a_3712_);
    lean_dec_ref(v_m_3711_);
    v_r_3714_ = lean_box((v_res_3713_) as usize);
    return v_r_3714_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2(
    mut v_as_3715_: *mut LeanObject,
    mut v_sz_3716_: usize,
    mut v_i_3717_: usize,
    mut v_b_3718_: *mut LeanObject,
    mut v___y_3719_: *mut LeanObject,
    mut v___y_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    v___x_3725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___redArg(v_as_3715_, v_sz_3716_, v_i_3717_, v_b_3718_, v___y_3719_);
    return v___x_3725_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2___boxed(
    mut v_as_3726_: *mut LeanObject,
    mut v_sz_3727_: *mut LeanObject,
    mut v_i_3728_: *mut LeanObject,
    mut v_b_3729_: *mut LeanObject,
    mut v___y_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
    mut v___y_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
    mut v___y_3734_: *mut LeanObject,
    mut v___y_3735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3736_: usize = 0;
    let mut v_i_boxed_3737_: usize = 0;
    let mut v_res_3738_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3736_ = lean_unbox_usize(v_sz_3727_);
    lean_dec(v_sz_3727_);
    v_i_boxed_3737_ = lean_unbox_usize(v_i_3728_);
    lean_dec(v_i_3728_);
    v_res_3738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__2(v_as_3726_, v_sz_boxed_3736_, v_i_boxed_3737_, v_b_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
    lean_dec(v___y_3734_);
    lean_dec_ref(v___y_3733_);
    lean_dec(v___y_3732_);
    lean_dec_ref(v___y_3731_);
    lean_dec(v___y_3730_);
    lean_dec_ref(v_as_3726_);
    return v_res_3738_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3(
    mut v_as_3739_: *mut LeanObject,
    mut v_sz_3740_: usize,
    mut v_i_3741_: usize,
    mut v_b_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
    mut v___y_3744_: *mut LeanObject,
    mut v___y_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___redArg(v_as_3739_, v_sz_3740_, v_i_3741_, v_b_3742_, v___y_3743_);
    return v___x_3749_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3___boxed(
    mut v_as_3750_: *mut LeanObject,
    mut v_sz_3751_: *mut LeanObject,
    mut v_i_3752_: *mut LeanObject,
    mut v_b_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3760_: usize = 0;
    let mut v_i_boxed_3761_: usize = 0;
    let mut v_res_3762_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3760_ = lean_unbox_usize(v_sz_3751_);
    lean_dec(v_sz_3751_);
    v_i_boxed_3761_ = lean_unbox_usize(v_i_3752_);
    lean_dec(v_i_3752_);
    v_res_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode_spec__3(v_as_3750_, v_sz_boxed_3760_, v_i_boxed_3761_, v_b_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
    lean_dec(v___y_3758_);
    lean_dec_ref(v___y_3757_);
    lean_dec(v___y_3756_);
    lean_dec_ref(v___y_3755_);
    lean_dec(v___y_3754_);
    lean_dec_ref(v_as_3750_);
    return v_res_3762_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_loop(
    mut v_decl_3763_: *mut LeanObject,
    mut v_a_3764_: *mut LeanObject,
    mut v_a_3765_: *mut LeanObject,
    mut v_a_3766_: *mut LeanObject,
    mut v_a_3767_: *mut LeanObject,
    mut v_a_3768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modified_3777_: u8 = 0;
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3781_ = lean_st_ref_take(v_a_3764_);
                v_values_3782_ = lean_ctor_get(v___x_3781_, 0);
                v_isSharedCheck_3794_ = (!lean_is_exclusive(v___x_3781_)) as u8;
                if v_isSharedCheck_3794_ == 0 {
                    v___x_3784_ = v___x_3781_;
                    v_isShared_3785_ = v_isSharedCheck_3794_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_values_3782_);
                    lean_dec(v___x_3781_);
                    v___x_3784_ = lean_box(0);
                    v_isShared_3785_ = v_isSharedCheck_3794_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3776_ = lean_st_ref_get(v___y_3771_);
                v_modified_3777_ = lean_ctor_get_uint8(
                    v___x_3776_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec(v___x_3776_);
                if v_modified_3777_ == 0 {
                    lean_dec_ref(v_decl_3763_);
                    v___x_3778_ = lean_box(0);
                    v___x_3779_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3779_, 0, v___x_3778_);
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
                    v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_values_3782_);
                    v___x_3788_ = v_reuseFailAlloc_3793_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_3788_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3786_,
                );
                v___x_3789_ = lean_st_ref_set(v_a_3764_, v___x_3788_);
                v_value_3790_ = lean_ctor_get(v_decl_3763_, 1);
                if lean_obj_tag(v_value_3790_) == 0 {
                    v_code_3791_ = lean_ctor_get(v_value_3790_, 0);
                    lean_inc_ref(v_code_3791_);
                    v___x_3792_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectCode(v_code_3791_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
                    if lean_obj_tag(v___x_3792_) == 0 {
                        lean_dec_ref_known(v___x_3792_, 1);
                        v___y_3771_ = v_a_3764_;
                        v___y_3772_ = v_a_3765_;
                        v___y_3773_ = v_a_3766_;
                        v___y_3774_ = v_a_3767_;
                        v___y_3775_ = v_a_3768_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_decl_3763_);
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
    mut v_decl_3795_: *mut LeanObject,
    mut v_a_3796_: *mut LeanObject,
    mut v_a_3797_: *mut LeanObject,
    mut v_a_3798_: *mut LeanObject,
    mut v_a_3799_: *mut LeanObject,
    mut v_a_3800_: *mut LeanObject,
    mut v_a_3801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3802_: *mut LeanObject = core::ptr::null_mut();
    v_res_3802_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_loop(v_decl_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
    lean_dec(v_a_3800_);
    lean_dec_ref(v_a_3799_);
    lean_dec(v_a_3798_);
    lean_dec_ref(v_a_3797_);
    lean_dec(v_a_3796_);
    return v_res_3802_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg(
    mut v_as_3803_: *mut LeanObject,
    mut v_sz_3804_: usize,
    mut v_i_3805_: usize,
    mut v_b_3806_: *mut LeanObject,
    mut v___y_3807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3809_: u8 = 0;
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_3812_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3815_: u8 = 0;
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modified_3818_: u8 = 0;
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3821_: u8 = 0;
    let mut v_fvarId_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: usize = 0;
    let mut v___x_3829_: usize = 0;
    let mut v_reuseFailAlloc_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3809_ = lean_usize_dec_lt(v_i_3805_, v_sz_3804_);
                if v___x_3809_ == 0 {
                    v___x_3810_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3810_, 0, v_b_3806_);
                    return v___x_3810_;
                } else {
                    v_a_3811_ = lean_array_uget_borrowed(v_as_3803_, v_i_3805_);
                    v_borrow_3812_ = lean_ctor_get_uint8(
                        v_a_3811_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v___x_3813_ = lean_box(0);
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
                v_values_3817_ = lean_ctor_get(v___x_3816_, 0);
                v_modified_3818_ = lean_ctor_get_uint8(
                    v___x_3816_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3832_ = (!lean_is_exclusive(v___x_3816_)) as u8;
                if v_isSharedCheck_3832_ == 0 {
                    v___x_3820_ = v___x_3816_;
                    v_isShared_3821_ = v_isSharedCheck_3832_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_values_3817_);
                    lean_dec(v___x_3816_);
                    v___x_3820_ = lean_box(0);
                    v_isShared_3821_ = v_isSharedCheck_3832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fvarId_3822_ = lean_ctor_get(v_a_3811_, 0);
                v___x_3823_ = lean_box((v___y_3815_) as usize);
                lean_inc(v_fvarId_3822_);
                v___x_3824_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_collectLetValue_spec__1___redArg(v_values_3817_, v_fvarId_3822_, v___x_3823_);
                if v_isShared_3821_ == 0 {
                    lean_ctor_set(v___x_3820_, 0, v___x_3824_);
                    v___x_3826_ = v___x_3820_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3824_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3831_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_as_3835_: *mut LeanObject,
    mut v_sz_3836_: *mut LeanObject,
    mut v_i_3837_: *mut LeanObject,
    mut v_b_3838_: *mut LeanObject,
    mut v___y_3839_: *mut LeanObject,
    mut v___y_3840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3841_: usize = 0;
    let mut v_i_boxed_3842_: usize = 0;
    let mut v_res_3843_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3841_ = lean_unbox_usize(v_sz_3836_);
    lean_dec(v_sz_3836_);
    v_i_boxed_3842_ = lean_unbox_usize(v_i_3837_);
    lean_dec(v_i_3837_);
    v_res_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg(v_as_3835_, v_sz_boxed_3841_, v_i_boxed_3842_, v_b_3838_, v___y_3839_);
    lean_dec(v___y_3839_);
    lean_dec_ref(v_as_3835_);
    return v_res_3843_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl(
    mut v_decl_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
    mut v_a_3846_: *mut LeanObject,
    mut v_a_3847_: *mut LeanObject,
    mut v_a_3848_: *mut LeanObject,
    mut v_a_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3855_: usize = 0;
    let mut v___x_3856_: usize = 0;
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3860_: u8 = 0;
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3864_: u8 = 0;
    let mut v_unused_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_3851_ = lean_ctor_get(v_decl_3844_, 1);
                if lean_obj_tag(v_value_3851_) == 0 {
                    v_toSignature_3852_ = lean_ctor_get(v_decl_3844_, 0);
                    v_params_3853_ = lean_ctor_get(v_toSignature_3852_, 3);
                    v___x_3854_ = lean_box(0);
                    v_sz_3855_ = lean_array_size(v_params_3853_);
                    v___x_3856_ = 0usize;
                    v___x_3857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg(v_params_3853_, v_sz_3855_, v___x_3856_, v___x_3854_, v_a_3845_);
                    if lean_obj_tag(v___x_3857_) == 0 {
                        v_isSharedCheck_3864_ = (!lean_is_exclusive(v___x_3857_)) as u8;
                        if v_isSharedCheck_3864_ == 0 {
                            v_unused_3865_ = lean_ctor_get(v___x_3857_, 0);
                            lean_dec(v_unused_3865_);
                            v___x_3859_ = v___x_3857_;
                            v_isShared_3860_ = v_isSharedCheck_3864_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3857_);
                            v___x_3859_ = lean_box(0);
                            v_isShared_3860_ = v_isSharedCheck_3864_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3857_;
                    }
                } else {
                    v___x_3866_ = lean_box(0);
                    v___x_3867_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3867_, 0, v___x_3866_);
                    return v___x_3867_;
                }
            }
            1 => {
                if v_isShared_3860_ == 0 {
                    lean_ctor_set(v___x_3859_, 0, v___x_3854_);
                    v___x_3862_ = v___x_3859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3854_);
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
    mut v_decl_3868_: *mut LeanObject,
    mut v_a_3869_: *mut LeanObject,
    mut v_a_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
    mut v_a_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_res_3875_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl(v_decl_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
    lean_dec(v_a_3873_);
    lean_dec_ref(v_a_3872_);
    lean_dec(v_a_3871_);
    lean_dec_ref(v_a_3870_);
    lean_dec(v_a_3869_);
    lean_dec_ref(v_decl_3868_);
    return v_res_3875_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0(
    mut v_as_3876_: *mut LeanObject,
    mut v_sz_3877_: usize,
    mut v_i_3878_: usize,
    mut v_b_3879_: *mut LeanObject,
    mut v___y_3880_: *mut LeanObject,
    mut v___y_3881_: *mut LeanObject,
    mut v___y_3882_: *mut LeanObject,
    mut v___y_3883_: *mut LeanObject,
    mut v___y_3884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___redArg(v_as_3876_, v_sz_3877_, v_i_3878_, v_b_3879_, v___y_3880_);
    return v___x_3886_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0___boxed(
    mut v_as_3887_: *mut LeanObject,
    mut v_sz_3888_: *mut LeanObject,
    mut v_i_3889_: *mut LeanObject,
    mut v_b_3890_: *mut LeanObject,
    mut v___y_3891_: *mut LeanObject,
    mut v___y_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
    mut v___y_3896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3897_: usize = 0;
    let mut v_i_boxed_3898_: usize = 0;
    let mut v_res_3899_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3897_ = lean_unbox_usize(v_sz_3888_);
    lean_dec(v_sz_3888_);
    v_i_boxed_3898_ = lean_unbox_usize(v_i_3889_);
    lean_dec(v_i_3889_);
    v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl_spec__0(v_as_3887_, v_sz_boxed_3897_, v_i_boxed_3898_, v_b_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
    lean_dec(v___y_3895_);
    lean_dec_ref(v___y_3894_);
    lean_dec(v___y_3893_);
    lean_dec_ref(v___y_3892_);
    lean_dec(v___y_3891_);
    lean_dec_ref(v_as_3887_);
    return v_res_3899_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_go(
    mut v_decl_3900_: *mut LeanObject,
    mut v_a_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
    mut v_a_3903_: *mut LeanObject,
    mut v_a_3904_: *mut LeanObject,
    mut v_a_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    v___x_3907_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_initializeDecl(v_decl_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
    if lean_obj_tag(v___x_3907_) == 0 {
        let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3907_, 1);
        v___x_3908_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_loop(v_decl_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
        return v___x_3908_;
    } else {
        lean_dec_ref(v_decl_3900_);
        return v___x_3907_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_go___boxed(
    mut v_decl_3909_: *mut LeanObject,
    mut v_a_3910_: *mut LeanObject,
    mut v_a_3911_: *mut LeanObject,
    mut v_a_3912_: *mut LeanObject,
    mut v_a_3913_: *mut LeanObject,
    mut v_a_3914_: *mut LeanObject,
    mut v_a_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3916_: *mut LeanObject = core::ptr::null_mut();
    v_res_3916_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_go(v_decl_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_);
    lean_dec(v_a_3914_);
    lean_dec_ref(v_a_3913_);
    lean_dec(v_a_3912_);
    lean_dec_ref(v_a_3911_);
    lean_dec(v_a_3910_);
    return v_res_3916_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(
    mut v_decl_3917_: *mut LeanObject,
    mut v_a_3918_: *mut LeanObject,
    mut v_a_3919_: *mut LeanObject,
    mut v_a_3920_: *mut LeanObject,
    mut v_a_3921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut v_unused_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3923_ = lean_obj_once(
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
                if lean_obj_tag(v___x_3925_) == 0 {
                    v_isSharedCheck_3934_ = (!lean_is_exclusive(v___x_3925_)) as u8;
                    if v_isSharedCheck_3934_ == 0 {
                        v_unused_3935_ = lean_ctor_get(v___x_3925_, 0);
                        lean_dec(v_unused_3935_);
                        v___x_3927_ = v___x_3925_;
                        v_isShared_3928_ = v_isSharedCheck_3934_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3925_);
                        v___x_3927_ = lean_box(0);
                        v_isShared_3928_ = v_isSharedCheck_3934_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3924_);
                    v_a_3936_ = lean_ctor_get(v___x_3925_, 0);
                    v_isSharedCheck_3943_ = (!lean_is_exclusive(v___x_3925_)) as u8;
                    if v_isSharedCheck_3943_ == 0 {
                        v___x_3938_ = v___x_3925_;
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3936_);
                        lean_dec(v___x_3925_);
                        v___x_3938_ = lean_box(0);
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3929_ = lean_st_ref_get(v___x_3924_);
                lean_dec(v___x_3924_);
                v_values_3930_ = lean_ctor_get(v___x_3929_, 0);
                lean_inc_ref(v_values_3930_);
                lean_dec(v___x_3929_);
                if v_isShared_3928_ == 0 {
                    lean_ctor_set(v___x_3927_, 0, v_values_3930_);
                    v___x_3932_ = v___x_3927_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_values_3930_);
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
                    v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
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
    mut v_decl_3944_: *mut LeanObject,
    mut v_a_3945_: *mut LeanObject,
    mut v_a_3946_: *mut LeanObject,
    mut v_a_3947_: *mut LeanObject,
    mut v_a_3948_: *mut LeanObject,
    mut v_a_3949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3950_: *mut LeanObject = core::ptr::null_mut();
    v_res_3950_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(
        v_decl_3944_,
        v_a_3945_,
        v_a_3946_,
        v_a_3947_,
        v_a_3948_,
    );
    lean_dec(v_a_3948_);
    lean_dec_ref(v_a_3947_);
    lean_dec(v_a_3946_);
    lean_dec_ref(v_a_3945_);
    return v_res_3950_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow(
    mut v_x_3957_: u8,
) -> *mut LeanObject {
    match v_x_3957_ {
        0 => {
            let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
            v___x_3958_ = lean_box(0);
            return v___x_3958_;
        }
        1 => {
            let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
            v___x_3959_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__0;
            return v___x_3959_;
        }
        _ => {
            let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
            v___x_3960_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___closed__1;
            return v___x_3960_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow___boxed(
    mut v_x_3961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_41__boxed_3962_: u8 = 0;
    let mut v_res_3963_: *mut LeanObject = core::ptr::null_mut();
    v_x_41__boxed_3962_ = (lean_unbox(v_x_3961_) as u8);
    v_res_3963_ =
        l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow(
            v_x_41__boxed_3962_,
        );
    return v_res_3963_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0_spec__1(
    mut v_msg_3964_: *mut LeanObject,
) -> u8 {
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    v___x_3965_ = 0;
    v___x_3966_ = lean_box((v___x_3965_) as usize);
    v___x_3967_ = lean_panic_fn_borrowed(v___x_3966_, v_msg_3964_);
    lean_dec(v___x_3966_);
    v___x_3968_ = (lean_unbox(v___x_3967_) as u8);
    lean_dec(v___x_3967_);
    return v___x_3968_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0_spec__1___boxed(
    mut v_msg_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3970_: u8 = 0;
    let mut v_r_3971_: *mut LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0_spec__1(v_msg_3969_);
    v_r_3971_ = lean_box((v_res_3970_) as usize);
    return v_r_3971_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    v___x_3975_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__2;
    v___x_3976_ = lean_unsigned_to_nat(11);
    v___x_3977_ = lean_unsigned_to_nat(163);
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
    mut v_a_3981_: *mut LeanObject,
    mut v_x_3982_: *mut LeanObject,
) -> u8 {
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v_key_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: u8 = 0;
    let mut v___x_3990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3982_) == 0 {
                    v___x_3983_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___closed__3);
                    v___x_3984_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0_spec__1(v___x_3983_);
                    return v___x_3984_;
                } else {
                    v_key_3985_ = lean_ctor_get(v_x_3982_, 0);
                    v_value_3986_ = lean_ctor_get(v_x_3982_, 1);
                    v_tail_3987_ = lean_ctor_get(v_x_3982_, 2);
                    v___x_3988_ = l_Lean_instBEqFVarId_beq(v_key_3985_, v_a_3981_);
                    if v___x_3988_ == 0 {
                        v_x_3982_ = v_tail_3987_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3990_ = (lean_unbox(v_value_3986_) as u8);
                        return v___x_3990_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0___boxed(
    mut v_a_3991_: *mut LeanObject,
    mut v_x_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3993_: u8 = 0;
    let mut v_r_3994_: *mut LeanObject = core::ptr::null_mut();
    v_res_3993_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0_spec__0(v_a_3991_, v_x_3992_);
    lean_dec(v_x_3992_);
    lean_dec(v_a_3991_);
    v_r_3994_ = lean_box((v_res_3993_) as usize);
    return v_r_3994_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0(
    mut v_m_3995_: *mut LeanObject,
    mut v_a_3996_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: u8 = 0;
    v_buckets_3997_ = lean_ctor_get(v_m_3995_, 1);
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
    mut v_m_4013_: *mut LeanObject,
    mut v_a_4014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4015_: u8 = 0;
    let mut v_r_4016_: *mut LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0(v_m_4013_, v_a_4014_);
    lean_dec(v_a_4014_);
    lean_dec_ref(v_m_4013_);
    v_r_4016_ = lean_box((v_res_4015_) as usize);
    return v_r_4016_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg(
    mut v_values_4017_: *mut LeanObject,
    mut v_sz_4018_: usize,
    mut v_i_4019_: usize,
    mut v_bs_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4023_: u8 = 0;
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: usize = 0;
    let mut v___x_4032_: usize = 0;
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: u8 = 0;
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4045_: u8 = 0;
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4023_ = lean_usize_dec_lt(v_i_4019_, v_sz_4018_);
                if v___x_4023_ == 0 {
                    v___x_4024_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4024_, 0, v_bs_4020_);
                    return v___x_4024_;
                } else {
                    v_v_4025_ = lean_array_uget(v_bs_4020_, v_i_4019_);
                    v_fvarId_4026_ = lean_ctor_get(v_v_4025_, 0);
                    v___x_4027_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4028_ = lean_array_uset(v_bs_4020_, v_i_4019_, v___x_4027_);
                    v___x_4035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__0(v_values_4017_, v_fvarId_4026_);
                    v___x_4036_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Ownedness_toBorrow(v___x_4035_);
                    if lean_obj_tag(v___x_4036_) == 0 {
                        v_a_4030_ = v_v_4025_;
                        state = 1;
                        continue;
                    } else {
                        v_val_4037_ = lean_ctor_get(v___x_4036_, 0);
                        lean_inc(v_val_4037_);
                        lean_dec_ref_known(v___x_4036_, 1);
                        v___x_4038_ = 1;
                        v___x_4039_ = (lean_unbox(v_val_4037_) as u8);
                        lean_dec(v_val_4037_);
                        v___x_4040_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_4038_, v_v_4025_, v___x_4039_, v___y_4021_);
                        if lean_obj_tag(v___x_4040_) == 0 {
                            v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
                            lean_inc(v_a_4041_);
                            lean_dec_ref_known(v___x_4040_, 1);
                            v_a_4030_ = v_a_4041_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_bs_x27_4028_);
                            v_a_4042_ = lean_ctor_get(v___x_4040_, 0);
                            v_isSharedCheck_4049_ = (!lean_is_exclusive(v___x_4040_)) as u8;
                            if v_isSharedCheck_4049_ == 0 {
                                v___x_4044_ = v___x_4040_;
                                v_isShared_4045_ = v_isSharedCheck_4049_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4042_);
                                lean_dec(v___x_4040_);
                                v___x_4044_ = lean_box(0);
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
                    v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
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
    mut v_values_4050_: *mut LeanObject,
    mut v_sz_4051_: *mut LeanObject,
    mut v_i_4052_: *mut LeanObject,
    mut v_bs_4053_: *mut LeanObject,
    mut v___y_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4056_: usize = 0;
    let mut v_i_boxed_4057_: usize = 0;
    let mut v_res_4058_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4056_ = lean_unbox_usize(v_sz_4051_);
    lean_dec(v_sz_4051_);
    v_i_boxed_4057_ = lean_unbox_usize(v_i_4052_);
    lean_dec(v_i_4052_);
    v_res_4058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg(v_values_4050_, v_sz_boxed_4056_, v_i_boxed_4057_, v_bs_4053_, v___y_4054_);
    lean_dec(v___y_4054_);
    lean_dec_ref(v_values_4050_);
    return v_res_4058_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams(
    mut v_values_4059_: *mut LeanObject,
    mut v_ps_4060_: *mut LeanObject,
    mut v_a_4061_: *mut LeanObject,
    mut v_a_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
    mut v_a_4064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4066_: usize = 0;
    let mut v___x_4067_: usize = 0;
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4066_ = lean_array_size(v_ps_4060_);
    v___x_4067_ = 0usize;
    v___x_4068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg(v_values_4059_, v_sz_4066_, v___x_4067_, v_ps_4060_, v_a_4062_);
    return v___x_4068_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams___boxed(
    mut v_values_4069_: *mut LeanObject,
    mut v_ps_4070_: *mut LeanObject,
    mut v_a_4071_: *mut LeanObject,
    mut v_a_4072_: *mut LeanObject,
    mut v_a_4073_: *mut LeanObject,
    mut v_a_4074_: *mut LeanObject,
    mut v_a_4075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4076_: *mut LeanObject = core::ptr::null_mut();
    v_res_4076_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams(v_values_4069_, v_ps_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
    lean_dec(v_a_4074_);
    lean_dec_ref(v_a_4073_);
    lean_dec(v_a_4072_);
    lean_dec_ref(v_a_4071_);
    lean_dec_ref(v_values_4069_);
    return v_res_4076_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1(
    mut v_values_4077_: *mut LeanObject,
    mut v_sz_4078_: usize,
    mut v_i_4079_: usize,
    mut v_bs_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    v___x_4086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___redArg(v_values_4077_, v_sz_4078_, v_i_4079_, v_bs_4080_, v___y_4082_);
    return v___x_4086_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1___boxed(
    mut v_values_4087_: *mut LeanObject,
    mut v_sz_4088_: *mut LeanObject,
    mut v_i_4089_: *mut LeanObject,
    mut v_bs_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
    mut v___y_4093_: *mut LeanObject,
    mut v___y_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4096_: usize = 0;
    let mut v_i_boxed_4097_: usize = 0;
    let mut v_res_4098_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4096_ = lean_unbox_usize(v_sz_4088_);
    lean_dec(v_sz_4088_);
    v_i_boxed_4097_ = lean_unbox_usize(v_i_4089_);
    lean_dec(v_i_4089_);
    v_res_4098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams_spec__1(v_values_4087_, v_sz_boxed_4096_, v_i_boxed_4097_, v_bs_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
    lean_dec(v___y_4094_);
    lean_dec_ref(v___y_4093_);
    lean_dec(v___y_4092_);
    lean_dec_ref(v___y_4091_);
    lean_dec_ref(v_values_4087_);
    return v_res_4098_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg(
    mut v_alt_4099_: *mut LeanObject,
    mut v_f_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
    mut v___y_4103_: *mut LeanObject,
    mut v___y_4104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_a_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4125_: u8 = 0;
    let mut v_code_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_alt_4099_) {
                0 => {
                    v_code_4126_ = lean_ctor_get(v_alt_4099_, 2);
                    lean_inc_ref(v_code_4126_);
                    v___y_4107_ = v_code_4126_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_4127_ = lean_ctor_get(v_alt_4099_, 1);
                    lean_inc_ref(v_code_4127_);
                    v___y_4107_ = v_code_4127_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_4128_ = lean_ctor_get(v_alt_4099_, 0);
                    lean_inc_ref(v_code_4128_);
                    v___y_4107_ = v_code_4128_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                lean_inc(v___y_4104_);
                lean_inc_ref(v___y_4103_);
                lean_inc(v___y_4102_);
                lean_inc_ref(v___y_4101_);
                v___x_4108_ = lean_apply_6(
                    v_f_4100_,
                    v___y_4107_,
                    v___y_4101_,
                    v___y_4102_,
                    v___y_4103_,
                    v___y_4104_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4108_) == 0 {
                    v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
                    v_isSharedCheck_4117_ = (!lean_is_exclusive(v___x_4108_)) as u8;
                    if v_isSharedCheck_4117_ == 0 {
                        v___x_4111_ = v___x_4108_;
                        v_isShared_4112_ = v_isSharedCheck_4117_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4109_);
                        lean_dec(v___x_4108_);
                        v___x_4111_ = lean_box(0);
                        v_isShared_4112_ = v_isSharedCheck_4117_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_alt_4099_);
                    v_a_4118_ = lean_ctor_get(v___x_4108_, 0);
                    v_isSharedCheck_4125_ = (!lean_is_exclusive(v___x_4108_)) as u8;
                    if v_isSharedCheck_4125_ == 0 {
                        v___x_4120_ = v___x_4108_;
                        v_isShared_4121_ = v_isSharedCheck_4125_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4118_);
                        lean_dec(v___x_4108_);
                        v___x_4120_ = lean_box(0);
                        v_isShared_4121_ = v_isSharedCheck_4125_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4113_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_4099_, v_a_4109_);
                if v_isShared_4112_ == 0 {
                    lean_ctor_set(v___x_4111_, 0, v___x_4113_);
                    v___x_4115_ = v___x_4111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
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
                    v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
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
    mut v_alt_4129_: *mut LeanObject,
    mut v_f_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
    mut v___y_4134_: *mut LeanObject,
    mut v___y_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4136_: *mut LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg(v_alt_4129_, v_f_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
    lean_dec(v___y_4134_);
    lean_dec_ref(v___y_4133_);
    lean_dec(v___y_4132_);
    lean_dec_ref(v___y_4131_);
    return v_res_4136_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0(
    mut v_pu_4137_: u8,
    mut v_alt_4138_: *mut LeanObject,
    mut v_f_4139_: *mut LeanObject,
    mut v___y_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    v___x_4145_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg(v_alt_4138_, v_f_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
    return v___x_4145_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___boxed(
    mut v_pu_4146_: *mut LeanObject,
    mut v_alt_4147_: *mut LeanObject,
    mut v_f_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
    mut v___y_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4154_: u8 = 0;
    let mut v_res_4155_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4154_ = (lean_unbox(v_pu_4146_) as u8);
    v_res_4155_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0(v_pu_boxed_4154_, v_alt_4147_, v_f_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
    lean_dec(v___y_4152_);
    lean_dec_ref(v___y_4151_);
    lean_dec(v___y_4150_);
    lean_dec_ref(v___y_4149_);
    return v_res_4155_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_4156_: u8 = 0;
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    v___x_4156_ = 1;
    v___x_4157_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2(
    mut v_msg_4158_: *mut LeanObject,
    mut v___y_4159_: *mut LeanObject,
    mut v___y_4160_: *mut LeanObject,
    mut v___y_4161_: *mut LeanObject,
    mut v___y_4162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v_toFunctor_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___f_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360__overap_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut v_unused_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4199_: u8 = 0;
    let mut v_unused_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4164_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__0);
                v___x_4165_ = l_StateRefT_x27_instMonad___redArg(v___x_4164_);
                v_toApplicative_4166_ = lean_ctor_get(v___x_4165_, 0);
                v_isSharedCheck_4199_ = (!lean_is_exclusive(v___x_4165_)) as u8;
                if v_isSharedCheck_4199_ == 0 {
                    v_unused_4200_ = lean_ctor_get(v___x_4165_, 1);
                    lean_dec(v_unused_4200_);
                    v___x_4168_ = v___x_4165_;
                    v_isShared_4169_ = v_isSharedCheck_4199_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4166_);
                    lean_dec(v___x_4165_);
                    v___x_4168_ = lean_box(0);
                    v_isShared_4169_ = v_isSharedCheck_4199_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4170_ = lean_ctor_get(v_toApplicative_4166_, 0);
                v_toSeq_4171_ = lean_ctor_get(v_toApplicative_4166_, 2);
                v_toSeqLeft_4172_ = lean_ctor_get(v_toApplicative_4166_, 3);
                v_toSeqRight_4173_ = lean_ctor_get(v_toApplicative_4166_, 4);
                v_isSharedCheck_4197_ = (!lean_is_exclusive(v_toApplicative_4166_)) as u8;
                if v_isSharedCheck_4197_ == 0 {
                    v_unused_4198_ = lean_ctor_get(v_toApplicative_4166_, 1);
                    lean_dec(v_unused_4198_);
                    v___x_4175_ = v_toApplicative_4166_;
                    v_isShared_4176_ = v_isSharedCheck_4197_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4173_);
                    lean_inc(v_toSeqLeft_4172_);
                    lean_inc(v_toSeq_4171_);
                    lean_inc(v_toFunctor_4170_);
                    lean_dec(v_toApplicative_4166_);
                    v___x_4175_ = lean_box(0);
                    v_isShared_4176_ = v_isSharedCheck_4197_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4177_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__1;
                v___f_4178_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_4170_);
                v___f_4179_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4179_, 0, v_toFunctor_4170_);
                v___f_4180_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4180_, 0, v_toFunctor_4170_);
                v___x_4181_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4181_, 0, v___f_4179_);
                lean_ctor_set(v___x_4181_, 1, v___f_4180_);
                v___f_4182_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4182_, 0, v_toSeqRight_4173_);
                v___f_4183_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4183_, 0, v_toSeqLeft_4172_);
                v___f_4184_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4184_, 0, v_toSeq_4171_);
                if v_isShared_4176_ == 0 {
                    lean_ctor_set(v___x_4175_, 4, v___f_4182_);
                    lean_ctor_set(v___x_4175_, 3, v___f_4183_);
                    lean_ctor_set(v___x_4175_, 2, v___f_4184_);
                    lean_ctor_set(v___x_4175_, 1, v___f_4177_);
                    lean_ctor_set(v___x_4175_, 0, v___x_4181_);
                    v___x_4186_ = v___x_4175_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4181_);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 1, v___f_4177_);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 2, v___f_4184_);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 3, v___f_4183_);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 4, v___f_4182_);
                    v___x_4186_ = v_reuseFailAlloc_4196_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4169_ == 0 {
                    lean_ctor_set(v___x_4168_, 1, v___f_4178_);
                    lean_ctor_set(v___x_4168_, 0, v___x_4186_);
                    v___x_4188_ = v___x_4168_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4186_);
                    lean_ctor_set(v_reuseFailAlloc_4195_, 1, v___f_4178_);
                    v___x_4188_ = v_reuseFailAlloc_4195_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4189_ = l_StateRefT_x27_instMonad___redArg(v___x_4188_);
                v___x_4190_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___closed__0);
                v___x_4191_ = l_instInhabitedOfMonad___redArg(v___x_4189_, v___x_4190_);
                v___f_4192_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_4192_, 0, v___x_4191_);
                v___x_3360__overap_4193_ = lean_panic_fn_borrowed(v___f_4192_, v_msg_4158_);
                lean_dec_ref(v___f_4192_);
                lean_inc(v___y_4162_);
                lean_inc_ref(v___y_4161_);
                lean_inc(v___y_4160_);
                lean_inc_ref(v___y_4159_);
                v___x_4194_ = lean_apply_5(
                    v___x_3360__overap_4193_,
                    v___y_4159_,
                    v___y_4160_,
                    v___y_4161_,
                    v___y_4162_,
                    lean_box(0),
                );
                return v___x_4194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2___boxed(
    mut v_msg_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
    mut v___y_4205_: *mut LeanObject,
    mut v___y_4206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4207_: *mut LeanObject = core::ptr::null_mut();
    v_res_4207_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2(v_msg_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
    lean_dec(v___y_4205_);
    lean_dec_ref(v___y_4204_);
    lean_dec(v___y_4203_);
    lean_dec_ref(v___y_4202_);
    return v_res_4207_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1()
-> *mut LeanObject {
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    v___x_4209_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows_getParams___closed__2;
    v___x_4210_ = lean_unsigned_to_nat(61);
    v___x_4211_ = lean_unsigned_to_nat(167);
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
    mut v_values_4215_: *mut LeanObject,
    mut v_code_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v___x_4229_: usize = 0;
    let mut v___x_4230_: usize = 0;
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v_unused_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v_decl_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4264_: u8 = 0;
    let mut v___y_4266_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4269_: u8 = 0;
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4276_: u8 = 0;
    let mut v_unused_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: usize = 0;
    let mut v___x_4284_: u8 = 0;
    let mut v___x_4285_: usize = 0;
    let mut v___x_4286_: usize = 0;
    let mut v___x_4287_: u8 = 0;
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_a_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut v_a_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4300_: u8 = 0;
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4304_: u8 = 0;
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4313_: u8 = 0;
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4320_: usize = 0;
    let mut v___x_4321_: usize = 0;
    let mut v___x_4322_: u8 = 0;
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4335_: u8 = 0;
    let mut v_unused_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut v_a_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4344_: u8 = 0;
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4348_: u8 = 0;
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v___x_4361_: usize = 0;
    let mut v___x_4362_: usize = 0;
    let mut v___x_4363_: u8 = 0;
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4373_: u8 = 0;
    let mut v_unused_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut v_fvarId_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4393_: usize = 0;
    let mut v___x_4394_: usize = 0;
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4405_: u8 = 0;
    let mut v_unused_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4415_: u8 = 0;
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_4216_) {
                0 => {
                    v_decl_4222_ = lean_ctor_get(v_code_4216_, 0);
                    v_k_4223_ = lean_ctor_get(v_code_4216_, 1);
                    lean_inc_ref(v_k_4223_);
                    v___x_4224_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_k_4223_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4224_) == 0 {
                        v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
                        v_isSharedCheck_4247_ = (!lean_is_exclusive(v___x_4224_)) as u8;
                        if v_isSharedCheck_4247_ == 0 {
                            v___x_4227_ = v___x_4224_;
                            v_isShared_4228_ = v_isSharedCheck_4247_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4225_);
                            lean_dec(v___x_4224_);
                            v___x_4227_ = lean_box(0);
                            v_isShared_4228_ = v_isSharedCheck_4247_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4216_, 2);
                        return v___x_4224_;
                    }
                }
                2 => {
                    v_decl_4248_ = lean_ctor_get(v_code_4216_, 0);
                    v_k_4249_ = lean_ctor_get(v_code_4216_, 1);
                    v_params_4250_ = lean_ctor_get(v_decl_4248_, 2);
                    v_type_4251_ = lean_ctor_get(v_decl_4248_, 3);
                    v_value_4252_ = lean_ctor_get(v_decl_4248_, 4);
                    lean_inc_ref(v_params_4250_);
                    v___x_4253_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams(v_values_4215_, v_params_4250_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4253_) == 0 {
                        v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
                        lean_inc(v_a_4254_);
                        lean_dec_ref_known(v___x_4253_, 1);
                        lean_inc_ref(v_value_4252_);
                        lean_inc_ref(v_values_4215_);
                        v___x_4255_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_value_4252_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                        if lean_obj_tag(v___x_4255_) == 0 {
                            v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
                            lean_inc(v_a_4256_);
                            lean_dec_ref_known(v___x_4255_, 1);
                            v___x_4257_ = 1;
                            lean_inc_ref(v_type_4251_);
                            lean_inc_ref(v_decl_4248_);
                            v___x_4258_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4257_, v_decl_4248_, v_type_4251_, v_a_4254_, v_a_4256_, v_a_4218_);
                            if lean_obj_tag(v___x_4258_) == 0 {
                                v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
                                lean_inc(v_a_4259_);
                                lean_dec_ref_known(v___x_4258_, 1);
                                lean_inc_ref(v_k_4249_);
                                v___x_4260_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_k_4249_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                                if lean_obj_tag(v___x_4260_) == 0 {
                                    v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
                                    v_isSharedCheck_4288_ = (!lean_is_exclusive(v___x_4260_)) as u8;
                                    if v_isSharedCheck_4288_ == 0 {
                                        v___x_4263_ = v___x_4260_;
                                        v_isShared_4264_ = v_isSharedCheck_4288_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4261_);
                                        lean_dec(v___x_4260_);
                                        v___x_4263_ = lean_box(0);
                                        v_isShared_4264_ = v_isSharedCheck_4288_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4259_);
                                    lean_dec_ref_known(v_code_4216_, 2);
                                    return v___x_4260_;
                                }
                            } else {
                                lean_dec_ref_known(v_code_4216_, 2);
                                lean_dec_ref(v_values_4215_);
                                v_a_4289_ = lean_ctor_get(v___x_4258_, 0);
                                v_isSharedCheck_4296_ = (!lean_is_exclusive(v___x_4258_)) as u8;
                                if v_isSharedCheck_4296_ == 0 {
                                    v___x_4291_ = v___x_4258_;
                                    v_isShared_4292_ = v_isSharedCheck_4296_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_4289_);
                                    lean_dec(v___x_4258_);
                                    v___x_4291_ = lean_box(0);
                                    v_isShared_4292_ = v_isSharedCheck_4296_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4254_);
                            lean_dec_ref_known(v_code_4216_, 2);
                            lean_dec_ref(v_values_4215_);
                            return v___x_4255_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4216_, 2);
                        lean_dec_ref(v_values_4215_);
                        v_a_4297_ = lean_ctor_get(v___x_4253_, 0);
                        v_isSharedCheck_4304_ = (!lean_is_exclusive(v___x_4253_)) as u8;
                        if v_isSharedCheck_4304_ == 0 {
                            v___x_4299_ = v___x_4253_;
                            v_isShared_4300_ = v_isSharedCheck_4304_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_4297_);
                            lean_dec(v___x_4253_);
                            v___x_4299_ = lean_box(0);
                            v_isShared_4300_ = v_isSharedCheck_4304_;
                            state = 14;
                            continue;
                        }
                    }
                }
                3 => {
                    lean_dec_ref(v_values_4215_);
                    v___x_4305_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4305_, 0, v_code_4216_);
                    return v___x_4305_;
                }
                4 => {
                    v_cases_4306_ = lean_ctor_get(v_code_4216_, 0);
                    lean_inc_ref(v_cases_4306_);
                    v_typeName_4307_ = lean_ctor_get(v_cases_4306_, 0);
                    v_resultType_4308_ = lean_ctor_get(v_cases_4306_, 1);
                    v_discr_4309_ = lean_ctor_get(v_cases_4306_, 2);
                    v_alts_4310_ = lean_ctor_get(v_cases_4306_, 3);
                    v_isSharedCheck_4349_ = (!lean_is_exclusive(v_cases_4306_)) as u8;
                    if v_isSharedCheck_4349_ == 0 {
                        v___x_4312_ = v_cases_4306_;
                        v_isShared_4313_ = v_isSharedCheck_4349_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_alts_4310_);
                        lean_inc(v_discr_4309_);
                        lean_inc(v_resultType_4308_);
                        lean_inc(v_typeName_4307_);
                        lean_dec(v_cases_4306_);
                        v___x_4312_ = lean_box(0);
                        v_isShared_4313_ = v_isSharedCheck_4349_;
                        state = 16;
                        continue;
                    }
                }
                5 => {
                    lean_dec_ref(v_values_4215_);
                    v___x_4350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4350_, 0, v_code_4216_);
                    return v___x_4350_;
                }
                6 => {
                    lean_dec_ref(v_values_4215_);
                    v___x_4351_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4351_, 0, v_code_4216_);
                    return v___x_4351_;
                }
                8 => {
                    v_fvarId_4352_ = lean_ctor_get(v_code_4216_, 0);
                    v_i_4353_ = lean_ctor_get(v_code_4216_, 1);
                    v_y_4354_ = lean_ctor_get(v_code_4216_, 2);
                    v_k_4355_ = lean_ctor_get(v_code_4216_, 3);
                    lean_inc_ref(v_k_4355_);
                    v___x_4356_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_k_4355_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4356_) == 0 {
                        v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
                        v_isSharedCheck_4381_ = (!lean_is_exclusive(v___x_4356_)) as u8;
                        if v_isSharedCheck_4381_ == 0 {
                            v___x_4359_ = v___x_4356_;
                            v_isShared_4360_ = v_isSharedCheck_4381_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_4357_);
                            lean_dec(v___x_4356_);
                            v___x_4359_ = lean_box(0);
                            v_isShared_4360_ = v_isSharedCheck_4381_;
                            state = 25;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4216_, 4);
                        return v___x_4356_;
                    }
                }
                9 => {
                    v_fvarId_4382_ = lean_ctor_get(v_code_4216_, 0);
                    v_i_4383_ = lean_ctor_get(v_code_4216_, 1);
                    v_offset_4384_ = lean_ctor_get(v_code_4216_, 2);
                    v_y_4385_ = lean_ctor_get(v_code_4216_, 3);
                    v_ty_4386_ = lean_ctor_get(v_code_4216_, 4);
                    v_k_4387_ = lean_ctor_get(v_code_4216_, 5);
                    lean_inc_ref(v_k_4387_);
                    v___x_4388_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4215_, v_k_4387_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    if lean_obj_tag(v___x_4388_) == 0 {
                        v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
                        v_isSharedCheck_4415_ = (!lean_is_exclusive(v___x_4388_)) as u8;
                        if v_isSharedCheck_4415_ == 0 {
                            v___x_4391_ = v___x_4388_;
                            v_isShared_4392_ = v_isSharedCheck_4415_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_4389_);
                            lean_dec(v___x_4388_);
                            v___x_4391_ = lean_box(0);
                            v_isShared_4392_ = v_isSharedCheck_4415_;
                            state = 30;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_4216_, 6);
                        return v___x_4388_;
                    }
                }
                _ => {
                    lean_dec_ref(v_code_4216_);
                    lean_dec_ref(v_values_4215_);
                    v___x_4416_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1_once), _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___closed__1);
                    v___x_4417_ = l_panic___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__2(v___x_4416_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                    return v___x_4417_;
                }
            },
            1 => {
                v___x_4229_ = lean_ptr_addr(v_k_4223_);
                v___x_4230_ = lean_ptr_addr(v_a_4225_);
                v___x_4231_ = lean_usize_dec_eq(v___x_4229_, v___x_4230_);
                if v___x_4231_ == 0 {
                    lean_inc_ref(v_decl_4222_);
                    v_isSharedCheck_4241_ = (!lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4241_ == 0 {
                        v_unused_4242_ = lean_ctor_get(v_code_4216_, 1);
                        lean_dec(v_unused_4242_);
                        v_unused_4243_ = lean_ctor_get(v_code_4216_, 0);
                        lean_dec(v_unused_4243_);
                        v___x_4233_ = v_code_4216_;
                        v_isShared_4234_ = v_isSharedCheck_4241_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_code_4216_);
                        v___x_4233_ = lean_box(0);
                        v_isShared_4234_ = v_isSharedCheck_4241_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4225_);
                    if v_isShared_4228_ == 0 {
                        lean_ctor_set(v___x_4227_, 0, v_code_4216_);
                        v___x_4245_ = v___x_4227_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_code_4216_);
                        v___x_4245_ = v_reuseFailAlloc_4246_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4234_ == 0 {
                    lean_ctor_set(v___x_4233_, 1, v_a_4225_);
                    v___x_4236_ = v___x_4233_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_decl_4222_);
                    lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_a_4225_);
                    v___x_4236_ = v_reuseFailAlloc_4240_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4228_ == 0 {
                    lean_ctor_set(v___x_4227_, 0, v___x_4236_);
                    v___x_4238_ = v___x_4227_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4236_);
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
                    v_isSharedCheck_4276_ = (!lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4276_ == 0 {
                        v_unused_4277_ = lean_ctor_get(v_code_4216_, 1);
                        lean_dec(v_unused_4277_);
                        v_unused_4278_ = lean_ctor_get(v_code_4216_, 0);
                        lean_dec(v_unused_4278_);
                        v___x_4268_ = v_code_4216_;
                        v_isShared_4269_ = v_isSharedCheck_4276_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_code_4216_);
                        v___x_4268_ = lean_box(0);
                        v_isShared_4269_ = v_isSharedCheck_4276_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4261_);
                    lean_dec(v_a_4259_);
                    if v_isShared_4264_ == 0 {
                        lean_ctor_set(v___x_4263_, 0, v_code_4216_);
                        v___x_4280_ = v___x_4263_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_code_4216_);
                        v___x_4280_ = v_reuseFailAlloc_4281_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4269_ == 0 {
                    lean_ctor_set(v___x_4268_, 1, v_a_4261_);
                    lean_ctor_set(v___x_4268_, 0, v_a_4259_);
                    v___x_4271_ = v___x_4268_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4275_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4259_);
                    lean_ctor_set(v_reuseFailAlloc_4275_, 1, v_a_4261_);
                    v___x_4271_ = v_reuseFailAlloc_4275_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4264_ == 0 {
                    lean_ctor_set(v___x_4263_, 0, v___x_4271_);
                    v___x_4273_ = v___x_4263_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
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
                    v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
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
                    v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
                    v___x_4302_ = v_reuseFailAlloc_4303_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4302_;
            }
            16 => {
                v___x_4314_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_4310_);
                v___x_4315_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__1(v_values_4215_, v___x_4314_, v_alts_4310_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
                if lean_obj_tag(v___x_4315_) == 0 {
                    v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
                    v_isSharedCheck_4340_ = (!lean_is_exclusive(v___x_4315_)) as u8;
                    if v_isSharedCheck_4340_ == 0 {
                        v___x_4318_ = v___x_4315_;
                        v_isShared_4319_ = v_isSharedCheck_4340_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_4316_);
                        lean_dec(v___x_4315_);
                        v___x_4318_ = lean_box(0);
                        v_isShared_4319_ = v_isSharedCheck_4340_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4312_);
                    lean_dec_ref(v_alts_4310_);
                    lean_dec(v_discr_4309_);
                    lean_dec_ref(v_resultType_4308_);
                    lean_dec(v_typeName_4307_);
                    lean_dec_ref_known(v_code_4216_, 1);
                    v_a_4341_ = lean_ctor_get(v___x_4315_, 0);
                    v_isSharedCheck_4348_ = (!lean_is_exclusive(v___x_4315_)) as u8;
                    if v_isSharedCheck_4348_ == 0 {
                        v___x_4343_ = v___x_4315_;
                        v_isShared_4344_ = v_isSharedCheck_4348_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_4341_);
                        lean_dec(v___x_4315_);
                        v___x_4343_ = lean_box(0);
                        v_isShared_4344_ = v_isSharedCheck_4348_;
                        state = 23;
                        continue;
                    }
                }
            }
            17 => {
                v___x_4320_ = lean_ptr_addr(v_alts_4310_);
                lean_dec_ref(v_alts_4310_);
                v___x_4321_ = lean_ptr_addr(v_a_4316_);
                v___x_4322_ = lean_usize_dec_eq(v___x_4320_, v___x_4321_);
                if v___x_4322_ == 0 {
                    v_isSharedCheck_4335_ = (!lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4335_ == 0 {
                        v_unused_4336_ = lean_ctor_get(v_code_4216_, 0);
                        lean_dec(v_unused_4336_);
                        v___x_4324_ = v_code_4216_;
                        v_isShared_4325_ = v_isSharedCheck_4335_;
                        state = 18;
                        continue;
                    } else {
                        lean_dec(v_code_4216_);
                        v___x_4324_ = lean_box(0);
                        v_isShared_4325_ = v_isSharedCheck_4335_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4316_);
                    lean_del_object(v___x_4312_);
                    lean_dec(v_discr_4309_);
                    lean_dec_ref(v_resultType_4308_);
                    lean_dec(v_typeName_4307_);
                    if v_isShared_4319_ == 0 {
                        lean_ctor_set(v___x_4318_, 0, v_code_4216_);
                        v___x_4338_ = v___x_4318_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_code_4216_);
                        v___x_4338_ = v_reuseFailAlloc_4339_;
                        state = 22;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4313_ == 0 {
                    lean_ctor_set(v___x_4312_, 3, v_a_4316_);
                    v___x_4327_ = v___x_4312_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_typeName_4307_);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_resultType_4308_);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 2, v_discr_4309_);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 3, v_a_4316_);
                    v___x_4327_ = v_reuseFailAlloc_4334_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4325_ == 0 {
                    lean_ctor_set(v___x_4324_, 0, v___x_4327_);
                    v___x_4329_ = v___x_4324_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4333_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4327_);
                    v___x_4329_ = v_reuseFailAlloc_4333_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_4319_ == 0 {
                    lean_ctor_set(v___x_4318_, 0, v___x_4329_);
                    v___x_4331_ = v___x_4318_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
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
                    v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
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
                    lean_inc(v_y_4354_);
                    lean_inc(v_i_4353_);
                    lean_inc(v_fvarId_4352_);
                    v_isSharedCheck_4373_ = (!lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4373_ == 0 {
                        v_unused_4374_ = lean_ctor_get(v_code_4216_, 3);
                        lean_dec(v_unused_4374_);
                        v_unused_4375_ = lean_ctor_get(v_code_4216_, 2);
                        lean_dec(v_unused_4375_);
                        v_unused_4376_ = lean_ctor_get(v_code_4216_, 1);
                        lean_dec(v_unused_4376_);
                        v_unused_4377_ = lean_ctor_get(v_code_4216_, 0);
                        lean_dec(v_unused_4377_);
                        v___x_4365_ = v_code_4216_;
                        v_isShared_4366_ = v_isSharedCheck_4373_;
                        state = 26;
                        continue;
                    } else {
                        lean_dec(v_code_4216_);
                        v___x_4365_ = lean_box(0);
                        v_isShared_4366_ = v_isSharedCheck_4373_;
                        state = 26;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4357_);
                    if v_isShared_4360_ == 0 {
                        lean_ctor_set(v___x_4359_, 0, v_code_4216_);
                        v___x_4379_ = v___x_4359_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_code_4216_);
                        v___x_4379_ = v_reuseFailAlloc_4380_;
                        state = 29;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_4366_ == 0 {
                    lean_ctor_set(v___x_4365_, 3, v_a_4357_);
                    v___x_4368_ = v___x_4365_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4372_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_fvarId_4352_);
                    lean_ctor_set(v_reuseFailAlloc_4372_, 1, v_i_4353_);
                    lean_ctor_set(v_reuseFailAlloc_4372_, 2, v_y_4354_);
                    lean_ctor_set(v_reuseFailAlloc_4372_, 3, v_a_4357_);
                    v___x_4368_ = v_reuseFailAlloc_4372_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_4360_ == 0 {
                    lean_ctor_set(v___x_4359_, 0, v___x_4368_);
                    v___x_4370_ = v___x_4359_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
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
                    lean_inc_ref(v_ty_4386_);
                    lean_inc(v_y_4385_);
                    lean_inc(v_offset_4384_);
                    lean_inc(v_i_4383_);
                    lean_inc(v_fvarId_4382_);
                    v_isSharedCheck_4405_ = (!lean_is_exclusive(v_code_4216_)) as u8;
                    if v_isSharedCheck_4405_ == 0 {
                        v_unused_4406_ = lean_ctor_get(v_code_4216_, 5);
                        lean_dec(v_unused_4406_);
                        v_unused_4407_ = lean_ctor_get(v_code_4216_, 4);
                        lean_dec(v_unused_4407_);
                        v_unused_4408_ = lean_ctor_get(v_code_4216_, 3);
                        lean_dec(v_unused_4408_);
                        v_unused_4409_ = lean_ctor_get(v_code_4216_, 2);
                        lean_dec(v_unused_4409_);
                        v_unused_4410_ = lean_ctor_get(v_code_4216_, 1);
                        lean_dec(v_unused_4410_);
                        v_unused_4411_ = lean_ctor_get(v_code_4216_, 0);
                        lean_dec(v_unused_4411_);
                        v___x_4397_ = v_code_4216_;
                        v_isShared_4398_ = v_isSharedCheck_4405_;
                        state = 31;
                        continue;
                    } else {
                        lean_dec(v_code_4216_);
                        v___x_4397_ = lean_box(0);
                        v_isShared_4398_ = v_isSharedCheck_4405_;
                        state = 31;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4389_);
                    if v_isShared_4392_ == 0 {
                        lean_ctor_set(v___x_4391_, 0, v_code_4216_);
                        v___x_4413_ = v___x_4391_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_code_4216_);
                        v___x_4413_ = v_reuseFailAlloc_4414_;
                        state = 34;
                        continue;
                    }
                }
            }
            31 => {
                if v_isShared_4398_ == 0 {
                    lean_ctor_set(v___x_4397_, 5, v_a_4389_);
                    v___x_4400_ = v___x_4397_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4404_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_fvarId_4382_);
                    lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_i_4383_);
                    lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_offset_4384_);
                    lean_ctor_set(v_reuseFailAlloc_4404_, 3, v_y_4385_);
                    lean_ctor_set(v_reuseFailAlloc_4404_, 4, v_ty_4386_);
                    lean_ctor_set(v_reuseFailAlloc_4404_, 5, v_a_4389_);
                    v___x_4400_ = v_reuseFailAlloc_4404_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_4392_ == 0 {
                    lean_ctor_set(v___x_4391_, 0, v___x_4400_);
                    v___x_4402_ = v___x_4391_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
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
    mut v_values_4418_: *mut LeanObject,
    mut v_code_4419_: *mut LeanObject,
    mut v_a_4420_: *mut LeanObject,
    mut v_a_4421_: *mut LeanObject,
    mut v_a_4422_: *mut LeanObject,
    mut v_a_4423_: *mut LeanObject,
    mut v_a_4424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4425_: *mut LeanObject = core::ptr::null_mut();
    v_res_4425_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4418_, v_code_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_);
    lean_dec(v_a_4423_);
    lean_dec_ref(v_a_4422_);
    lean_dec(v_a_4421_);
    lean_dec_ref(v_a_4420_);
    return v_res_4425_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__1(
    mut v_values_4426_: *mut LeanObject,
    mut v_i_4427_: *mut LeanObject,
    mut v_as_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
    mut v___y_4431_: *mut LeanObject,
    mut v___y_4432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: u8 = 0;
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: usize = 0;
    let mut v___x_4442_: usize = 0;
    let mut v___x_4443_: u8 = 0;
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4434_ = lean_array_get_size(v_as_4428_);
                v___x_4435_ = lean_nat_dec_lt(v_i_4427_, v___x_4434_);
                if v___x_4435_ == 0 {
                    lean_dec(v_i_4427_);
                    lean_dec_ref(v_values_4426_);
                    v___x_4436_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4436_, 0, v_as_4428_);
                    return v___x_4436_;
                } else {
                    v_a_4437_ = lean_array_fget_borrowed(v_as_4428_, v_i_4427_);
                    lean_inc_ref(v_values_4426_);
                    v___x_4438_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode___boxed as *mut core::ffi::c_void, 7, 1);
                    lean_closure_set(v___x_4438_, 0, v_values_4426_);
                    lean_inc(v_a_4437_);
                    v___x_4439_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__0___redArg(v_a_4437_, v___x_4438_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
                    if lean_obj_tag(v___x_4439_) == 0 {
                        v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
                        lean_inc(v_a_4440_);
                        lean_dec_ref_known(v___x_4439_, 1);
                        v___x_4441_ = lean_ptr_addr(v_a_4437_);
                        v___x_4442_ = lean_ptr_addr(v_a_4440_);
                        v___x_4443_ = lean_usize_dec_eq(v___x_4441_, v___x_4442_);
                        if v___x_4443_ == 0 {
                            v___x_4444_ = lean_unsigned_to_nat(1);
                            v___x_4445_ = lean_nat_add(v_i_4427_, v___x_4444_);
                            v___x_4446_ = lean_array_fset(v_as_4428_, v_i_4427_, v_a_4440_);
                            lean_dec(v_i_4427_);
                            v_i_4427_ = v___x_4445_;
                            v_as_4428_ = v___x_4446_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_4440_);
                            v___x_4448_ = lean_unsigned_to_nat(1);
                            v___x_4449_ = lean_nat_add(v_i_4427_, v___x_4448_);
                            lean_dec(v_i_4427_);
                            v_i_4427_ = v___x_4449_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_4428_);
                        lean_dec(v_i_4427_);
                        lean_dec_ref(v_values_4426_);
                        v_a_4451_ = lean_ctor_get(v___x_4439_, 0);
                        v_isSharedCheck_4458_ = (!lean_is_exclusive(v___x_4439_)) as u8;
                        if v_isSharedCheck_4458_ == 0 {
                            v___x_4453_ = v___x_4439_;
                            v_isShared_4454_ = v_isSharedCheck_4458_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4451_);
                            lean_dec(v___x_4439_);
                            v___x_4453_ = lean_box(0);
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
                    v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
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
    mut v_values_4459_: *mut LeanObject,
    mut v_i_4460_: *mut LeanObject,
    mut v_as_4461_: *mut LeanObject,
    mut v___y_4462_: *mut LeanObject,
    mut v___y_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4467_: *mut LeanObject = core::ptr::null_mut();
    v_res_4467_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode_spec__1(v_values_4459_, v_i_4460_, v_as_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
    lean_dec(v___y_4465_);
    lean_dec_ref(v___y_4464_);
    lean_dec(v___y_4463_);
    lean_dec_ref(v___y_4462_);
    return v_res_4467_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_applyOwnedness(
    mut v_decl_4468_: *mut LeanObject,
    mut v_values_4469_: *mut LeanObject,
    mut v_a_4470_: *mut LeanObject,
    mut v_a_4471_: *mut LeanObject,
    mut v_a_4472_: *mut LeanObject,
    mut v_a_4473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_4477_: u8 = 0;
    let mut v_inlineAttr_x3f_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v_code_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4485_: u8 = 0;
    let mut v_name_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_safe_4490_: u8 = 0;
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_a_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4521_: u8 = 0;
    let mut v_a_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v_unused_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_4475_ = lean_ctor_get(v_decl_4468_, 1);
                lean_inc_ref(v_value_4475_);
                if lean_obj_tag(v_value_4475_) == 0 {
                    v_toSignature_4476_ = lean_ctor_get(v_decl_4468_, 0);
                    v_recursive_4477_ = lean_ctor_get_uint8(
                        v_decl_4468_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_4478_ = lean_ctor_get(v_decl_4468_, 2);
                    v_isSharedCheck_4532_ = (!lean_is_exclusive(v_decl_4468_)) as u8;
                    if v_isSharedCheck_4532_ == 0 {
                        v_unused_4533_ = lean_ctor_get(v_decl_4468_, 1);
                        lean_dec(v_unused_4533_);
                        v___x_4480_ = v_decl_4468_;
                        v_isShared_4481_ = v_isSharedCheck_4532_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_inlineAttr_x3f_4478_);
                        lean_inc(v_toSignature_4476_);
                        lean_dec(v_decl_4468_);
                        v___x_4480_ = lean_box(0);
                        v_isShared_4481_ = v_isSharedCheck_4532_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_value_4475_);
                    lean_dec_ref(v_values_4469_);
                    v___x_4534_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4534_, 0, v_decl_4468_);
                    return v___x_4534_;
                }
            }
            1 => {
                v_code_4482_ = lean_ctor_get(v_value_4475_, 0);
                v_isSharedCheck_4531_ = (!lean_is_exclusive(v_value_4475_)) as u8;
                if v_isSharedCheck_4531_ == 0 {
                    v___x_4484_ = v_value_4475_;
                    v_isShared_4485_ = v_isSharedCheck_4531_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_code_4482_);
                    lean_dec(v_value_4475_);
                    v___x_4484_ = lean_box(0);
                    v_isShared_4485_ = v_isSharedCheck_4531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_name_4486_ = lean_ctor_get(v_toSignature_4476_, 0);
                v_levelParams_4487_ = lean_ctor_get(v_toSignature_4476_, 1);
                v_type_4488_ = lean_ctor_get(v_toSignature_4476_, 2);
                v_params_4489_ = lean_ctor_get(v_toSignature_4476_, 3);
                v_safe_4490_ = lean_ctor_get_uint8(
                    v_toSignature_4476_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_4530_ = (!lean_is_exclusive(v_toSignature_4476_)) as u8;
                if v_isSharedCheck_4530_ == 0 {
                    v___x_4492_ = v_toSignature_4476_;
                    v_isShared_4493_ = v_isSharedCheck_4530_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_params_4489_);
                    lean_inc(v_type_4488_);
                    lean_inc(v_levelParams_4487_);
                    lean_inc(v_name_4486_);
                    lean_dec(v_toSignature_4476_);
                    v___x_4492_ = lean_box(0);
                    v_isShared_4493_ = v_isSharedCheck_4530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4494_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_updateParams(v_values_4469_, v_params_4489_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_);
                if lean_obj_tag(v___x_4494_) == 0 {
                    v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
                    lean_inc(v_a_4495_);
                    lean_dec_ref_known(v___x_4494_, 1);
                    v___x_4496_ = l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_Decl_applyOwnedness_goCode(v_values_4469_, v_code_4482_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_);
                    if lean_obj_tag(v___x_4496_) == 0 {
                        v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
                        v_isSharedCheck_4513_ = (!lean_is_exclusive(v___x_4496_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v___x_4499_ = v___x_4496_;
                            v_isShared_4500_ = v_isSharedCheck_4513_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4497_);
                            lean_dec(v___x_4496_);
                            v___x_4499_ = lean_box(0);
                            v_isShared_4500_ = v_isSharedCheck_4513_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4495_);
                        lean_del_object(v___x_4492_);
                        lean_dec_ref(v_type_4488_);
                        lean_dec(v_levelParams_4487_);
                        lean_dec(v_name_4486_);
                        lean_del_object(v___x_4484_);
                        lean_del_object(v___x_4480_);
                        lean_dec(v_inlineAttr_x3f_4478_);
                        v_a_4514_ = lean_ctor_get(v___x_4496_, 0);
                        v_isSharedCheck_4521_ = (!lean_is_exclusive(v___x_4496_)) as u8;
                        if v_isSharedCheck_4521_ == 0 {
                            v___x_4516_ = v___x_4496_;
                            v_isShared_4517_ = v_isSharedCheck_4521_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4514_);
                            lean_dec(v___x_4496_);
                            v___x_4516_ = lean_box(0);
                            v_isShared_4517_ = v_isSharedCheck_4521_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4492_);
                    lean_dec_ref(v_type_4488_);
                    lean_dec(v_levelParams_4487_);
                    lean_dec(v_name_4486_);
                    lean_del_object(v___x_4484_);
                    lean_dec_ref(v_code_4482_);
                    lean_del_object(v___x_4480_);
                    lean_dec(v_inlineAttr_x3f_4478_);
                    lean_dec_ref(v_values_4469_);
                    v_a_4522_ = lean_ctor_get(v___x_4494_, 0);
                    v_isSharedCheck_4529_ = (!lean_is_exclusive(v___x_4494_)) as u8;
                    if v_isSharedCheck_4529_ == 0 {
                        v___x_4524_ = v___x_4494_;
                        v_isShared_4525_ = v_isSharedCheck_4529_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4522_);
                        lean_dec(v___x_4494_);
                        v___x_4524_ = lean_box(0);
                        v_isShared_4525_ = v_isSharedCheck_4529_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4493_ == 0 {
                    lean_ctor_set(v___x_4492_, 3, v_a_4495_);
                    v___x_4502_ = v___x_4492_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_name_4486_);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_levelParams_4487_);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 2, v_type_4488_);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 3, v_a_4495_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4512_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_safe_4490_,
                    );
                    v___x_4502_ = v_reuseFailAlloc_4512_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4485_ == 0 {
                    lean_ctor_set(v___x_4484_, 0, v_a_4497_);
                    v___x_4504_ = v___x_4484_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4497_);
                    v___x_4504_ = v_reuseFailAlloc_4511_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4481_ == 0 {
                    lean_ctor_set(v___x_4480_, 1, v___x_4504_);
                    lean_ctor_set(v___x_4480_, 0, v___x_4502_);
                    v___x_4506_ = v___x_4480_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4502_);
                    lean_ctor_set(v_reuseFailAlloc_4510_, 1, v___x_4504_);
                    lean_ctor_set(v_reuseFailAlloc_4510_, 2, v_inlineAttr_x3f_4478_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4510_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_4477_,
                    );
                    v___x_4506_ = v_reuseFailAlloc_4510_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4500_ == 0 {
                    lean_ctor_set(v___x_4499_, 0, v___x_4506_);
                    v___x_4508_ = v___x_4499_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
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
                    v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
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
                    v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
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
    mut v_decl_4535_: *mut LeanObject,
    mut v_values_4536_: *mut LeanObject,
    mut v_a_4537_: *mut LeanObject,
    mut v_a_4538_: *mut LeanObject,
    mut v_a_4539_: *mut LeanObject,
    mut v_a_4540_: *mut LeanObject,
    mut v_a_4541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4542_: *mut LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(
        v_decl_4535_,
        v_values_4536_,
        v_a_4537_,
        v_a_4538_,
        v_a_4539_,
        v_a_4540_,
    );
    lean_dec(v_a_4540_);
    lean_dec_ref(v_a_4539_);
    lean_dec(v_a_4538_);
    lean_dec_ref(v_a_4537_);
    return v_res_4542_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(
    builtin: u8,
) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedOwnedness_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedOwnedness_default();
    l_Lean_Compiler_LCNF_instInhabitedOwnedness =
        _init_l_Lean_Compiler_LCNF_instInhabitedOwnedness();
    l_Lean_Compiler_LCNF_instInhabitedState_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedState_default();
    lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedState_default);
    l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState = _init_l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState();
    lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_PropagateBorrow_0__Lean_Compiler_LCNF_instInhabitedState,
    );
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
}
