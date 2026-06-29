// Lean compiler output
// Module: Lean.Compiler.LCNF.ResetReuse
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.LiveVars Lean.Compiler.LCNF.DependsOn Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.PropagateBorrow
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_unzip___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_Lean_Name_str___override,
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
    l_Lean_Compiler_LCNF_Code_toCodeDecl_x21, l_Lean_Compiler_LCNF_CtorInfo_isScalar,
    l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg,
    l_Lean_Compiler_LCNF_getConfig___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
    l_Lean_Compiler_LCNF_mkFreshBinderName___redArg,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::DependsOn::{
    initialize_Lean_Compiler_LCNF_DependsOn,
    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn,
    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn,
    l_Lean_Compiler_LCNF_CodeDecl_dependsOn, runtime_initialize_Lean_Compiler_LCNF_DependsOn,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_addLetDecl;
use crate::r#gen::Lean::Compiler::LCNF::LiveVars::{
    initialize_Lean_Compiler_LCNF_LiveVars, l_Lean_Compiler_LCNF_Code_isFVarLiveIn,
    runtime_initialize_Lean_Compiler_LCNF_LiveVars,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::Compiler::LCNF::PropagateBorrow::{
    initialize_Lean_Compiler_LCNF_PropagateBorrow,
    l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows, l_Lean_Compiler_LCNF_Decl_applyOwnedness,
    l_Lean_Compiler_LCNF_instBEqOwnedness_beq,
    runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_getPrefix;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash,
    l_Lean_instSingletonFVarIdFVarIdSet___lam__0,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value: crate::leanh::LeanStringObject<69> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 117, 112, 100, 97, 116, 101, 67, 111, 110, 116, 73, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value: crate::leanh::LeanStringObject<65> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 46, 103, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 120, 0],
};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        7699194985028780469 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 111, 98, 106, 0],
};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        930430701391226905 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value: crate::leanh::LeanStringObject<65> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 46, 103, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value: crate::leanh::LeanStringObject<82> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 100, 101, 46, 105, 110, 115, 101, 114, 116, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value: crate::leanh::LeanStringObject<100> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 100, m_capacity: 100, m_length: 99, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 68, 101, 99, 108, 46, 105, 110, 115, 101, 114, 116, 82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 67, 111, 114, 101, 46, 99, 111, 108, 108, 101, 99, 116, 82, 101, 115, 101, 116, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [114, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0],
};
static mut l_Lean_Compiler_LCNF_insertResetReuse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5257689452882282900 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_insertResetReuse___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_insertResetReuse___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_insertResetReuse___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_insertResetReuse: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value) as *mut crate::leanh::LeanObject,16226545838414566954 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [82, 101, 115, 101, 116, 82, 101, 117, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4716849658683630864 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16911656791395636841 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18416815962956886572 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1676712919186840246 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7077680281623442975 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7668881657817563838 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5633212236934799583 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12968239667096334226 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1332082790119883104 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10346552649561275353 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7328009740721607944 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(
    mut v_c_u2081_3129_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_3130_: *mut crate::leanh::LeanObject,
    mut v_a_3131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: u8 = 0;
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relaxedReuse_3148_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: u8 = 0;
    let mut v___x_3157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3133_ = crate::leanh::lean_ctor_get(v_c_u2081_3129_, 0);
                v_size_3134_ = crate::leanh::lean_ctor_get(v_c_u2081_3129_, 2);
                v_usize_3135_ = crate::leanh::lean_ctor_get(v_c_u2081_3129_, 3);
                v_ssize_3136_ = crate::leanh::lean_ctor_get(v_c_u2081_3129_, 4);
                v_name_3137_ = crate::leanh::lean_ctor_get(v_c_u2082_3130_, 0);
                v_size_3138_ = crate::leanh::lean_ctor_get(v_c_u2082_3130_, 2);
                v_usize_3139_ = crate::leanh::lean_ctor_get(v_c_u2082_3130_, 3);
                v_ssize_3140_ = crate::leanh::lean_ctor_get(v_c_u2082_3130_, 4);
                v___x_3156_ = lean_nat_dec_eq(v_size_3134_, v_size_3138_);
                if v___x_3156_ == 0 {
                    v___y_3142_ = v___x_3156_;
                    state = 1;
                    continue;
                } else {
                    v___x_3157_ = lean_nat_dec_eq(v_usize_3135_, v_usize_3139_);
                    v___y_3142_ = v___x_3157_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3142_ == 0 {
                    v___x_3143_ = crate::leanh::lean_box((v___y_3142_) as usize);
                    v___x_3144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3144_, 0, v___x_3143_);
                    return v___x_3144_;
                } else {
                    v___x_3145_ = lean_nat_dec_eq(v_ssize_3136_, v_ssize_3140_);
                    if v___x_3145_ == 0 {
                        v___x_3146_ = crate::leanh::lean_box((v___x_3145_) as usize);
                        v___x_3147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3147_, 0, v___x_3146_);
                        return v___x_3147_;
                    } else {
                        v_relaxedReuse_3148_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_3131_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        if v_relaxedReuse_3148_ == 0 {
                            v___x_3149_ = l_Lean_Name_getPrefix(v_name_3133_);
                            v___x_3150_ = l_Lean_Name_getPrefix(v_name_3137_);
                            v___x_3151_ = lean_name_eq(v___x_3149_, v___x_3150_);
                            crate::leanh::lean_dec(v___x_3150_);
                            crate::leanh::lean_dec(v___x_3149_);
                            v___x_3152_ = crate::leanh::lean_box((v___x_3151_) as usize);
                            v___x_3153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3153_, 0, v___x_3152_);
                            return v___x_3153_;
                        } else {
                            v___x_3154_ = crate::leanh::lean_box((v_relaxedReuse_3148_) as usize);
                            v___x_3155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3155_, 0, v___x_3154_);
                            return v___x_3155_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(
    mut v_c_u2081_3158_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
    mut v_a_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3162_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(
        v_c_u2081_3158_,
        v_c_u2082_3159_,
        v_a_3160_,
    );
    crate::leanh::lean_dec_ref(v_a_3160_);
    crate::leanh::lean_dec_ref(v_c_u2082_3159_);
    crate::leanh::lean_dec_ref(v_c_u2081_3158_);
    return v_res_3162_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(
    mut v_c_u2081_3163_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_a_3166_: *mut crate::leanh::LeanObject,
    mut v_a_3167_: *mut crate::leanh::LeanObject,
    mut v_a_3168_: *mut crate::leanh::LeanObject,
    mut v_a_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3171_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(
        v_c_u2081_3163_,
        v_c_u2082_3164_,
        v_a_3165_,
    );
    return v___x_3171_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(
    mut v_c_u2081_3172_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
    mut v_a_3177_: *mut crate::leanh::LeanObject,
    mut v_a_3178_: *mut crate::leanh::LeanObject,
    mut v_a_3179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3180_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(
        v_c_u2081_3172_,
        v_c_u2082_3173_,
        v_a_3174_,
        v_a_3175_,
        v_a_3176_,
        v_a_3177_,
        v_a_3178_,
    );
    crate::leanh::lean_dec(v_a_3178_);
    crate::leanh::lean_dec_ref(v_a_3177_);
    crate::leanh::lean_dec(v_a_3176_);
    crate::leanh::lean_dec_ref(v_a_3175_);
    crate::leanh::lean_dec_ref(v_a_3174_);
    crate::leanh::lean_dec_ref(v_c_u2082_3173_);
    crate::leanh::lean_dec_ref(v_c_u2081_3172_);
    return v_res_3180_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3181_ = 1;
    v___x_3182_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_3181_);
    return v___x_3182_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(
    mut v_msg_3183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3184_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
    v___x_3185_ = lean_panic_fn_borrowed(v___x_3184_, v_msg_3183_);
    return v___x_3185_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3186_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3186_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(
    mut v_msg_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
    mut v___y_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v_toFunctor_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___f_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796__overap_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3233_: u8 = 0;
    let mut v_unused_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3235_: u8 = 0;
    let mut v_unused_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3196_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
                v___x_3197_ = l_StateRefT_x27_instMonad___redArg(v___x_3196_);
                v_toApplicative_3198_ = crate::leanh::lean_ctor_get(v___x_3197_, 0);
                v_isSharedCheck_3235_ = (!crate::leanh::lean_is_exclusive(v___x_3197_)) as u8;
                if v_isSharedCheck_3235_ == 0 {
                    v_unused_3236_ = crate::leanh::lean_ctor_get(v___x_3197_, 1);
                    crate::leanh::lean_dec(v_unused_3236_);
                    v___x_3200_ = v___x_3197_;
                    v_isShared_3201_ = v_isSharedCheck_3235_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3198_);
                    crate::leanh::lean_dec(v___x_3197_);
                    v___x_3200_ = crate::leanh::lean_box(0);
                    v_isShared_3201_ = v_isSharedCheck_3235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3202_ = crate::leanh::lean_ctor_get(v_toApplicative_3198_, 0);
                v_toSeq_3203_ = crate::leanh::lean_ctor_get(v_toApplicative_3198_, 2);
                v_toSeqLeft_3204_ = crate::leanh::lean_ctor_get(v_toApplicative_3198_, 3);
                v_toSeqRight_3205_ = crate::leanh::lean_ctor_get(v_toApplicative_3198_, 4);
                v_isSharedCheck_3233_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3198_)) as u8;
                if v_isSharedCheck_3233_ == 0 {
                    v_unused_3234_ = crate::leanh::lean_ctor_get(v_toApplicative_3198_, 1);
                    crate::leanh::lean_dec(v_unused_3234_);
                    v___x_3207_ = v_toApplicative_3198_;
                    v_isShared_3208_ = v_isSharedCheck_3233_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3205_);
                    crate::leanh::lean_inc(v_toSeqLeft_3204_);
                    crate::leanh::lean_inc(v_toSeq_3203_);
                    crate::leanh::lean_inc(v_toFunctor_3202_);
                    crate::leanh::lean_dec(v_toApplicative_3198_);
                    v___x_3207_ = crate::leanh::lean_box(0);
                    v_isShared_3208_ = v_isSharedCheck_3233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3209_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1;
                v___f_3210_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_3202_);
                v___f_3211_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3211_, 0, v_toFunctor_3202_);
                v___f_3212_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3212_, 0, v_toFunctor_3202_);
                v___x_3213_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3213_, 0, v___f_3211_);
                crate::leanh::lean_ctor_set(v___x_3213_, 1, v___f_3212_);
                v___f_3214_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3214_, 0, v_toSeqRight_3205_);
                v___f_3215_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3215_, 0, v_toSeqLeft_3204_);
                v___f_3216_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3216_, 0, v_toSeq_3203_);
                if v_isShared_3208_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3207_, 4, v___f_3214_);
                    crate::leanh::lean_ctor_set(v___x_3207_, 3, v___f_3215_);
                    crate::leanh::lean_ctor_set(v___x_3207_, 2, v___f_3216_);
                    crate::leanh::lean_ctor_set(v___x_3207_, 1, v___f_3209_);
                    crate::leanh::lean_ctor_set(v___x_3207_, 0, v___x_3213_);
                    v___x_3218_ = v___x_3207_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3232_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 1, v___f_3209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 2, v___f_3216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 3, v___f_3215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 4, v___f_3214_);
                    v___x_3218_ = v_reuseFailAlloc_3232_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3200_, 1, v___f_3210_);
                    crate::leanh::lean_ctor_set(v___x_3200_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3200_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___f_3210_);
                    v___x_3220_ = v_reuseFailAlloc_3231_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3221_ = l_StateRefT_x27_instMonad___redArg(v___x_3220_);
                v___x_3222_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
                v___x_3223_ = 0;
                v___x_3224_ = crate::leanh::lean_box((v___x_3223_) as usize);
                v___x_3225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3225_, 0, v___x_3222_);
                crate::leanh::lean_ctor_set(v___x_3225_, 1, v___x_3224_);
                v___x_3226_ = l_instInhabitedOfMonad___redArg(v___x_3221_, v___x_3225_);
                v___f_3227_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3227_, 0, v___x_3226_);
                v___f_3228_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3228_, 0, v___f_3227_);
                v___x_3796__overap_3229_ = lean_panic_fn_borrowed(v___f_3228_, v_msg_3189_);
                crate::leanh::lean_dec_ref(v___f_3228_);
                crate::leanh::lean_inc(v___y_3194_);
                crate::leanh::lean_inc_ref(v___y_3193_);
                crate::leanh::lean_inc(v___y_3192_);
                crate::leanh::lean_inc_ref(v___y_3191_);
                crate::leanh::lean_inc_ref(v___y_3190_);
                v___x_3230_ = crate::leanh::lean_apply_6(
                    v___x_3796__overap_3229_,
                    v___y_3190_,
                    v___y_3191_,
                    v___y_3192_,
                    v___y_3193_,
                    v___y_3194_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(
    mut v_msg_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3244_ =
        l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(
            v_msg_3237_,
            v___y_3238_,
            v___y_3239_,
            v___y_3240_,
            v___y_3241_,
            v___y_3242_,
        );
    crate::leanh::lean_dec(v___y_3242_);
    crate::leanh::lean_dec_ref(v___y_3241_);
    crate::leanh::lean_dec(v___y_3240_);
    crate::leanh::lean_dec_ref(v___y_3239_);
    crate::leanh::lean_dec_ref(v___y_3238_);
    return v_res_3244_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(
    mut v_as_3245_: *mut crate::leanh::LeanObject,
    mut v_i_3246_: usize,
    mut v_stop_3247_: usize,
) -> u8 {
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: u8 = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: usize = 0;
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3248_ = lean_usize_dec_eq(v_i_3246_, v_stop_3247_);
                if v___x_3248_ == 0 {
                    v___x_3249_ = lean_array_uget_borrowed(v_as_3245_, v_i_3246_);
                    v___x_3250_ = (crate::leanh::lean_unbox(v___x_3249_) as u8);
                    if v___x_3250_ == 0 {
                        v___x_3251_ = 1usize;
                        v___x_3252_ = lean_usize_add(v_i_3246_, v___x_3251_);
                        v_i_3246_ = v___x_3252_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3254_ = (crate::leanh::lean_unbox(v___x_3249_) as u8);
                        return v___x_3254_;
                    }
                } else {
                    v___x_3255_ = 0;
                    return v___x_3255_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(
    mut v_as_3256_: *mut crate::leanh::LeanObject,
    mut v_i_3257_: *mut crate::leanh::LeanObject,
    mut v_stop_3258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3259_: usize = 0;
    let mut v_stop_boxed_3260_: usize = 0;
    let mut v_res_3261_: u8 = 0;
    let mut v_r_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3259_ = crate::leanh::lean_unbox_usize(v_i_3257_);
    crate::leanh::lean_dec(v_i_3257_);
    v_stop_boxed_3260_ = crate::leanh::lean_unbox_usize(v_stop_3258_);
    crate::leanh::lean_dec(v_stop_3258_);
    v_res_3261_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_as_3256_, v_i_boxed_3259_, v_stop_boxed_3260_);
    crate::leanh::lean_dec_ref(v_as_3256_);
    v_r_3262_ = crate::leanh::lean_box((v_res_3261_) as usize);
    return v_r_3262_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3266_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2;
    v___x_3267_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_3268_ = crate::leanh::lean_unsigned_to_nat(633);
    v___x_3269_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1;
    v___x_3270_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0;
    v___x_3271_ = l_mkPanicMessageWithDecl(
        v___x_3270_,
        v___x_3269_,
        v___x_3268_,
        v___x_3267_,
        v___x_3266_,
    );
    return v___x_3271_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3274_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2;
    v___x_3275_ = crate::leanh::lean_unsigned_to_nat(61);
    v___x_3276_ = crate::leanh::lean_unsigned_to_nat(125);
    v___x_3277_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5;
    v___x_3278_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4;
    v___x_3279_ = l_mkPanicMessageWithDecl(
        v___x_3278_,
        v___x_3277_,
        v___x_3276_,
        v___x_3275_,
        v___x_3274_,
    );
    return v___x_3279_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(
    mut v_info_3280_: *mut crate::leanh::LeanObject,
    mut v_w_3281_: *mut crate::leanh::LeanObject,
    mut v_c_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_3284_: *mut crate::leanh::LeanObject,
    mut v_a_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
    mut v_a_3287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3290_: u8 = 0;
    let mut v___y_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: usize = 0;
    let mut v___x_3309_: usize = 0;
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: u8 = 0;
    let mut v_reuseFailAlloc_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v_unused_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: u8 = 0;
    let mut v_fst_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: usize = 0;
    let mut v___x_3327_: usize = 0;
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: u8 = 0;
    let mut v_reuseFailAlloc_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3336_: u8 = 0;
    let mut v_unused_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    let mut v_fst_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3349_: u8 = 0;
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v_reuseFailAlloc_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut v_unused_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: u8 = 0;
    let mut v_fst_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: usize = 0;
    let mut v___x_3365_: usize = 0;
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: u8 = 0;
    let mut v_reuseFailAlloc_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut v_unused_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: u8 = 0;
    let mut v_fst_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: usize = 0;
    let mut v___x_3389_: usize = 0;
    let mut v___x_3390_: u8 = 0;
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3393_: u8 = 0;
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v_reuseFailAlloc_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3398_: u8 = 0;
    let mut v_unused_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: u8 = 0;
    let mut v_fst_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: usize = 0;
    let mut v___x_3413_: usize = 0;
    let mut v___x_3414_: u8 = 0;
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: u8 = 0;
    let mut v_reuseFailAlloc_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3422_: u8 = 0;
    let mut v_unused_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: u8 = 0;
    let mut v_fst_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: usize = 0;
    let mut v___x_3434_: usize = 0;
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: u8 = 0;
    let mut v_reuseFailAlloc_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v_unused_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: u8 = 0;
    let mut v_fst_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_3452_: u8 = 0;
    let mut v_persistent_3453_: u8 = 0;
    let mut v_k_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: usize = 0;
    let mut v___x_3456_: usize = 0;
    let mut v___x_3457_: u8 = 0;
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: u8 = 0;
    let mut v_reuseFailAlloc_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_unused_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    let mut v_fst_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_3474_: u8 = 0;
    let mut v_persistent_3475_: u8 = 0;
    let mut v_objs_x3f_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: usize = 0;
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: u8 = 0;
    let mut v_reuseFailAlloc_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_unused_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: u8 = 0;
    let mut v_fst_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: usize = 0;
    let mut v___x_3499_: usize = 0;
    let mut v___x_3500_: u8 = 0;
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u8 = 0;
    let mut v_reuseFailAlloc_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3508_: u8 = 0;
    let mut v_unused_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    let mut v_snd_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: u8 = 0;
    let mut v_decl_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v_i_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3529_: u8 = 0;
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v_cidx_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3544_: u8 = 0;
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v_a_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3562_: u8 = 0;
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3566_: u8 = 0;
    let mut v___x_3567_: u8 = 0;
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: u8 = 0;
    let mut v_reuseFailAlloc_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_unused_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3582_: u8 = 0;
    let mut v_isSharedCheck_3583_: u8 = 0;
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v_unused_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v_fst_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3605_: u8 = 0;
    let mut v___y_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3615_: u8 = 0;
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v_unused_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: usize = 0;
    let mut v___x_3626_: u8 = 0;
    let mut v___x_3627_: usize = 0;
    let mut v___x_3628_: usize = 0;
    let mut v___x_3629_: u8 = 0;
    let mut v_isSharedCheck_3630_: u8 = 0;
    let mut v_a_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut v_isSharedCheck_3639_: u8 = 0;
    let mut v_unused_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3652_: u8 = 0;
    let mut v_sz_3653_: usize = 0;
    let mut v___x_3654_: usize = 0;
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v___y_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3662_: u8 = 0;
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: u8 = 0;
    let mut v___x_3676_: usize = 0;
    let mut v___x_3677_: u8 = 0;
    let mut v___x_3678_: usize = 0;
    let mut v___x_3679_: usize = 0;
    let mut v___x_3680_: u8 = 0;
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3683_: u8 = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_unused_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_a_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut v___x_3702_: u8 = 0;
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_c_3282_) {
                0 => {
                    v_decl_3516_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                    crate::leanh::lean_inc_ref(v_decl_3516_);
                    v_value_3517_ = crate::leanh::lean_ctor_get(v_decl_3516_, 3);
                    crate::leanh::lean_inc(v_value_3517_);
                    if crate::leanh::lean_obj_tag(v_value_3517_) == 5 {
                        v_k_3518_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                        v_fvarId_3519_ = crate::leanh::lean_ctor_get(v_decl_3516_, 0);
                        v_binderName_3520_ = crate::leanh::lean_ctor_get(v_decl_3516_, 1);
                        v_type_3521_ = crate::leanh::lean_ctor_get(v_decl_3516_, 2);
                        v_isSharedCheck_3584_ =
                            (!crate::leanh::lean_is_exclusive(v_decl_3516_)) as u8;
                        if v_isSharedCheck_3584_ == 0 {
                            v_unused_3585_ = crate::leanh::lean_ctor_get(v_decl_3516_, 3);
                            crate::leanh::lean_dec(v_unused_3585_);
                            v___x_3523_ = v_decl_3516_;
                            v_isShared_3524_ = v_isSharedCheck_3584_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_type_3521_);
                            crate::leanh::lean_inc(v_binderName_3520_);
                            crate::leanh::lean_inc(v_fvarId_3519_);
                            crate::leanh::lean_dec(v_decl_3516_);
                            v___x_3523_ = crate::leanh::lean_box(0);
                            v_isShared_3524_ = v_isSharedCheck_3584_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_value_3517_);
                        crate::leanh::lean_dec_ref(v_decl_3516_);
                        v_k_3586_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                        crate::leanh::lean_inc_ref(v_k_3586_);
                        v_k_3296_ = v_k_3586_;
                        v___y_3297_ = v_a_3283_;
                        v___y_3298_ = v_a_3284_;
                        v___y_3299_ = v_a_3285_;
                        v___y_3300_ = v_a_3286_;
                        v___y_3301_ = v_a_3287_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_decl_3587_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                    v_k_3588_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                    v_params_3589_ = crate::leanh::lean_ctor_get(v_decl_3587_, 2);
                    v_type_3590_ = crate::leanh::lean_ctor_get(v_decl_3587_, 3);
                    v_value_3591_ = crate::leanh::lean_ctor_get(v_decl_3587_, 4);
                    crate::leanh::lean_inc_ref(v_value_3591_);
                    crate::leanh::lean_inc(v_w_3281_);
                    v___x_3592_ =
                        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(
                            v_info_3280_,
                            v_w_3281_,
                            v_value_3591_,
                            v_a_3283_,
                            v_a_3284_,
                            v_a_3285_,
                            v_a_3286_,
                            v_a_3287_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3592_) == 0 {
                        v_a_3593_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                        crate::leanh::lean_inc(v_a_3593_);
                        crate::leanh::lean_dec_ref_known(v___x_3592_, 1);
                        v_snd_3594_ = crate::leanh::lean_ctor_get(v_a_3593_, 1);
                        crate::leanh::lean_inc(v_snd_3594_);
                        v___x_3595_ = (crate::leanh::lean_unbox(v_snd_3594_) as u8);
                        if v___x_3595_ == 0 {
                            crate::leanh::lean_dec(v_snd_3594_);
                            crate::leanh::lean_dec(v_a_3593_);
                            crate::leanh::lean_inc_ref(v_k_3588_);
                            v_k_3296_ = v_k_3588_;
                            v___y_3297_ = v_a_3283_;
                            v___y_3298_ = v_a_3284_;
                            v___y_3299_ = v_a_3285_;
                            v___y_3300_ = v_a_3286_;
                            v___y_3301_ = v_a_3287_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_w_3281_);
                            v_fst_3596_ = crate::leanh::lean_ctor_get(v_a_3593_, 0);
                            v_isSharedCheck_3639_ =
                                (!crate::leanh::lean_is_exclusive(v_a_3593_)) as u8;
                            if v_isSharedCheck_3639_ == 0 {
                                v_unused_3640_ = crate::leanh::lean_ctor_get(v_a_3593_, 1);
                                crate::leanh::lean_dec(v_unused_3640_);
                                v___x_3598_ = v_a_3593_;
                                v_isShared_3599_ = v_isSharedCheck_3639_;
                                state = 36;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_fst_3596_);
                                crate::leanh::lean_dec(v_a_3593_);
                                v___x_3598_ = crate::leanh::lean_box(0);
                                v_isShared_3599_ = v_isSharedCheck_3639_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_c_3282_, 2);
                        crate::leanh::lean_dec(v_w_3281_);
                        return v___x_3592_;
                    }
                }
                3 => {
                    crate::leanh::lean_dec(v_w_3281_);
                    v___x_3641_ = 0;
                    v___x_3642_ = crate::leanh::lean_box((v___x_3641_) as usize);
                    v___x_3643_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3643_, 0, v_c_3282_);
                    crate::leanh::lean_ctor_set(v___x_3643_, 1, v___x_3642_);
                    v___x_3644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                    return v___x_3644_;
                }
                4 => {
                    v_cases_3645_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                    crate::leanh::lean_inc_ref(v_cases_3645_);
                    v_typeName_3646_ = crate::leanh::lean_ctor_get(v_cases_3645_, 0);
                    v_resultType_3647_ = crate::leanh::lean_ctor_get(v_cases_3645_, 1);
                    v_discr_3648_ = crate::leanh::lean_ctor_get(v_cases_3645_, 2);
                    v_alts_3649_ = crate::leanh::lean_ctor_get(v_cases_3645_, 3);
                    v_isSharedCheck_3701_ = (!crate::leanh::lean_is_exclusive(v_cases_3645_)) as u8;
                    if v_isSharedCheck_3701_ == 0 {
                        v___x_3651_ = v_cases_3645_;
                        v_isShared_3652_ = v_isSharedCheck_3701_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_3649_);
                        crate::leanh::lean_inc(v_discr_3648_);
                        crate::leanh::lean_inc(v_resultType_3647_);
                        crate::leanh::lean_inc(v_typeName_3646_);
                        crate::leanh::lean_dec(v_cases_3645_);
                        v___x_3651_ = crate::leanh::lean_box(0);
                        v_isShared_3652_ = v_isSharedCheck_3701_;
                        state = 46;
                        continue;
                    }
                }
                5 => {
                    crate::leanh::lean_dec(v_w_3281_);
                    v___x_3702_ = 0;
                    v___x_3703_ = crate::leanh::lean_box((v___x_3702_) as usize);
                    v___x_3704_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3704_, 0, v_c_3282_);
                    crate::leanh::lean_ctor_set(v___x_3704_, 1, v___x_3703_);
                    v___x_3705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3705_, 0, v___x_3704_);
                    return v___x_3705_;
                }
                6 => {
                    crate::leanh::lean_dec(v_w_3281_);
                    v___x_3706_ = 0;
                    v___x_3707_ = crate::leanh::lean_box((v___x_3706_) as usize);
                    v___x_3708_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3708_, 0, v_c_3282_);
                    crate::leanh::lean_ctor_set(v___x_3708_, 1, v___x_3707_);
                    v___x_3709_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3709_, 0, v___x_3708_);
                    return v___x_3709_;
                }
                8 => {
                    v_k_3710_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                    crate::leanh::lean_inc_ref(v_k_3710_);
                    v_k_3296_ = v_k_3710_;
                    v___y_3297_ = v_a_3283_;
                    v___y_3298_ = v_a_3284_;
                    v___y_3299_ = v_a_3285_;
                    v___y_3300_ = v_a_3286_;
                    v___y_3301_ = v_a_3287_;
                    state = 2;
                    continue;
                }
                9 => {
                    v_k_3711_ = crate::leanh::lean_ctor_get(v_c_3282_, 5);
                    crate::leanh::lean_inc_ref(v_k_3711_);
                    v_k_3296_ = v_k_3711_;
                    v___y_3297_ = v_a_3283_;
                    v___y_3298_ = v_a_3284_;
                    v___y_3299_ = v_a_3285_;
                    v___y_3300_ = v_a_3286_;
                    v___y_3301_ = v_a_3287_;
                    state = 2;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_c_3282_);
                    crate::leanh::lean_dec(v_w_3281_);
                    v___x_3712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6);
                    v___x_3713_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_3712_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
                    return v___x_3713_;
                }
            },
            1 => {
                v___x_3292_ = crate::leanh::lean_box((v___y_3290_) as usize);
                v___x_3293_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3293_, 0, v___y_3291_);
                crate::leanh::lean_ctor_set(v___x_3293_, 1, v___x_3292_);
                v___x_3294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3294_, 0, v___x_3293_);
                return v___x_3294_;
            }
            2 => {
                v___x_3302_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(
                    v_info_3280_,
                    v_w_3281_,
                    v_k_3296_,
                    v___y_3297_,
                    v___y_3298_,
                    v___y_3299_,
                    v___y_3300_,
                    v___y_3301_,
                );
                if crate::leanh::lean_obj_tag(v___x_3302_) == 0 {
                    v_a_3303_ = crate::leanh::lean_ctor_get(v___x_3302_, 0);
                    crate::leanh::lean_inc(v_a_3303_);
                    crate::leanh::lean_dec_ref_known(v___x_3302_, 1);
                    match crate::leanh::lean_obj_tag(v_c_3282_) {
                        0 => {
                            v_fst_3304_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3304_);
                            v_snd_3305_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3305_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_decl_3306_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_k_3307_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v___x_3308_ = lean_ptr_addr(v_k_3307_);
                            v___x_3309_ = lean_ptr_addr(v_fst_3304_);
                            v___x_3310_ = lean_usize_dec_eq(v___x_3308_, v___x_3309_);
                            if v___x_3310_ == 0 {
                                crate::leanh::lean_inc_ref(v_decl_3306_);
                                v_isSharedCheck_3318_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3318_ == 0 {
                                    v_unused_3319_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3319_);
                                    v_unused_3320_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3320_);
                                    v___x_3312_ = v_c_3282_;
                                    v_isShared_3313_ = v_isSharedCheck_3318_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3312_ = crate::leanh::lean_box(0);
                                    v_isShared_3313_ = v_isSharedCheck_3318_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3304_);
                                v___x_3321_ = (crate::leanh::lean_unbox(v_snd_3305_) as u8);
                                crate::leanh::lean_dec(v_snd_3305_);
                                v___y_3290_ = v___x_3321_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        1 => {
                            v_fst_3322_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3322_);
                            v_snd_3323_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3323_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_decl_3324_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_k_3325_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v___x_3326_ = lean_ptr_addr(v_k_3325_);
                            v___x_3327_ = lean_ptr_addr(v_fst_3322_);
                            v___x_3328_ = lean_usize_dec_eq(v___x_3326_, v___x_3327_);
                            if v___x_3328_ == 0 {
                                crate::leanh::lean_inc_ref(v_decl_3324_);
                                v_isSharedCheck_3336_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3336_ == 0 {
                                    v_unused_3337_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3337_);
                                    v_unused_3338_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3338_);
                                    v___x_3330_ = v_c_3282_;
                                    v_isShared_3331_ = v_isSharedCheck_3336_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3330_ = crate::leanh::lean_box(0);
                                    v_isShared_3331_ = v_isSharedCheck_3336_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3322_);
                                v___x_3339_ = (crate::leanh::lean_unbox(v_snd_3323_) as u8);
                                crate::leanh::lean_dec(v_snd_3323_);
                                v___y_3290_ = v___x_3339_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        2 => {
                            v_fst_3340_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3340_);
                            v_snd_3341_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3341_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_decl_3342_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_k_3343_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v___x_3344_ = lean_ptr_addr(v_k_3343_);
                            v___x_3345_ = lean_ptr_addr(v_fst_3340_);
                            v___x_3346_ = lean_usize_dec_eq(v___x_3344_, v___x_3345_);
                            if v___x_3346_ == 0 {
                                crate::leanh::lean_inc_ref(v_decl_3342_);
                                v_isSharedCheck_3354_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3354_ == 0 {
                                    v_unused_3355_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3355_);
                                    v_unused_3356_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3356_);
                                    v___x_3348_ = v_c_3282_;
                                    v_isShared_3349_ = v_isSharedCheck_3354_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3348_ = crate::leanh::lean_box(0);
                                    v_isShared_3349_ = v_isSharedCheck_3354_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3340_);
                                v___x_3357_ = (crate::leanh::lean_unbox(v_snd_3341_) as u8);
                                crate::leanh::lean_dec(v_snd_3341_);
                                v___y_3290_ = v___x_3357_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        7 => {
                            v_fst_3358_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3358_);
                            v_snd_3359_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3359_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_fvarId_3360_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_i_3361_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v_y_3362_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                            v_k_3363_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                            v___x_3364_ = lean_ptr_addr(v_k_3363_);
                            v___x_3365_ = lean_ptr_addr(v_fst_3358_);
                            v___x_3366_ = lean_usize_dec_eq(v___x_3364_, v___x_3365_);
                            if v___x_3366_ == 0 {
                                crate::leanh::lean_inc(v_y_3362_);
                                crate::leanh::lean_inc(v_i_3361_);
                                crate::leanh::lean_inc(v_fvarId_3360_);
                                v_isSharedCheck_3374_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3374_ == 0 {
                                    v_unused_3375_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                                    crate::leanh::lean_dec(v_unused_3375_);
                                    v_unused_3376_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                                    crate::leanh::lean_dec(v_unused_3376_);
                                    v_unused_3377_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3377_);
                                    v_unused_3378_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3378_);
                                    v___x_3368_ = v_c_3282_;
                                    v_isShared_3369_ = v_isSharedCheck_3374_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3368_ = crate::leanh::lean_box(0);
                                    v_isShared_3369_ = v_isSharedCheck_3374_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3358_);
                                v___x_3379_ = (crate::leanh::lean_unbox(v_snd_3359_) as u8);
                                crate::leanh::lean_dec(v_snd_3359_);
                                v___y_3290_ = v___x_3379_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        9 => {
                            v_fst_3380_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3380_);
                            v_snd_3381_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3381_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_fvarId_3382_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_i_3383_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v_offset_3384_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                            v_y_3385_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                            v_ty_3386_ = crate::leanh::lean_ctor_get(v_c_3282_, 4);
                            v_k_3387_ = crate::leanh::lean_ctor_get(v_c_3282_, 5);
                            v___x_3388_ = lean_ptr_addr(v_k_3387_);
                            v___x_3389_ = lean_ptr_addr(v_fst_3380_);
                            v___x_3390_ = lean_usize_dec_eq(v___x_3388_, v___x_3389_);
                            if v___x_3390_ == 0 {
                                crate::leanh::lean_inc_ref(v_ty_3386_);
                                crate::leanh::lean_inc(v_y_3385_);
                                crate::leanh::lean_inc(v_offset_3384_);
                                crate::leanh::lean_inc(v_i_3383_);
                                crate::leanh::lean_inc(v_fvarId_3382_);
                                v_isSharedCheck_3398_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3398_ == 0 {
                                    v_unused_3399_ = crate::leanh::lean_ctor_get(v_c_3282_, 5);
                                    crate::leanh::lean_dec(v_unused_3399_);
                                    v_unused_3400_ = crate::leanh::lean_ctor_get(v_c_3282_, 4);
                                    crate::leanh::lean_dec(v_unused_3400_);
                                    v_unused_3401_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                                    crate::leanh::lean_dec(v_unused_3401_);
                                    v_unused_3402_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                                    crate::leanh::lean_dec(v_unused_3402_);
                                    v_unused_3403_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3403_);
                                    v_unused_3404_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3404_);
                                    v___x_3392_ = v_c_3282_;
                                    v_isShared_3393_ = v_isSharedCheck_3398_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3392_ = crate::leanh::lean_box(0);
                                    v_isShared_3393_ = v_isSharedCheck_3398_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3380_);
                                v___x_3405_ = (crate::leanh::lean_unbox(v_snd_3381_) as u8);
                                crate::leanh::lean_dec(v_snd_3381_);
                                v___y_3290_ = v___x_3405_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        8 => {
                            v_fst_3406_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3406_);
                            v_snd_3407_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3407_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_fvarId_3408_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_i_3409_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v_y_3410_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                            v_k_3411_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                            v___x_3412_ = lean_ptr_addr(v_k_3411_);
                            v___x_3413_ = lean_ptr_addr(v_fst_3406_);
                            v___x_3414_ = lean_usize_dec_eq(v___x_3412_, v___x_3413_);
                            if v___x_3414_ == 0 {
                                crate::leanh::lean_inc(v_y_3410_);
                                crate::leanh::lean_inc(v_i_3409_);
                                crate::leanh::lean_inc(v_fvarId_3408_);
                                v_isSharedCheck_3422_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3422_ == 0 {
                                    v_unused_3423_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                                    crate::leanh::lean_dec(v_unused_3423_);
                                    v_unused_3424_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                                    crate::leanh::lean_dec(v_unused_3424_);
                                    v_unused_3425_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3425_);
                                    v_unused_3426_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3426_);
                                    v___x_3416_ = v_c_3282_;
                                    v_isShared_3417_ = v_isSharedCheck_3422_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3416_ = crate::leanh::lean_box(0);
                                    v_isShared_3417_ = v_isSharedCheck_3422_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3406_);
                                v___x_3427_ = (crate::leanh::lean_unbox(v_snd_3407_) as u8);
                                crate::leanh::lean_dec(v_snd_3407_);
                                v___y_3290_ = v___x_3427_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        10 => {
                            v_fst_3428_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3428_);
                            v_snd_3429_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3429_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_fvarId_3430_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_cidx_3431_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v_k_3432_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                            v___x_3433_ = lean_ptr_addr(v_k_3432_);
                            v___x_3434_ = lean_ptr_addr(v_fst_3428_);
                            v___x_3435_ = lean_usize_dec_eq(v___x_3433_, v___x_3434_);
                            if v___x_3435_ == 0 {
                                crate::leanh::lean_inc(v_cidx_3431_);
                                crate::leanh::lean_inc(v_fvarId_3430_);
                                v_isSharedCheck_3443_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3443_ == 0 {
                                    v_unused_3444_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                                    crate::leanh::lean_dec(v_unused_3444_);
                                    v_unused_3445_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3445_);
                                    v_unused_3446_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3446_);
                                    v___x_3437_ = v_c_3282_;
                                    v_isShared_3438_ = v_isSharedCheck_3443_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3437_ = crate::leanh::lean_box(0);
                                    v_isShared_3438_ = v_isSharedCheck_3443_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3428_);
                                v___x_3447_ = (crate::leanh::lean_unbox(v_snd_3429_) as u8);
                                crate::leanh::lean_dec(v_snd_3429_);
                                v___y_3290_ = v___x_3447_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        11 => {
                            v_fst_3448_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3448_);
                            v_snd_3449_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3449_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_fvarId_3450_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_n_3451_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v_check_3452_ = crate::leanh::lean_ctor_get_uint8(
                                v_c_3282_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            );
                            v_persistent_3453_ = crate::leanh::lean_ctor_get_uint8(
                                v_c_3282_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1)
                                    as u32,
                            );
                            v_k_3454_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                            v___x_3455_ = lean_ptr_addr(v_k_3454_);
                            v___x_3456_ = lean_ptr_addr(v_fst_3448_);
                            v___x_3457_ = lean_usize_dec_eq(v___x_3455_, v___x_3456_);
                            if v___x_3457_ == 0 {
                                crate::leanh::lean_inc(v_n_3451_);
                                crate::leanh::lean_inc(v_fvarId_3450_);
                                v_isSharedCheck_3465_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3465_ == 0 {
                                    v_unused_3466_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                                    crate::leanh::lean_dec(v_unused_3466_);
                                    v_unused_3467_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3467_);
                                    v_unused_3468_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3468_);
                                    v___x_3459_ = v_c_3282_;
                                    v_isShared_3460_ = v_isSharedCheck_3465_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3459_ = crate::leanh::lean_box(0);
                                    v_isShared_3460_ = v_isSharedCheck_3465_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3448_);
                                v___x_3469_ = (crate::leanh::lean_unbox(v_snd_3449_) as u8);
                                crate::leanh::lean_dec(v_snd_3449_);
                                v___y_3290_ = v___x_3469_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        12 => {
                            v_fst_3470_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3470_);
                            v_snd_3471_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3471_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_fvarId_3472_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_n_3473_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v_check_3474_ = crate::leanh::lean_ctor_get_uint8(
                                v_c_3282_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            v_persistent_3475_ = crate::leanh::lean_ctor_get_uint8(
                                v_c_3282_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1)
                                    as u32,
                            );
                            v_objs_x3f_3476_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                            v_k_3477_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                            v___x_3478_ = lean_ptr_addr(v_k_3477_);
                            v___x_3479_ = lean_ptr_addr(v_fst_3470_);
                            v___x_3480_ = lean_usize_dec_eq(v___x_3478_, v___x_3479_);
                            if v___x_3480_ == 0 {
                                crate::leanh::lean_inc(v_objs_x3f_3476_);
                                crate::leanh::lean_inc(v_n_3473_);
                                crate::leanh::lean_inc(v_fvarId_3472_);
                                v_isSharedCheck_3488_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3488_ == 0 {
                                    v_unused_3489_ = crate::leanh::lean_ctor_get(v_c_3282_, 3);
                                    crate::leanh::lean_dec(v_unused_3489_);
                                    v_unused_3490_ = crate::leanh::lean_ctor_get(v_c_3282_, 2);
                                    crate::leanh::lean_dec(v_unused_3490_);
                                    v_unused_3491_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3491_);
                                    v_unused_3492_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3492_);
                                    v___x_3482_ = v_c_3282_;
                                    v_isShared_3483_ = v_isSharedCheck_3488_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3482_ = crate::leanh::lean_box(0);
                                    v_isShared_3483_ = v_isSharedCheck_3488_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3470_);
                                v___x_3493_ = (crate::leanh::lean_unbox(v_snd_3471_) as u8);
                                crate::leanh::lean_dec(v_snd_3471_);
                                v___y_3290_ = v___x_3493_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        13 => {
                            v_fst_3494_ = crate::leanh::lean_ctor_get(v_a_3303_, 0);
                            crate::leanh::lean_inc(v_fst_3494_);
                            v_snd_3495_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3495_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v_fvarId_3496_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            v_k_3497_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            v___x_3498_ = lean_ptr_addr(v_k_3497_);
                            v___x_3499_ = lean_ptr_addr(v_fst_3494_);
                            v___x_3500_ = lean_usize_dec_eq(v___x_3498_, v___x_3499_);
                            if v___x_3500_ == 0 {
                                crate::leanh::lean_inc(v_fvarId_3496_);
                                v_isSharedCheck_3508_ =
                                    (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                                if v_isSharedCheck_3508_ == 0 {
                                    v_unused_3509_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                                    crate::leanh::lean_dec(v_unused_3509_);
                                    v_unused_3510_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                                    crate::leanh::lean_dec(v_unused_3510_);
                                    v___x_3502_ = v_c_3282_;
                                    v_isShared_3503_ = v_isSharedCheck_3508_;
                                    state = 21;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_c_3282_);
                                    v___x_3502_ = crate::leanh::lean_box(0);
                                    v_isShared_3503_ = v_isSharedCheck_3508_;
                                    state = 21;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3494_);
                                v___x_3511_ = (crate::leanh::lean_unbox(v_snd_3495_) as u8);
                                crate::leanh::lean_dec(v_snd_3495_);
                                v___y_3290_ = v___x_3511_;
                                v___y_3291_ = v_c_3282_;
                                state = 1;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_c_3282_);
                            v_snd_3512_ = crate::leanh::lean_ctor_get(v_a_3303_, 1);
                            crate::leanh::lean_inc(v_snd_3512_);
                            crate::leanh::lean_dec(v_a_3303_);
                            v___x_3513_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3);
                            v___x_3514_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(v___x_3513_);
                            v___x_3515_ = (crate::leanh::lean_unbox(v_snd_3512_) as u8);
                            crate::leanh::lean_dec(v_snd_3512_);
                            v___y_3290_ = v___x_3515_;
                            v___y_3291_ = v___x_3514_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_c_3282_);
                    return v___x_3302_;
                }
            }
            3 => {
                if v_isShared_3313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3312_, 1, v_fst_3304_);
                    v___x_3315_ = v___x_3312_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3317_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_decl_3306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_fst_3304_);
                    v___x_3315_ = v_reuseFailAlloc_3317_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3316_ = (crate::leanh::lean_unbox(v_snd_3305_) as u8);
                crate::leanh::lean_dec(v_snd_3305_);
                v___y_3290_ = v___x_3316_;
                v___y_3291_ = v___x_3315_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_3331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3330_, 1, v_fst_3322_);
                    v___x_3333_ = v___x_3330_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3335_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_decl_3324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_fst_3322_);
                    v___x_3333_ = v_reuseFailAlloc_3335_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3334_ = (crate::leanh::lean_unbox(v_snd_3323_) as u8);
                crate::leanh::lean_dec(v_snd_3323_);
                v___y_3290_ = v___x_3334_;
                v___y_3291_ = v___x_3333_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_3349_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3348_, 1, v_fst_3340_);
                    v___x_3351_ = v___x_3348_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_decl_3342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_fst_3340_);
                    v___x_3351_ = v_reuseFailAlloc_3353_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3352_ = (crate::leanh::lean_unbox(v_snd_3341_) as u8);
                crate::leanh::lean_dec(v_snd_3341_);
                v___y_3290_ = v___x_3352_;
                v___y_3291_ = v___x_3351_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_3369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3368_, 3, v_fst_3358_);
                    v___x_3371_ = v___x_3368_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_fvarId_3360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_i_3361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 2, v_y_3362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 3, v_fst_3358_);
                    v___x_3371_ = v_reuseFailAlloc_3373_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3372_ = (crate::leanh::lean_unbox(v_snd_3359_) as u8);
                crate::leanh::lean_dec(v_snd_3359_);
                v___y_3290_ = v___x_3372_;
                v___y_3291_ = v___x_3371_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_3393_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3392_, 5, v_fst_3380_);
                    v___x_3395_ = v___x_3392_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3397_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_fvarId_3382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_i_3383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 2, v_offset_3384_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 3, v_y_3385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 4, v_ty_3386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 5, v_fst_3380_);
                    v___x_3395_ = v_reuseFailAlloc_3397_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3396_ = (crate::leanh::lean_unbox(v_snd_3381_) as u8);
                crate::leanh::lean_dec(v_snd_3381_);
                v___y_3290_ = v___x_3396_;
                v___y_3291_ = v___x_3395_;
                state = 1;
                continue;
            }
            13 => {
                if v_isShared_3417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3416_, 3, v_fst_3406_);
                    v___x_3419_ = v___x_3416_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_fvarId_3408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_i_3409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 2, v_y_3410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 3, v_fst_3406_);
                    v___x_3419_ = v_reuseFailAlloc_3421_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3420_ = (crate::leanh::lean_unbox(v_snd_3407_) as u8);
                crate::leanh::lean_dec(v_snd_3407_);
                v___y_3290_ = v___x_3420_;
                v___y_3291_ = v___x_3419_;
                state = 1;
                continue;
            }
            15 => {
                if v_isShared_3438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3437_, 2, v_fst_3428_);
                    v___x_3440_ = v___x_3437_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3442_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_fvarId_3430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_cidx_3431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3442_, 2, v_fst_3428_);
                    v___x_3440_ = v_reuseFailAlloc_3442_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_3441_ = (crate::leanh::lean_unbox(v_snd_3429_) as u8);
                crate::leanh::lean_dec(v_snd_3429_);
                v___y_3290_ = v___x_3441_;
                v___y_3291_ = v___x_3440_;
                state = 1;
                continue;
            }
            17 => {
                if v_isShared_3460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3459_, 2, v_fst_3448_);
                    v___x_3462_ = v___x_3459_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fvarId_3450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_n_3451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_fst_3448_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_check_3452_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_3453_,
                    );
                    v___x_3462_ = v_reuseFailAlloc_3464_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3463_ = (crate::leanh::lean_unbox(v_snd_3449_) as u8);
                crate::leanh::lean_dec(v_snd_3449_);
                v___y_3290_ = v___x_3463_;
                v___y_3291_ = v___x_3462_;
                state = 1;
                continue;
            }
            19 => {
                if v_isShared_3483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3482_, 3, v_fst_3470_);
                    v___x_3485_ = v___x_3482_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_fvarId_3472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_n_3473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_objs_x3f_3476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_fst_3470_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3487_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_3474_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3487_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_3475_,
                    );
                    v___x_3485_ = v_reuseFailAlloc_3487_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3486_ = (crate::leanh::lean_unbox(v_snd_3471_) as u8);
                crate::leanh::lean_dec(v_snd_3471_);
                v___y_3290_ = v___x_3486_;
                v___y_3291_ = v___x_3485_;
                state = 1;
                continue;
            }
            21 => {
                if v_isShared_3503_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3502_, 1, v_fst_3494_);
                    v___x_3505_ = v___x_3502_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3507_ = crate::leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_fvarId_3496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_fst_3494_);
                    v___x_3505_ = v_reuseFailAlloc_3507_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_3506_ = (crate::leanh::lean_unbox(v_snd_3495_) as u8);
                crate::leanh::lean_dec(v_snd_3495_);
                v___y_3290_ = v___x_3506_;
                v___y_3291_ = v___x_3505_;
                state = 1;
                continue;
            }
            23 => {
                v_i_3525_ = crate::leanh::lean_ctor_get(v_value_3517_, 0);
                v_args_3526_ = crate::leanh::lean_ctor_get(v_value_3517_, 1);
                v_isSharedCheck_3583_ = (!crate::leanh::lean_is_exclusive(v_value_3517_)) as u8;
                if v_isSharedCheck_3583_ == 0 {
                    v___x_3528_ = v_value_3517_;
                    v_isShared_3529_ = v_isSharedCheck_3583_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_args_3526_);
                    crate::leanh::lean_inc(v_i_3525_);
                    crate::leanh::lean_dec(v_value_3517_);
                    v___x_3528_ = crate::leanh::lean_box(0);
                    v_isShared_3529_ = v_isSharedCheck_3583_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_3530_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_info_3280_, v_i_3525_, v_a_3283_);
                if crate::leanh::lean_obj_tag(v___x_3530_) == 0 {
                    v_a_3531_ = crate::leanh::lean_ctor_get(v___x_3530_, 0);
                    crate::leanh::lean_inc(v_a_3531_);
                    crate::leanh::lean_dec_ref_known(v___x_3530_, 1);
                    v___x_3532_ = (crate::leanh::lean_unbox(v_a_3531_) as u8);
                    if v___x_3532_ == 0 {
                        crate::leanh::lean_dec(v_a_3531_);
                        crate::leanh::lean_del_object(v___x_3528_);
                        crate::leanh::lean_dec_ref(v_args_3526_);
                        crate::leanh::lean_dec_ref(v_i_3525_);
                        crate::leanh::lean_del_object(v___x_3523_);
                        crate::leanh::lean_dec_ref(v_type_3521_);
                        crate::leanh::lean_dec(v_binderName_3520_);
                        crate::leanh::lean_dec(v_fvarId_3519_);
                        crate::leanh::lean_inc_ref(v_k_3518_);
                        v_k_3296_ = v_k_3518_;
                        v___y_3297_ = v_a_3283_;
                        v___y_3298_ = v_a_3284_;
                        v___y_3299_ = v_a_3285_;
                        v___y_3300_ = v_a_3286_;
                        v___y_3301_ = v_a_3287_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_k_3518_);
                        v_isSharedCheck_3572_ = (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                        if v_isSharedCheck_3572_ == 0 {
                            v_unused_3573_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                            crate::leanh::lean_dec(v_unused_3573_);
                            v_unused_3574_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                            crate::leanh::lean_dec(v_unused_3574_);
                            v___x_3534_ = v_c_3282_;
                            v_isShared_3535_ = v_isSharedCheck_3572_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_c_3282_);
                            v___x_3534_ = crate::leanh::lean_box(0);
                            v_isShared_3535_ = v_isSharedCheck_3572_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3528_);
                    crate::leanh::lean_dec_ref(v_args_3526_);
                    crate::leanh::lean_dec_ref(v_i_3525_);
                    crate::leanh::lean_del_object(v___x_3523_);
                    crate::leanh::lean_dec_ref(v_type_3521_);
                    crate::leanh::lean_dec(v_binderName_3520_);
                    crate::leanh::lean_dec(v_fvarId_3519_);
                    crate::leanh::lean_dec_ref_known(v_c_3282_, 2);
                    crate::leanh::lean_dec(v_w_3281_);
                    v_a_3575_ = crate::leanh::lean_ctor_get(v___x_3530_, 0);
                    v_isSharedCheck_3582_ = (!crate::leanh::lean_is_exclusive(v___x_3530_)) as u8;
                    if v_isSharedCheck_3582_ == 0 {
                        v___x_3577_ = v___x_3530_;
                        v_isShared_3578_ = v_isSharedCheck_3582_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3575_);
                        crate::leanh::lean_dec(v___x_3530_);
                        v___x_3577_ = crate::leanh::lean_box(0);
                        v_isShared_3578_ = v_isSharedCheck_3582_;
                        state = 34;
                        continue;
                    }
                }
            }
            25 => {
                v_cidx_3536_ = crate::leanh::lean_ctor_get(v_info_3280_, 1);
                v_cidx_3537_ = crate::leanh::lean_ctor_get(v_i_3525_, 1);
                v___x_3538_ = 1;
                crate::leanh::lean_inc_ref(v_args_3526_);
                crate::leanh::lean_inc_ref(v_i_3525_);
                if v_isShared_3529_ == 0 {
                    v___x_3540_ = v___x_3528_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3571_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_i_3525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_args_3526_);
                    v___x_3540_ = v_reuseFailAlloc_3571_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                crate::leanh::lean_inc_ref(v_type_3521_);
                if v_isShared_3524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3523_, 3, v___x_3540_);
                    v___x_3542_ = v___x_3523_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3570_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_fvarId_3519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_binderName_3520_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_type_3521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 3, v___x_3540_);
                    v___x_3542_ = v_reuseFailAlloc_3570_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_3567_ = lean_nat_dec_eq(v_cidx_3536_, v_cidx_3537_);
                if v___x_3567_ == 0 {
                    v___x_3568_ = (crate::leanh::lean_unbox(v_a_3531_) as u8);
                    v___y_3544_ = v___x_3568_;
                    state = 28;
                    continue;
                } else {
                    v___x_3569_ = 0;
                    v___y_3544_ = v___x_3569_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_3545_ = crate::leanh::lean_alloc_ctor(12, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3545_, 0, v_w_3281_);
                crate::leanh::lean_ctor_set(v___x_3545_, 1, v_i_3525_);
                crate::leanh::lean_ctor_set(v___x_3545_, 2, v_args_3526_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3545_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___y_3544_,
                );
                v___x_3546_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3538_, v___x_3542_, v_type_3521_, v___x_3545_, v_a_3285_);
                if crate::leanh::lean_obj_tag(v___x_3546_) == 0 {
                    v_a_3547_ = crate::leanh::lean_ctor_get(v___x_3546_, 0);
                    v_isSharedCheck_3558_ = (!crate::leanh::lean_is_exclusive(v___x_3546_)) as u8;
                    if v_isSharedCheck_3558_ == 0 {
                        v___x_3549_ = v___x_3546_;
                        v_isShared_3550_ = v_isSharedCheck_3558_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3547_);
                        crate::leanh::lean_dec(v___x_3546_);
                        v___x_3549_ = crate::leanh::lean_box(0);
                        v_isShared_3550_ = v_isSharedCheck_3558_;
                        state = 29;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3534_);
                    crate::leanh::lean_dec(v_a_3531_);
                    crate::leanh::lean_dec_ref(v_k_3518_);
                    v_a_3559_ = crate::leanh::lean_ctor_get(v___x_3546_, 0);
                    v_isSharedCheck_3566_ = (!crate::leanh::lean_is_exclusive(v___x_3546_)) as u8;
                    if v_isSharedCheck_3566_ == 0 {
                        v___x_3561_ = v___x_3546_;
                        v_isShared_3562_ = v_isSharedCheck_3566_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3559_);
                        crate::leanh::lean_dec(v___x_3546_);
                        v___x_3561_ = crate::leanh::lean_box(0);
                        v_isShared_3562_ = v_isSharedCheck_3566_;
                        state = 32;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_3535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3534_, 0, v_a_3547_);
                    v___x_3552_ = v___x_3534_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_k_3518_);
                    v___x_3552_ = v_reuseFailAlloc_3557_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3553_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3553_, 0, v___x_3552_);
                crate::leanh::lean_ctor_set(v___x_3553_, 1, v_a_3531_);
                if v_isShared_3550_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3549_, 0, v___x_3553_);
                    v___x_3555_ = v___x_3549_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
                    v___x_3555_ = v_reuseFailAlloc_3556_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3555_;
            }
            32 => {
                if v_isShared_3562_ == 0 {
                    v___x_3564_ = v___x_3561_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
                    v___x_3564_ = v_reuseFailAlloc_3565_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3564_;
            }
            34 => {
                if v_isShared_3578_ == 0 {
                    v___x_3580_ = v___x_3577_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
                    v___x_3580_ = v_reuseFailAlloc_3581_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3580_;
            }
            36 => {
                v___x_3600_ = 1;
                crate::leanh::lean_inc_ref(v_params_3589_);
                crate::leanh::lean_inc_ref(v_type_3590_);
                crate::leanh::lean_inc_ref(v_decl_3587_);
                v___x_3601_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3600_, v_decl_3587_, v_type_3590_, v_params_3589_, v_fst_3596_, v_a_3285_);
                if crate::leanh::lean_obj_tag(v___x_3601_) == 0 {
                    v_a_3602_ = crate::leanh::lean_ctor_get(v___x_3601_, 0);
                    v_isSharedCheck_3630_ = (!crate::leanh::lean_is_exclusive(v___x_3601_)) as u8;
                    if v_isSharedCheck_3630_ == 0 {
                        v___x_3604_ = v___x_3601_;
                        v_isShared_3605_ = v_isSharedCheck_3630_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3602_);
                        crate::leanh::lean_dec(v___x_3601_);
                        v___x_3604_ = crate::leanh::lean_box(0);
                        v_isShared_3605_ = v_isSharedCheck_3630_;
                        state = 37;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3598_);
                    crate::leanh::lean_dec(v_snd_3594_);
                    crate::leanh::lean_dec_ref_known(v_c_3282_, 2);
                    v_a_3631_ = crate::leanh::lean_ctor_get(v___x_3601_, 0);
                    v_isSharedCheck_3638_ = (!crate::leanh::lean_is_exclusive(v___x_3601_)) as u8;
                    if v_isSharedCheck_3638_ == 0 {
                        v___x_3633_ = v___x_3601_;
                        v_isShared_3634_ = v_isSharedCheck_3638_;
                        state = 44;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3631_);
                        crate::leanh::lean_dec(v___x_3601_);
                        v___x_3633_ = crate::leanh::lean_box(0);
                        v_isShared_3634_ = v_isSharedCheck_3638_;
                        state = 44;
                        continue;
                    }
                }
            }
            37 => {
                v___x_3625_ = lean_ptr_addr(v_k_3588_);
                v___x_3626_ = lean_usize_dec_eq(v___x_3625_, v___x_3625_);
                if v___x_3626_ == 0 {
                    v___y_3615_ = v___x_3626_;
                    state = 41;
                    continue;
                } else {
                    v___x_3627_ = lean_ptr_addr(v_decl_3587_);
                    v___x_3628_ = lean_ptr_addr(v_a_3602_);
                    v___x_3629_ = lean_usize_dec_eq(v___x_3627_, v___x_3628_);
                    v___y_3615_ = v___x_3629_;
                    state = 41;
                    continue;
                }
            }
            38 => {
                if v_isShared_3599_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3598_, 0, v___y_3607_);
                    v___x_3609_ = v___x_3598_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___y_3607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_snd_3594_);
                    v___x_3609_ = v_reuseFailAlloc_3613_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_3605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3604_, 0, v___x_3609_);
                    v___x_3611_ = v___x_3604_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3612_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
                    v___x_3611_ = v_reuseFailAlloc_3612_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3611_;
            }
            41 => {
                if v___y_3615_ == 0 {
                    crate::leanh::lean_inc_ref(v_k_3588_);
                    v_isSharedCheck_3622_ = (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                    if v_isSharedCheck_3622_ == 0 {
                        v_unused_3623_ = crate::leanh::lean_ctor_get(v_c_3282_, 1);
                        crate::leanh::lean_dec(v_unused_3623_);
                        v_unused_3624_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                        crate::leanh::lean_dec(v_unused_3624_);
                        v___x_3617_ = v_c_3282_;
                        v_isShared_3618_ = v_isSharedCheck_3622_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_3282_);
                        v___x_3617_ = crate::leanh::lean_box(0);
                        v_isShared_3618_ = v_isSharedCheck_3622_;
                        state = 42;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3602_);
                    v___y_3607_ = v_c_3282_;
                    state = 38;
                    continue;
                }
            }
            42 => {
                if v_isShared_3618_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3617_, 0, v_a_3602_);
                    v___x_3620_ = v___x_3617_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3621_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_k_3588_);
                    v___x_3620_ = v_reuseFailAlloc_3621_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___y_3607_ = v___x_3620_;
                state = 38;
                continue;
            }
            44 => {
                if v_isShared_3634_ == 0 {
                    v___x_3636_ = v___x_3633_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
                    v___x_3636_ = v_reuseFailAlloc_3637_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_3636_;
            }
            46 => {
                v_sz_3653_ = lean_array_size(v_alts_3649_);
                v___x_3654_ = 0usize;
                crate::leanh::lean_inc_ref(v_alts_3649_);
                v___x_3655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_3280_, v_w_3281_, v_sz_3653_, v___x_3654_, v_alts_3649_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
                if crate::leanh::lean_obj_tag(v___x_3655_) == 0 {
                    v_a_3656_ = crate::leanh::lean_ctor_get(v___x_3655_, 0);
                    v_isSharedCheck_3692_ = (!crate::leanh::lean_is_exclusive(v___x_3655_)) as u8;
                    if v_isSharedCheck_3692_ == 0 {
                        v___x_3658_ = v___x_3655_;
                        v_isShared_3659_ = v_isSharedCheck_3692_;
                        state = 47;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3656_);
                        crate::leanh::lean_dec(v___x_3655_);
                        v___x_3658_ = crate::leanh::lean_box(0);
                        v_isShared_3659_ = v_isSharedCheck_3692_;
                        state = 47;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3651_);
                    crate::leanh::lean_dec_ref(v_alts_3649_);
                    crate::leanh::lean_dec(v_discr_3648_);
                    crate::leanh::lean_dec_ref(v_resultType_3647_);
                    crate::leanh::lean_dec(v_typeName_3646_);
                    crate::leanh::lean_dec_ref_known(v_c_3282_, 1);
                    v_a_3693_ = crate::leanh::lean_ctor_get(v___x_3655_, 0);
                    v_isSharedCheck_3700_ = (!crate::leanh::lean_is_exclusive(v___x_3655_)) as u8;
                    if v_isSharedCheck_3700_ == 0 {
                        v___x_3695_ = v___x_3655_;
                        v_isShared_3696_ = v_isSharedCheck_3700_;
                        state = 54;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3693_);
                        crate::leanh::lean_dec(v___x_3655_);
                        v___x_3695_ = crate::leanh::lean_box(0);
                        v_isShared_3696_ = v_isSharedCheck_3700_;
                        state = 54;
                        continue;
                    }
                }
            }
            47 => {
                v___x_3668_ = l_Array_unzip___redArg(v_a_3656_);
                crate::leanh::lean_dec(v_a_3656_);
                v_fst_3669_ = crate::leanh::lean_ctor_get(v___x_3668_, 0);
                crate::leanh::lean_inc(v_fst_3669_);
                v_snd_3670_ = crate::leanh::lean_ctor_get(v___x_3668_, 1);
                crate::leanh::lean_inc(v_snd_3670_);
                crate::leanh::lean_dec_ref(v___x_3668_);
                v___x_3678_ = lean_ptr_addr(v_alts_3649_);
                crate::leanh::lean_dec_ref(v_alts_3649_);
                v___x_3679_ = lean_ptr_addr(v_fst_3669_);
                v___x_3680_ = lean_usize_dec_eq(v___x_3678_, v___x_3679_);
                if v___x_3680_ == 0 {
                    v_isSharedCheck_3690_ = (!crate::leanh::lean_is_exclusive(v_c_3282_)) as u8;
                    if v_isSharedCheck_3690_ == 0 {
                        v_unused_3691_ = crate::leanh::lean_ctor_get(v_c_3282_, 0);
                        crate::leanh::lean_dec(v_unused_3691_);
                        v___x_3682_ = v_c_3282_;
                        v_isShared_3683_ = v_isSharedCheck_3690_;
                        state = 51;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_3282_);
                        v___x_3682_ = crate::leanh::lean_box(0);
                        v_isShared_3683_ = v_isSharedCheck_3690_;
                        state = 51;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_3669_);
                    crate::leanh::lean_del_object(v___x_3651_);
                    crate::leanh::lean_dec(v_discr_3648_);
                    crate::leanh::lean_dec_ref(v_resultType_3647_);
                    crate::leanh::lean_dec(v_typeName_3646_);
                    v___y_3672_ = v_c_3282_;
                    state = 50;
                    continue;
                }
            }
            48 => {
                v___x_3663_ = crate::leanh::lean_box((v___y_3662_) as usize);
                v___x_3664_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3664_, 0, v___y_3661_);
                crate::leanh::lean_ctor_set(v___x_3664_, 1, v___x_3663_);
                if v_isShared_3659_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3658_, 0, v___x_3664_);
                    v___x_3666_ = v___x_3658_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
                    v___x_3666_ = v_reuseFailAlloc_3667_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_3666_;
            }
            50 => {
                v___x_3673_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3674_ = lean_array_get_size(v_snd_3670_);
                v___x_3675_ = lean_nat_dec_lt(v___x_3673_, v___x_3674_);
                if v___x_3675_ == 0 {
                    crate::leanh::lean_dec(v_snd_3670_);
                    v___y_3661_ = v___y_3672_;
                    v___y_3662_ = v___x_3675_;
                    state = 48;
                    continue;
                } else {
                    if v___x_3675_ == 0 {
                        crate::leanh::lean_dec(v_snd_3670_);
                        v___y_3661_ = v___y_3672_;
                        v___y_3662_ = v___x_3675_;
                        state = 48;
                        continue;
                    } else {
                        v___x_3676_ = lean_usize_of_nat(v___x_3674_);
                        v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_snd_3670_, v___x_3654_, v___x_3676_);
                        crate::leanh::lean_dec(v_snd_3670_);
                        v___y_3661_ = v___y_3672_;
                        v___y_3662_ = v___x_3677_;
                        state = 48;
                        continue;
                    }
                }
            }
            51 => {
                if v_isShared_3652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3651_, 3, v_fst_3669_);
                    v___x_3685_ = v___x_3651_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_3689_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_typeName_3646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_resultType_3647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_discr_3648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_fst_3669_);
                    v___x_3685_ = v_reuseFailAlloc_3689_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                if v_isShared_3683_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3682_, 0, v___x_3685_);
                    v___x_3687_ = v___x_3682_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_3688_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
                    v___x_3687_ = v_reuseFailAlloc_3688_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                v___y_3672_ = v___x_3687_;
                state = 50;
                continue;
            }
            54 => {
                if v_isShared_3696_ == 0 {
                    v___x_3698_ = v___x_3695_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_3699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
                    v___x_3698_ = v_reuseFailAlloc_3699_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_3698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(
    mut v_info_3714_: *mut crate::leanh::LeanObject,
    mut v_w_3715_: *mut crate::leanh::LeanObject,
    mut v_sz_3716_: usize,
    mut v_i_3717_: usize,
    mut v_bs_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3725_: u8 = 0;
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: usize = 0;
    let mut v___x_3743_: usize = 0;
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut v_a_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3751_: u8 = 0;
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3755_: u8 = 0;
    let mut v_code_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3725_ = lean_usize_dec_lt(v_i_3717_, v_sz_3716_);
                if v___x_3725_ == 0 {
                    crate::leanh::lean_dec(v_w_3715_);
                    v___x_3726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3726_, 0, v_bs_3718_);
                    return v___x_3726_;
                } else {
                    v_v_3727_ = lean_array_uget(v_bs_3718_, v_i_3717_);
                    v___x_3728_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3729_ = lean_array_uset(v_bs_3718_, v_i_3717_, v___x_3728_);
                    match crate::leanh::lean_obj_tag(v_v_3727_) {
                        0 => {
                            v_code_3756_ = crate::leanh::lean_ctor_get(v_v_3727_, 2);
                            crate::leanh::lean_inc_ref(v_code_3756_);
                            v___y_3731_ = v_code_3756_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_3757_ = crate::leanh::lean_ctor_get(v_v_3727_, 1);
                            crate::leanh::lean_inc_ref(v_code_3757_);
                            v___y_3731_ = v_code_3757_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_3758_ = crate::leanh::lean_ctor_get(v_v_3727_, 0);
                            crate::leanh::lean_inc_ref(v_code_3758_);
                            v___y_3731_ = v_code_3758_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_w_3715_);
                v___x_3732_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(
                    v_info_3714_,
                    v_w_3715_,
                    v___y_3731_,
                    v___y_3719_,
                    v___y_3720_,
                    v___y_3721_,
                    v___y_3722_,
                    v___y_3723_,
                );
                if crate::leanh::lean_obj_tag(v___x_3732_) == 0 {
                    v_a_3733_ = crate::leanh::lean_ctor_get(v___x_3732_, 0);
                    crate::leanh::lean_inc(v_a_3733_);
                    crate::leanh::lean_dec_ref_known(v___x_3732_, 1);
                    v_fst_3734_ = crate::leanh::lean_ctor_get(v_a_3733_, 0);
                    v_snd_3735_ = crate::leanh::lean_ctor_get(v_a_3733_, 1);
                    v_isSharedCheck_3747_ = (!crate::leanh::lean_is_exclusive(v_a_3733_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3737_ = v_a_3733_;
                        v_isShared_3738_ = v_isSharedCheck_3747_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3735_);
                        crate::leanh::lean_inc(v_fst_3734_);
                        crate::leanh::lean_dec(v_a_3733_);
                        v___x_3737_ = crate::leanh::lean_box(0);
                        v_isShared_3738_ = v_isSharedCheck_3747_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_3729_);
                    crate::leanh::lean_dec(v_v_3727_);
                    crate::leanh::lean_dec(v_w_3715_);
                    v_a_3748_ = crate::leanh::lean_ctor_get(v___x_3732_, 0);
                    v_isSharedCheck_3755_ = (!crate::leanh::lean_is_exclusive(v___x_3732_)) as u8;
                    if v_isSharedCheck_3755_ == 0 {
                        v___x_3750_ = v___x_3732_;
                        v_isShared_3751_ = v_isSharedCheck_3755_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3748_);
                        crate::leanh::lean_dec(v___x_3732_);
                        v___x_3750_ = crate::leanh::lean_box(0);
                        v_isShared_3751_ = v_isSharedCheck_3755_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3739_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3727_, v_fst_3734_);
                if v_isShared_3738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3737_, 0, v___x_3739_);
                    v___x_3741_ = v___x_3737_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_snd_3735_);
                    v___x_3741_ = v_reuseFailAlloc_3746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3742_ = 1usize;
                v___x_3743_ = lean_usize_add(v_i_3717_, v___x_3742_);
                v___x_3744_ = lean_array_uset(v_bs_x27_3729_, v_i_3717_, v___x_3741_);
                v_i_3717_ = v___x_3743_;
                v_bs_3718_ = v___x_3744_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3751_ == 0 {
                    v___x_3753_ = v___x_3750_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
                    v___x_3753_ = v_reuseFailAlloc_3754_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(
    mut v_info_3759_: *mut crate::leanh::LeanObject,
    mut v_w_3760_: *mut crate::leanh::LeanObject,
    mut v_sz_3761_: *mut crate::leanh::LeanObject,
    mut v_i_3762_: *mut crate::leanh::LeanObject,
    mut v_bs_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
    mut v___y_3765_: *mut crate::leanh::LeanObject,
    mut v___y_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3770_: usize = 0;
    let mut v_i_boxed_3771_: usize = 0;
    let mut v_res_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3770_ = crate::leanh::lean_unbox_usize(v_sz_3761_);
    crate::leanh::lean_dec(v_sz_3761_);
    v_i_boxed_3771_ = crate::leanh::lean_unbox_usize(v_i_3762_);
    crate::leanh::lean_dec(v_i_3762_);
    v_res_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_3759_, v_w_3760_, v_sz_boxed_3770_, v_i_boxed_3771_, v_bs_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
    crate::leanh::lean_dec(v___y_3768_);
    crate::leanh::lean_dec_ref(v___y_3767_);
    crate::leanh::lean_dec(v___y_3766_);
    crate::leanh::lean_dec_ref(v___y_3765_);
    crate::leanh::lean_dec_ref(v___y_3764_);
    crate::leanh::lean_dec_ref(v_info_3759_);
    return v_res_3772_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(
    mut v_info_3773_: *mut crate::leanh::LeanObject,
    mut v_w_3774_: *mut crate::leanh::LeanObject,
    mut v_c_3775_: *mut crate::leanh::LeanObject,
    mut v_a_3776_: *mut crate::leanh::LeanObject,
    mut v_a_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v_a_3779_: *mut crate::leanh::LeanObject,
    mut v_a_3780_: *mut crate::leanh::LeanObject,
    mut v_a_3781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3782_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(
        v_info_3773_,
        v_w_3774_,
        v_c_3775_,
        v_a_3776_,
        v_a_3777_,
        v_a_3778_,
        v_a_3779_,
        v_a_3780_,
    );
    crate::leanh::lean_dec(v_a_3780_);
    crate::leanh::lean_dec_ref(v_a_3779_);
    crate::leanh::lean_dec(v_a_3778_);
    crate::leanh::lean_dec_ref(v_a_3777_);
    crate::leanh::lean_dec_ref(v_a_3776_);
    crate::leanh::lean_dec_ref(v_info_3773_);
    return v_res_3782_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(
    mut v___y_3783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3803_: u8 = 0;
    let mut v_r_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3815_: u8 = 0;
    let mut v_unused_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3785_ = lean_st_ref_get(v___y_3783_);
                v_ngen_3786_ = crate::leanh::lean_ctor_get(v___x_3785_, 2);
                crate::leanh::lean_inc_ref(v_ngen_3786_);
                crate::leanh::lean_dec(v___x_3785_);
                v_namePrefix_3787_ = crate::leanh::lean_ctor_get(v_ngen_3786_, 0);
                v_idx_3788_ = crate::leanh::lean_ctor_get(v_ngen_3786_, 1);
                v_isSharedCheck_3817_ = (!crate::leanh::lean_is_exclusive(v_ngen_3786_)) as u8;
                if v_isSharedCheck_3817_ == 0 {
                    v___x_3790_ = v_ngen_3786_;
                    v_isShared_3791_ = v_isSharedCheck_3817_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_3788_);
                    crate::leanh::lean_inc(v_namePrefix_3787_);
                    crate::leanh::lean_dec(v_ngen_3786_);
                    v___x_3790_ = crate::leanh::lean_box(0);
                    v_isShared_3791_ = v_isSharedCheck_3817_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3792_ = lean_st_ref_take(v___y_3783_);
                v_env_3793_ = crate::leanh::lean_ctor_get(v___x_3792_, 0);
                v_nextMacroScope_3794_ = crate::leanh::lean_ctor_get(v___x_3792_, 1);
                v_auxDeclNGen_3795_ = crate::leanh::lean_ctor_get(v___x_3792_, 3);
                v_traceState_3796_ = crate::leanh::lean_ctor_get(v___x_3792_, 4);
                v_cache_3797_ = crate::leanh::lean_ctor_get(v___x_3792_, 5);
                v_messages_3798_ = crate::leanh::lean_ctor_get(v___x_3792_, 6);
                v_infoState_3799_ = crate::leanh::lean_ctor_get(v___x_3792_, 7);
                v_snapshotTasks_3800_ = crate::leanh::lean_ctor_get(v___x_3792_, 8);
                v_isSharedCheck_3815_ = (!crate::leanh::lean_is_exclusive(v___x_3792_)) as u8;
                if v_isSharedCheck_3815_ == 0 {
                    v_unused_3816_ = crate::leanh::lean_ctor_get(v___x_3792_, 2);
                    crate::leanh::lean_dec(v_unused_3816_);
                    v___x_3802_ = v___x_3792_;
                    v_isShared_3803_ = v_isSharedCheck_3815_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3800_);
                    crate::leanh::lean_inc(v_infoState_3799_);
                    crate::leanh::lean_inc(v_messages_3798_);
                    crate::leanh::lean_inc(v_cache_3797_);
                    crate::leanh::lean_inc(v_traceState_3796_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3795_);
                    crate::leanh::lean_inc(v_nextMacroScope_3794_);
                    crate::leanh::lean_inc(v_env_3793_);
                    crate::leanh::lean_dec(v___x_3792_);
                    v___x_3802_ = crate::leanh::lean_box(0);
                    v_isShared_3803_ = v_isSharedCheck_3815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_3788_);
                crate::leanh::lean_inc(v_namePrefix_3787_);
                v_r_3804_ = l_Lean_Name_num___override(v_namePrefix_3787_, v_idx_3788_);
                v___x_3805_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3806_ = lean_nat_add(v_idx_3788_, v___x_3805_);
                crate::leanh::lean_dec(v_idx_3788_);
                if v_isShared_3791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3790_, 1, v___x_3806_);
                    v___x_3808_ = v___x_3790_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_namePrefix_3787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 1, v___x_3806_);
                    v___x_3808_ = v_reuseFailAlloc_3814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3803_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3802_, 2, v___x_3808_);
                    v___x_3810_ = v___x_3802_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_env_3793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_nextMacroScope_3794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 2, v___x_3808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_auxDeclNGen_3795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_traceState_3796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 5, v_cache_3797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 6, v_messages_3798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 7, v_infoState_3799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 8, v_snapshotTasks_3800_);
                    v___x_3810_ = v_reuseFailAlloc_3813_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3811_ = lean_st_ref_set(v___y_3783_, v___x_3810_);
                v___x_3812_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3812_, 0, v_r_3804_);
                return v___x_3812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3820_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_3818_);
    crate::leanh::lean_dec(v___y_3818_);
    return v_res_3820_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(
    mut v___y_3821_: *mut crate::leanh::LeanObject,
    mut v___y_3822_: *mut crate::leanh::LeanObject,
    mut v___y_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3827_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_3825_);
                v_a_3828_ = crate::leanh::lean_ctor_get(v___x_3827_, 0);
                v_isSharedCheck_3835_ = (!crate::leanh::lean_is_exclusive(v___x_3827_)) as u8;
                if v_isSharedCheck_3835_ == 0 {
                    v___x_3830_ = v___x_3827_;
                    v_isShared_3831_ = v_isSharedCheck_3835_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3828_);
                    crate::leanh::lean_dec(v___x_3827_);
                    v___x_3830_ = crate::leanh::lean_box(0);
                    v_isShared_3831_ = v_isSharedCheck_3835_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3831_ == 0 {
                    v___x_3833_ = v___x_3830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
                    v___x_3833_ = v_reuseFailAlloc_3834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(
    mut v___y_3836_: *mut crate::leanh::LeanObject,
    mut v___y_3837_: *mut crate::leanh::LeanObject,
    mut v___y_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3842_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
    crate::leanh::lean_dec(v___y_3840_);
    crate::leanh::lean_dec_ref(v___y_3839_);
    crate::leanh::lean_dec(v___y_3838_);
    crate::leanh::lean_dec_ref(v___y_3837_);
    crate::leanh::lean_dec_ref(v___y_3836_);
    return v_res_3842_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3849_ = crate::leanh::lean_box(0);
    v___x_3850_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3;
    v___x_3851_ = l_Lean_Expr_const___override(v___x_3850_, v___x_3849_);
    return v___x_3851_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(
    mut v_x_3852_: *mut crate::leanh::LeanObject,
    mut v_info_3853_: *mut crate::leanh::LeanObject,
    mut v_c_3854_: *mut crate::leanh::LeanObject,
    mut v_a_3855_: *mut crate::leanh::LeanObject,
    mut v_a_3856_: *mut crate::leanh::LeanObject,
    mut v_a_3857_: *mut crate::leanh::LeanObject,
    mut v_a_3858_: *mut crate::leanh::LeanObject,
    mut v_a_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v_snd_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v_fst_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3877_: u8 = 0;
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v_size_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3890_: u8 = 0;
    let mut v___x_3891_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v_isSharedCheck_3907_: u8 = 0;
    let mut v_a_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3911_: u8 = 0;
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut v_unused_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_a_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v_a_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3930_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3861_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
                if crate::leanh::lean_obj_tag(v___x_3861_) == 0 {
                    v_a_3862_ = crate::leanh::lean_ctor_get(v___x_3861_, 0);
                    crate::leanh::lean_inc_n(v_a_3862_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3861_, 1);
                    v___x_3863_ =
                        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(
                            v_info_3853_,
                            v_a_3862_,
                            v_c_3854_,
                            v_a_3855_,
                            v_a_3856_,
                            v_a_3857_,
                            v_a_3858_,
                            v_a_3859_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3863_) == 0 {
                        v_a_3864_ = crate::leanh::lean_ctor_get(v___x_3863_, 0);
                        v_isSharedCheck_3918_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3863_)) as u8;
                        if v_isSharedCheck_3918_ == 0 {
                            v___x_3866_ = v___x_3863_;
                            v_isShared_3867_ = v_isSharedCheck_3918_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3864_);
                            crate::leanh::lean_dec(v___x_3863_);
                            v___x_3866_ = crate::leanh::lean_box(0);
                            v_isShared_3867_ = v_isSharedCheck_3918_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3862_);
                        crate::leanh::lean_dec(v_x_3852_);
                        v_a_3919_ = crate::leanh::lean_ctor_get(v___x_3863_, 0);
                        v_isSharedCheck_3926_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3863_)) as u8;
                        if v_isSharedCheck_3926_ == 0 {
                            v___x_3921_ = v___x_3863_;
                            v_isShared_3922_ = v_isSharedCheck_3926_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3919_);
                            crate::leanh::lean_dec(v___x_3863_);
                            v___x_3921_ = crate::leanh::lean_box(0);
                            v_isShared_3922_ = v_isSharedCheck_3926_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_c_3854_);
                    crate::leanh::lean_dec(v_x_3852_);
                    v_a_3927_ = crate::leanh::lean_ctor_get(v___x_3861_, 0);
                    v_isSharedCheck_3934_ = (!crate::leanh::lean_is_exclusive(v___x_3861_)) as u8;
                    if v_isSharedCheck_3934_ == 0 {
                        v___x_3929_ = v___x_3861_;
                        v_isShared_3930_ = v_isSharedCheck_3934_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3927_);
                        crate::leanh::lean_dec(v___x_3861_);
                        v___x_3929_ = crate::leanh::lean_box(0);
                        v_isShared_3930_ = v_isSharedCheck_3934_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3868_ = crate::leanh::lean_ctor_get(v_a_3864_, 1);
                v___x_3869_ = (crate::leanh::lean_unbox(v_snd_3868_) as u8);
                if v___x_3869_ == 0 {
                    crate::leanh::lean_dec(v_a_3862_);
                    crate::leanh::lean_dec(v_x_3852_);
                    v_fst_3870_ = crate::leanh::lean_ctor_get(v_a_3864_, 0);
                    crate::leanh::lean_inc(v_fst_3870_);
                    crate::leanh::lean_dec(v_a_3864_);
                    if v_isShared_3867_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3866_, 0, v_fst_3870_);
                        v___x_3872_ = v___x_3866_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_fst_3870_);
                        v___x_3872_ = v_reuseFailAlloc_3873_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3866_);
                    v_fst_3874_ = crate::leanh::lean_ctor_get(v_a_3864_, 0);
                    v_isSharedCheck_3916_ = (!crate::leanh::lean_is_exclusive(v_a_3864_)) as u8;
                    if v_isSharedCheck_3916_ == 0 {
                        v_unused_3917_ = crate::leanh::lean_ctor_get(v_a_3864_, 1);
                        crate::leanh::lean_dec(v_unused_3917_);
                        v___x_3876_ = v_a_3864_;
                        v_isShared_3877_ = v_isSharedCheck_3916_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3874_);
                        crate::leanh::lean_dec(v_a_3864_);
                        v___x_3876_ = crate::leanh::lean_box(0);
                        v_isShared_3877_ = v_isSharedCheck_3916_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3872_;
            }
            3 => {
                v___x_3878_ =
                    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1;
                v___x_3879_ =
                    l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_3878_, v_a_3857_);
                if crate::leanh::lean_obj_tag(v___x_3879_) == 0 {
                    v_a_3880_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                    v_isSharedCheck_3907_ = (!crate::leanh::lean_is_exclusive(v___x_3879_)) as u8;
                    if v_isSharedCheck_3907_ == 0 {
                        v___x_3882_ = v___x_3879_;
                        v_isShared_3883_ = v_isSharedCheck_3907_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3880_);
                        crate::leanh::lean_dec(v___x_3879_);
                        v___x_3882_ = crate::leanh::lean_box(0);
                        v_isShared_3883_ = v_isSharedCheck_3907_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3876_);
                    crate::leanh::lean_dec(v_fst_3874_);
                    crate::leanh::lean_dec(v_a_3862_);
                    crate::leanh::lean_dec(v_x_3852_);
                    v_a_3908_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                    v_isSharedCheck_3915_ = (!crate::leanh::lean_is_exclusive(v___x_3879_)) as u8;
                    if v_isSharedCheck_3915_ == 0 {
                        v___x_3910_ = v___x_3879_;
                        v_isShared_3911_ = v_isSharedCheck_3915_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3908_);
                        crate::leanh::lean_dec(v___x_3879_);
                        v___x_3910_ = crate::leanh::lean_box(0);
                        v_isShared_3911_ = v_isSharedCheck_3915_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_size_3884_ = crate::leanh::lean_ctor_get(v_info_3853_, 2);
                v___x_3885_ = lean_st_ref_take(v_a_3857_);
                v_lctx_3886_ = crate::leanh::lean_ctor_get(v___x_3885_, 0);
                v_nextIdx_3887_ = crate::leanh::lean_ctor_get(v___x_3885_, 1);
                v_isSharedCheck_3906_ = (!crate::leanh::lean_is_exclusive(v___x_3885_)) as u8;
                if v_isSharedCheck_3906_ == 0 {
                    v___x_3889_ = v___x_3885_;
                    v_isShared_3890_ = v_isSharedCheck_3906_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_3887_);
                    crate::leanh::lean_inc(v_lctx_3886_);
                    crate::leanh::lean_dec(v___x_3885_);
                    v___x_3889_ = crate::leanh::lean_box(0);
                    v_isShared_3890_ = v_isSharedCheck_3906_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3891_ = 1;
                crate::leanh::lean_inc(v_size_3884_);
                if v_isShared_3877_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3876_, 11);
                    crate::leanh::lean_ctor_set(v___x_3876_, 1, v_x_3852_);
                    crate::leanh::lean_ctor_set(v___x_3876_, 0, v_size_3884_);
                    v___x_3893_ = v___x_3876_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = crate::leanh::lean_alloc_ctor(11, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_size_3884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_x_3852_);
                    v___x_3893_ = v_reuseFailAlloc_3905_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4);
                v___x_3895_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3895_, 0, v_a_3862_);
                crate::leanh::lean_ctor_set(v___x_3895_, 1, v_a_3880_);
                crate::leanh::lean_ctor_set(v___x_3895_, 2, v___x_3894_);
                crate::leanh::lean_ctor_set(v___x_3895_, 3, v___x_3893_);
                crate::leanh::lean_inc_ref(v___x_3895_);
                v___x_3896_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3891_, v_lctx_3886_, v___x_3895_);
                if v_isShared_3890_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3889_, 0, v___x_3896_);
                    v___x_3898_ = v___x_3889_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_nextIdx_3887_);
                    v___x_3898_ = v_reuseFailAlloc_3904_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3899_ = lean_st_ref_set(v_a_3857_, v___x_3898_);
                v___x_3900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3900_, 0, v___x_3895_);
                crate::leanh::lean_ctor_set(v___x_3900_, 1, v_fst_3874_);
                if v_isShared_3883_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3900_);
                    v___x_3902_ = v___x_3882_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3902_;
            }
            9 => {
                if v_isShared_3911_ == 0 {
                    v___x_3913_ = v___x_3910_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3914_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
                    v___x_3913_ = v_reuseFailAlloc_3914_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3913_;
            }
            11 => {
                if v_isShared_3922_ == 0 {
                    v___x_3924_ = v___x_3921_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3924_;
            }
            13 => {
                if v_isShared_3930_ == 0 {
                    v___x_3932_ = v___x_3929_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
                    v___x_3932_ = v_reuseFailAlloc_3933_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(
    mut v_x_3935_: *mut crate::leanh::LeanObject,
    mut v_info_3936_: *mut crate::leanh::LeanObject,
    mut v_c_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_a_3942_: *mut crate::leanh::LeanObject,
    mut v_a_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3944_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(
        v_x_3935_,
        v_info_3936_,
        v_c_3937_,
        v_a_3938_,
        v_a_3939_,
        v_a_3940_,
        v_a_3941_,
        v_a_3942_,
    );
    crate::leanh::lean_dec(v_a_3942_);
    crate::leanh::lean_dec_ref(v_a_3941_);
    crate::leanh::lean_dec(v_a_3940_);
    crate::leanh::lean_dec_ref(v_a_3939_);
    crate::leanh::lean_dec_ref(v_a_3938_);
    crate::leanh::lean_dec_ref(v_info_3936_);
    return v_res_3944_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(
    mut v___y_3945_: *mut crate::leanh::LeanObject,
    mut v___y_3946_: *mut crate::leanh::LeanObject,
    mut v___y_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_3949_);
    return v___x_3951_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
    mut v___y_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3958_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
    crate::leanh::lean_dec(v___y_3956_);
    crate::leanh::lean_dec_ref(v___y_3955_);
    crate::leanh::lean_dec(v___y_3954_);
    crate::leanh::lean_dec_ref(v___y_3953_);
    crate::leanh::lean_dec_ref(v___y_3952_);
    return v_res_3958_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(
    mut v_x_3959_: *mut crate::leanh::LeanObject,
    mut v_as_3960_: *mut crate::leanh::LeanObject,
    mut v_i_3961_: usize,
    mut v_stop_3962_: usize,
) -> u8 {
    let mut v___x_3963_: u8 = 0;
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    let mut v___x_3968_: usize = 0;
    let mut v___x_3969_: usize = 0;
    let mut v___x_3971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3963_ = lean_usize_dec_eq(v_i_3961_, v_stop_3962_);
                if v___x_3963_ == 0 {
                    v___x_3964_ = lean_array_uget_borrowed(v_as_3960_, v_i_3961_);
                    v___x_3965_ = 1;
                    crate::leanh::lean_inc(v_x_3959_);
                    v___x_3966_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_3959_);
                    v___x_3967_ =
                        l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(
                            v___x_3965_,
                            v___x_3964_,
                            v___x_3966_,
                        );
                    crate::leanh::lean_dec(v___x_3966_);
                    if v___x_3967_ == 0 {
                        v___x_3968_ = 1usize;
                        v___x_3969_ = lean_usize_add(v_i_3961_, v___x_3968_);
                        v_i_3961_ = v___x_3969_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3959_);
                        return v___x_3967_;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3959_);
                    v___x_3971_ = 0;
                    return v___x_3971_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(
    mut v_x_3972_: *mut crate::leanh::LeanObject,
    mut v_as_3973_: *mut crate::leanh::LeanObject,
    mut v_i_3974_: *mut crate::leanh::LeanObject,
    mut v_stop_3975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3976_: usize = 0;
    let mut v_stop_boxed_3977_: usize = 0;
    let mut v_res_3978_: u8 = 0;
    let mut v_r_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3976_ = crate::leanh::lean_unbox_usize(v_i_3974_);
    crate::leanh::lean_dec(v_i_3974_);
    v_stop_boxed_3977_ = crate::leanh::lean_unbox_usize(v_stop_3975_);
    crate::leanh::lean_dec(v_stop_3975_);
    v_res_3978_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_3972_, v_as_3973_, v_i_boxed_3976_, v_stop_boxed_3977_);
    crate::leanh::lean_dec_ref(v_as_3973_);
    v_r_3979_ = crate::leanh::lean_box((v_res_3978_) as usize);
    return v_r_3979_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(
    mut v_instr_3980_: *mut crate::leanh::LeanObject,
    mut v_x_3981_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_instr_3980_) == 0 {
        let mut v_decl_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_decl_3982_ = crate::leanh::lean_ctor_get(v_instr_3980_, 0);
        v_value_3983_ = crate::leanh::lean_ctor_get(v_decl_3982_, 3);
        if crate::leanh::lean_obj_tag(v_value_3983_) == 5 {
            let mut v_args_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3987_: u8 = 0;
            v_args_3984_ = crate::leanh::lean_ctor_get(v_value_3983_, 1);
            v___x_3985_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_3986_ = lean_array_get_size(v_args_3984_);
            v___x_3987_ = lean_nat_dec_lt(v___x_3985_, v___x_3986_);
            if v___x_3987_ == 0 {
                crate::leanh::lean_dec(v_x_3981_);
                return v___x_3987_;
            } else {
                if v___x_3987_ == 0 {
                    crate::leanh::lean_dec(v_x_3981_);
                    return v___x_3987_;
                } else {
                    let mut v___x_3988_: usize = 0;
                    let mut v___x_3989_: usize = 0;
                    let mut v___x_3990_: u8 = 0;
                    v___x_3988_ = 0usize;
                    v___x_3989_ = lean_usize_of_nat(v___x_3986_);
                    v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_3981_, v_args_3984_, v___x_3988_, v___x_3989_);
                    return v___x_3990_;
                }
            }
        } else {
            let mut v___x_3991_: u8 = 0;
            crate::leanh::lean_dec(v_x_3981_);
            v___x_3991_ = 0;
            return v___x_3991_;
        }
    } else {
        let mut v___x_3992_: u8 = 0;
        crate::leanh::lean_dec(v_x_3981_);
        v___x_3992_ = 0;
        return v___x_3992_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(
    mut v_instr_3993_: *mut crate::leanh::LeanObject,
    mut v_x_3994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3995_: u8 = 0;
    let mut v_r_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3995_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(
        v_instr_3993_,
        v_x_3994_,
    );
    crate::leanh::lean_dec_ref(v_instr_3993_);
    v_r_3996_ = crate::leanh::lean_box((v_res_3995_) as usize);
    return v_r_3996_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(
    mut v_x_3997_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3997_ {
        0 => {
            let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3998_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3998_;
        }
        1 => {
            let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3999_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3999_;
        }
        _ => {
            let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4000_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4000_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(
    mut v_x_4001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4002_: u8 = 0;
    let mut v_res_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4002_ = (crate::leanh::lean_unbox(v_x_4001_) as u8);
    v_res_4003_ =
        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(
            v_x_boxed_4002_,
        );
    return v_res_4003_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(
    mut v_x_4004_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4005_ =
        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(
            v_x_4004_,
        );
    return v___x_4005_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx___boxed(
    mut v_x_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4007_: u8 = 0;
    let mut v_res_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4007_ = (crate::leanh::lean_unbox(v_x_4006_) as u8);
    v_res_4008_ =
        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(
            v_x_4__boxed_4007_,
        );
    return v_res_4008_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(
    mut v_k_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4009_);
    return v_k_4009_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(
    mut v_k_4010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4011_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(v_k_4010_);
    crate::leanh::lean_dec(v_k_4010_);
    return v_res_4011_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(
    mut v_motive_4012_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4013_: *mut crate::leanh::LeanObject,
    mut v_t_4014_: u8,
    mut v_h_4015_: *mut crate::leanh::LeanObject,
    mut v_k_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4016_);
    return v_k_4016_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(
    mut v_motive_4017_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4018_: *mut crate::leanh::LeanObject,
    mut v_t_4019_: *mut crate::leanh::LeanObject,
    mut v_h_4020_: *mut crate::leanh::LeanObject,
    mut v_k_4021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4022_: u8 = 0;
    let mut v_res_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4022_ = (crate::leanh::lean_unbox(v_t_4019_) as u8);
    v_res_4023_ =
        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(
            v_motive_4017_,
            v_ctorIdx_4018_,
            v_t_boxed_4022_,
            v_h_4020_,
            v_k_4021_,
        );
    crate::leanh::lean_dec(v_k_4021_);
    crate::leanh::lean_dec(v_ctorIdx_4018_);
    return v_res_4023_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(
    mut v_ownedArg_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ownedArg_4024_);
    return v_ownedArg_4024_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(
    mut v_ownedArg_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4026_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(v_ownedArg_4025_);
    crate::leanh::lean_dec(v_ownedArg_4025_);
    return v_res_4026_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(
    mut v_motive_4027_: *mut crate::leanh::LeanObject,
    mut v_t_4028_: u8,
    mut v_h_4029_: *mut crate::leanh::LeanObject,
    mut v_ownedArg_4030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ownedArg_4030_);
    return v_ownedArg_4030_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(
    mut v_motive_4031_: *mut crate::leanh::LeanObject,
    mut v_t_4032_: *mut crate::leanh::LeanObject,
    mut v_h_4033_: *mut crate::leanh::LeanObject,
    mut v_ownedArg_4034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4035_: u8 = 0;
    let mut v_res_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4035_ = (crate::leanh::lean_unbox(v_t_4032_) as u8);
    v_res_4036_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(v_motive_4031_, v_t_boxed_4035_, v_h_4033_, v_ownedArg_4034_);
    crate::leanh::lean_dec(v_ownedArg_4034_);
    return v_res_4036_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(
    mut v_other_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_other_4037_);
    return v_other_4037_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(
    mut v_other_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4039_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(v_other_4038_);
    crate::leanh::lean_dec(v_other_4038_);
    return v_res_4039_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(
    mut v_motive_4040_: *mut crate::leanh::LeanObject,
    mut v_t_4041_: u8,
    mut v_h_4042_: *mut crate::leanh::LeanObject,
    mut v_other_4043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_other_4043_);
    return v_other_4043_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(
    mut v_motive_4044_: *mut crate::leanh::LeanObject,
    mut v_t_4045_: *mut crate::leanh::LeanObject,
    mut v_h_4046_: *mut crate::leanh::LeanObject,
    mut v_other_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4048_: u8 = 0;
    let mut v_res_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4048_ = (crate::leanh::lean_unbox(v_t_4045_) as u8);
    v_res_4049_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(v_motive_4044_, v_t_boxed_4048_, v_h_4046_, v_other_4047_);
    crate::leanh::lean_dec(v_other_4047_);
    return v_res_4049_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(
    mut v_none_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_4050_);
    return v_none_4050_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(
    mut v_none_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4052_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(v_none_4051_);
    crate::leanh::lean_dec(v_none_4051_);
    return v_res_4052_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(
    mut v_motive_4053_: *mut crate::leanh::LeanObject,
    mut v_t_4054_: u8,
    mut v_h_4055_: *mut crate::leanh::LeanObject,
    mut v_none_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_4056_);
    return v_none_4056_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(
    mut v_motive_4057_: *mut crate::leanh::LeanObject,
    mut v_t_4058_: *mut crate::leanh::LeanObject,
    mut v_h_4059_: *mut crate::leanh::LeanObject,
    mut v_none_4060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4061_: u8 = 0;
    let mut v_res_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4061_ = (crate::leanh::lean_unbox(v_t_4058_) as u8);
    v_res_4062_ =
        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(
            v_motive_4057_,
            v_t_boxed_4061_,
            v_h_4059_,
            v_none_4060_,
        );
    crate::leanh::lean_dec(v_none_4060_);
    return v_res_4062_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(
    mut v_x_4063_: *mut crate::leanh::LeanObject,
    mut v_as_4064_: *mut crate::leanh::LeanObject,
    mut v_sz_4065_: usize,
    mut v_i_4066_: usize,
    mut v_b_4067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: usize = 0;
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4080_: u8 = 0;
    let mut v_array_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v_a_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: u8 = 0;
    let mut v_borrow_4108_: u8 = 0;
    let mut v___x_4109_: u8 = 0;
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: u8 = 0;
    let mut v_borrow_4112_: u8 = 0;
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: u8 = 0;
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_unused_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4074_ = lean_usize_dec_lt(v_i_4066_, v_sz_4065_);
                if v___x_4074_ == 0 {
                    v___x_4075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4075_, 0, v_b_4067_);
                    return v___x_4075_;
                } else {
                    v_snd_4076_ = crate::leanh::lean_ctor_get(v_b_4067_, 1);
                    v_fst_4077_ = crate::leanh::lean_ctor_get(v_b_4067_, 0);
                    v_isSharedCheck_4121_ = (!crate::leanh::lean_is_exclusive(v_b_4067_)) as u8;
                    if v_isSharedCheck_4121_ == 0 {
                        v___x_4079_ = v_b_4067_;
                        v_isShared_4080_ = v_isSharedCheck_4121_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4076_);
                        crate::leanh::lean_inc(v_fst_4077_);
                        crate::leanh::lean_dec(v_b_4067_);
                        v___x_4079_ = crate::leanh::lean_box(0);
                        v_isShared_4080_ = v_isSharedCheck_4121_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4071_ = 1usize;
                v___x_4072_ = lean_usize_add(v_i_4066_, v___x_4071_);
                v_i_4066_ = v___x_4072_;
                v_b_4067_ = v_a_4070_;
                state = 0;
                continue;
            }
            2 => {
                v_array_4081_ = crate::leanh::lean_ctor_get(v_snd_4076_, 0);
                v_start_4082_ = crate::leanh::lean_ctor_get(v_snd_4076_, 1);
                v_stop_4083_ = crate::leanh::lean_ctor_get(v_snd_4076_, 2);
                v___x_4084_ = lean_nat_dec_lt(v_start_4082_, v_stop_4083_);
                if v___x_4084_ == 0 {
                    if v_isShared_4080_ == 0 {
                        v___x_4086_ = v___x_4079_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4088_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_fst_4077_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_snd_4076_);
                        v___x_4086_ = v_reuseFailAlloc_4088_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_4083_);
                    crate::leanh::lean_inc(v_start_4082_);
                    crate::leanh::lean_inc_ref(v_array_4081_);
                    v_isSharedCheck_4117_ = (!crate::leanh::lean_is_exclusive(v_snd_4076_)) as u8;
                    if v_isSharedCheck_4117_ == 0 {
                        v_unused_4118_ = crate::leanh::lean_ctor_get(v_snd_4076_, 2);
                        crate::leanh::lean_dec(v_unused_4118_);
                        v_unused_4119_ = crate::leanh::lean_ctor_get(v_snd_4076_, 1);
                        crate::leanh::lean_dec(v_unused_4119_);
                        v_unused_4120_ = crate::leanh::lean_ctor_get(v_snd_4076_, 0);
                        crate::leanh::lean_dec(v_unused_4120_);
                        v___x_4090_ = v_snd_4076_;
                        v_isShared_4091_ = v_isSharedCheck_4117_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_4076_);
                        v___x_4090_ = crate::leanh::lean_box(0);
                        v_isShared_4091_ = v_isSharedCheck_4117_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4087_, 0, v___x_4086_);
                return v___x_4087_;
            }
            4 => {
                v_a_4092_ = lean_array_uget_borrowed(v_as_4064_, v_i_4066_);
                v___x_4093_ = lean_array_fget(v_array_4081_, v_start_4082_);
                v___x_4094_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4095_ = lean_nat_add(v_start_4082_, v___x_4094_);
                crate::leanh::lean_dec(v_start_4082_);
                if v_isShared_4091_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4090_, 1, v___x_4095_);
                    v___x_4097_ = v___x_4090_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4116_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_array_4081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 1, v___x_4095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 2, v_stop_4083_);
                    v___x_4097_ = v_reuseFailAlloc_4116_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_4092_) == 1 {
                    v_fvarId_4104_ = crate::leanh::lean_ctor_get(v_a_4092_, 0);
                    v___x_4105_ = l_Lean_instBEqFVarId_beq(v_fvarId_4104_, v_x_4063_);
                    if v___x_4105_ == 0 {
                        crate::leanh::lean_dec(v___x_4093_);
                        crate::leanh::lean_del_object(v___x_4079_);
                        v___x_4106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4106_, 0, v_fst_4077_);
                        crate::leanh::lean_ctor_set(v___x_4106_, 1, v___x_4097_);
                        v_a_4070_ = v___x_4106_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4107_ = (crate::leanh::lean_unbox(v_fst_4077_) as u8);
                        match v___x_4107_ {
                            0 => {
                                v_borrow_4108_ = crate::leanh::lean_ctor_get_uint8(
                                    v___x_4093_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                                        as u32,
                                );
                                crate::leanh::lean_dec(v___x_4093_);
                                if v_borrow_4108_ == 0 {
                                    v___x_4109_ = (crate::leanh::lean_unbox(v_fst_4077_) as u8);
                                    crate::leanh::lean_dec(v_fst_4077_);
                                    v___y_4099_ = v___x_4109_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_fst_4077_);
                                    v___x_4110_ = 1;
                                    v___y_4099_ = v___x_4110_;
                                    state = 6;
                                    continue;
                                }
                            }
                            1 => {
                                crate::leanh::lean_dec(v___x_4093_);
                                v___x_4111_ = (crate::leanh::lean_unbox(v_fst_4077_) as u8);
                                crate::leanh::lean_dec(v_fst_4077_);
                                v___y_4099_ = v___x_4111_;
                                state = 6;
                                continue;
                            }
                            _ => {
                                crate::leanh::lean_dec(v_fst_4077_);
                                v_borrow_4112_ = crate::leanh::lean_ctor_get_uint8(
                                    v___x_4093_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                                        as u32,
                                );
                                crate::leanh::lean_dec(v___x_4093_);
                                if v_borrow_4112_ == 0 {
                                    v___x_4113_ = 0;
                                    v___y_4099_ = v___x_4113_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_4114_ = 1;
                                    v___y_4099_ = v___x_4114_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4093_);
                    crate::leanh::lean_del_object(v___x_4079_);
                    v___x_4115_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4115_, 0, v_fst_4077_);
                    crate::leanh::lean_ctor_set(v___x_4115_, 1, v___x_4097_);
                    v_a_4070_ = v___x_4115_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_4100_ = crate::leanh::lean_box((v___y_4099_) as usize);
                if v_isShared_4080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4079_, 1, v___x_4097_);
                    crate::leanh::lean_ctor_set(v___x_4079_, 0, v___x_4100_);
                    v___x_4102_ = v___x_4079_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4103_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4103_, 1, v___x_4097_);
                    v___x_4102_ = v_reuseFailAlloc_4103_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_4070_ = v___x_4102_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(
    mut v_x_4122_: *mut crate::leanh::LeanObject,
    mut v_as_4123_: *mut crate::leanh::LeanObject,
    mut v_sz_4124_: *mut crate::leanh::LeanObject,
    mut v_i_4125_: *mut crate::leanh::LeanObject,
    mut v_b_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4128_: usize = 0;
    let mut v_i_boxed_4129_: usize = 0;
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4128_ = crate::leanh::lean_unbox_usize(v_sz_4124_);
    crate::leanh::lean_dec(v_sz_4124_);
    v_i_boxed_4129_ = crate::leanh::lean_unbox_usize(v_i_4125_);
    crate::leanh::lean_dec(v_i_4125_);
    v_res_4130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_4122_, v_as_4123_, v_sz_boxed_4128_, v_i_boxed_4129_, v_b_4126_);
    crate::leanh::lean_dec_ref(v_as_4123_);
    crate::leanh::lean_dec(v_x_4122_);
    return v_res_4130_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(
    mut v_instr_4131_: *mut crate::leanh::LeanObject,
    mut v_x_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
    mut v_a_4134_: *mut crate::leanh::LeanObject,
    mut v_a_4135_: *mut crate::leanh::LeanObject,
    mut v_a_4136_: *mut crate::leanh::LeanObject,
    mut v_a_4137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: u8 = 0;
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: u8 = 0;
    let mut v___x_4143_: u8 = 0;
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v_val_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: u8 = 0;
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4171_: usize = 0;
    let mut v___x_4172_: usize = 0;
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v_fst_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4182_: u8 = 0;
    let mut v_a_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4190_: u8 = 0;
    let mut v___x_4191_: u8 = 0;
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: u8 = 0;
    let mut v___x_4194_: u8 = 0;
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: u8 = 0;
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v_a_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_reuseFailAlloc_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4214_: u8 = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v_fn_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4222_: u8 = 0;
    let mut v___x_4223_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: u8 = 0;
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: u8 = 0;
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4239_: u8 = 0;
    let mut v_isSharedCheck_4240_: u8 = 0;
    let mut v_unused_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4244_: u8 = 0;
    let mut v_fvarId_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4249_: u8 = 0;
    let mut v___x_4250_: u8 = 0;
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: u8 = 0;
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: u8 = 0;
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v_isSharedCheck_4267_: u8 = 0;
    let mut v_unused_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_instr_4131_) == 0 {
                    v_decl_4149_ = crate::leanh::lean_ctor_get(v_instr_4131_, 0);
                    v_value_4150_ = crate::leanh::lean_ctor_get(v_decl_4149_, 3);
                    crate::leanh::lean_inc(v_value_4150_);
                    match crate::leanh::lean_obj_tag(v_value_4150_) {
                        9 => {
                            crate::leanh::lean_dec_ref_known(v_instr_4131_, 1);
                            v_fn_4151_ = crate::leanh::lean_ctor_get(v_value_4150_, 0);
                            v_args_4152_ = crate::leanh::lean_ctor_get(v_value_4150_, 1);
                            v_isSharedCheck_4214_ =
                                (!crate::leanh::lean_is_exclusive(v_value_4150_)) as u8;
                            if v_isSharedCheck_4214_ == 0 {
                                v___x_4154_ = v_value_4150_;
                                v_isShared_4155_ = v_isSharedCheck_4214_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_args_4152_);
                                crate::leanh::lean_inc(v_fn_4151_);
                                crate::leanh::lean_dec(v_value_4150_);
                                v___x_4154_ = crate::leanh::lean_box(0);
                                v_isShared_4155_ = v_isSharedCheck_4214_;
                                state = 2;
                                continue;
                            }
                        }
                        10 => {
                            v_isSharedCheck_4240_ =
                                (!crate::leanh::lean_is_exclusive(v_instr_4131_)) as u8;
                            if v_isSharedCheck_4240_ == 0 {
                                v_unused_4241_ = crate::leanh::lean_ctor_get(v_instr_4131_, 0);
                                crate::leanh::lean_dec(v_unused_4241_);
                                v___x_4216_ = v_instr_4131_;
                                v_isShared_4217_ = v_isSharedCheck_4240_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_instr_4131_);
                                v___x_4216_ = crate::leanh::lean_box(0);
                                v_isShared_4217_ = v_isSharedCheck_4240_;
                                state = 13;
                                continue;
                            }
                        }
                        4 => {
                            v_isSharedCheck_4267_ =
                                (!crate::leanh::lean_is_exclusive(v_instr_4131_)) as u8;
                            if v_isSharedCheck_4267_ == 0 {
                                v_unused_4268_ = crate::leanh::lean_ctor_get(v_instr_4131_, 0);
                                crate::leanh::lean_dec(v_unused_4268_);
                                v___x_4243_ = v_instr_4131_;
                                v_isShared_4244_ = v_isSharedCheck_4267_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_instr_4131_);
                                v___x_4243_ = crate::leanh::lean_box(0);
                                v_isShared_4244_ = v_isSharedCheck_4267_;
                                state = 18;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_value_4150_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4140_ = 1;
                v___x_4141_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_4132_);
                v___x_4142_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(
                    v___x_4140_,
                    v_instr_4131_,
                    v___x_4141_,
                );
                crate::leanh::lean_dec(v___x_4141_);
                crate::leanh::lean_dec_ref(v_instr_4131_);
                if v___x_4142_ == 0 {
                    v___x_4143_ = 2;
                    v___x_4144_ = crate::leanh::lean_box((v___x_4143_) as usize);
                    v___x_4145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4145_, 0, v___x_4144_);
                    return v___x_4145_;
                } else {
                    v___x_4146_ = 1;
                    v___x_4147_ = crate::leanh::lean_box((v___x_4146_) as usize);
                    v___x_4148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4148_, 0, v___x_4147_);
                    return v___x_4148_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_args_4152_);
                crate::leanh::lean_inc(v_fn_4151_);
                if v_isShared_4155_ == 0 {
                    v___x_4157_ = v___x_4154_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4213_ = crate::leanh::lean_alloc_ctor(9, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_fn_4151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4213_, 1, v_args_4152_);
                    v___x_4157_ = v_reuseFailAlloc_4213_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4158_ =
                    l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_4151_, v_a_4137_);
                if crate::leanh::lean_obj_tag(v___x_4158_) == 0 {
                    v_a_4159_ = crate::leanh::lean_ctor_get(v___x_4158_, 0);
                    v_isSharedCheck_4204_ = (!crate::leanh::lean_is_exclusive(v___x_4158_)) as u8;
                    if v_isSharedCheck_4204_ == 0 {
                        v___x_4161_ = v___x_4158_;
                        v_isShared_4162_ = v_isSharedCheck_4204_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4159_);
                        crate::leanh::lean_dec(v___x_4158_);
                        v___x_4161_ = crate::leanh::lean_box(0);
                        v_isShared_4162_ = v_isSharedCheck_4204_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4157_);
                    crate::leanh::lean_dec_ref(v_args_4152_);
                    crate::leanh::lean_dec(v_x_4132_);
                    v_a_4205_ = crate::leanh::lean_ctor_get(v___x_4158_, 0);
                    v_isSharedCheck_4212_ = (!crate::leanh::lean_is_exclusive(v___x_4158_)) as u8;
                    if v_isSharedCheck_4212_ == 0 {
                        v___x_4207_ = v___x_4158_;
                        v_isShared_4208_ = v_isSharedCheck_4212_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4205_);
                        crate::leanh::lean_dec(v___x_4158_);
                        v___x_4207_ = crate::leanh::lean_box(0);
                        v_isShared_4208_ = v_isSharedCheck_4212_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4159_) == 1 {
                    crate::leanh::lean_del_object(v___x_4161_);
                    crate::leanh::lean_dec_ref(v___x_4157_);
                    v_val_4163_ = crate::leanh::lean_ctor_get(v_a_4159_, 0);
                    crate::leanh::lean_inc(v_val_4163_);
                    crate::leanh::lean_dec_ref_known(v_a_4159_, 1);
                    v_params_4164_ = crate::leanh::lean_ctor_get(v_val_4163_, 3);
                    crate::leanh::lean_inc_ref(v_params_4164_);
                    crate::leanh::lean_dec(v_val_4163_);
                    v___x_4165_ = 2;
                    v___x_4166_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4167_ = lean_array_get_size(v_params_4164_);
                    v___x_4168_ =
                        l_Array_toSubarray___redArg(v_params_4164_, v___x_4166_, v___x_4167_);
                    v___x_4169_ = crate::leanh::lean_box((v___x_4165_) as usize);
                    v___x_4170_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4170_, 0, v___x_4169_);
                    crate::leanh::lean_ctor_set(v___x_4170_, 1, v___x_4168_);
                    v_sz_4171_ = lean_array_size(v_args_4152_);
                    v___x_4172_ = 0usize;
                    v___x_4173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_4132_, v_args_4152_, v_sz_4171_, v___x_4172_, v___x_4170_);
                    crate::leanh::lean_dec_ref(v_args_4152_);
                    crate::leanh::lean_dec(v_x_4132_);
                    if crate::leanh::lean_obj_tag(v___x_4173_) == 0 {
                        v_a_4174_ = crate::leanh::lean_ctor_get(v___x_4173_, 0);
                        v_isSharedCheck_4182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4182_ == 0 {
                            v___x_4176_ = v___x_4173_;
                            v_isShared_4177_ = v_isSharedCheck_4182_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4174_);
                            crate::leanh::lean_dec(v___x_4173_);
                            v___x_4176_ = crate::leanh::lean_box(0);
                            v_isShared_4177_ = v_isSharedCheck_4182_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4183_ = crate::leanh::lean_ctor_get(v___x_4173_, 0);
                        v_isSharedCheck_4190_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4190_ == 0 {
                            v___x_4185_ = v___x_4173_;
                            v_isShared_4186_ = v_isSharedCheck_4190_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4183_);
                            crate::leanh::lean_dec(v___x_4173_);
                            v___x_4185_ = crate::leanh::lean_box(0);
                            v_isShared_4186_ = v_isSharedCheck_4190_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4159_);
                    crate::leanh::lean_dec_ref(v_args_4152_);
                    v___x_4191_ = 1;
                    v___x_4192_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_4132_);
                    v___x_4193_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_4191_, v___x_4157_, v___x_4192_);
                    crate::leanh::lean_dec(v___x_4192_);
                    crate::leanh::lean_dec_ref(v___x_4157_);
                    if v___x_4193_ == 0 {
                        v___x_4194_ = 2;
                        v___x_4195_ = crate::leanh::lean_box((v___x_4194_) as usize);
                        if v_isShared_4162_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4161_, 0, v___x_4195_);
                            v___x_4197_ = v___x_4161_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_4198_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4195_);
                            v___x_4197_ = v_reuseFailAlloc_4198_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___x_4199_ = 0;
                        v___x_4200_ = crate::leanh::lean_box((v___x_4199_) as usize);
                        if v_isShared_4162_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4161_, 0, v___x_4200_);
                            v___x_4202_ = v___x_4161_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_4203_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
                            v___x_4202_ = v_reuseFailAlloc_4203_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v_fst_4178_ = crate::leanh::lean_ctor_get(v_a_4174_, 0);
                crate::leanh::lean_inc(v_fst_4178_);
                crate::leanh::lean_dec(v_a_4174_);
                if v_isShared_4177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4176_, 0, v_fst_4178_);
                    v___x_4180_ = v___x_4176_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_fst_4178_);
                    v___x_4180_ = v_reuseFailAlloc_4181_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4180_;
            }
            7 => {
                if v_isShared_4186_ == 0 {
                    v___x_4188_ = v___x_4185_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
                    v___x_4188_ = v_reuseFailAlloc_4189_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4188_;
            }
            9 => {
                return v___x_4197_;
            }
            10 => {
                return v___x_4202_;
            }
            11 => {
                if v_isShared_4208_ == 0 {
                    v___x_4210_ = v___x_4207_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
                    v___x_4210_ = v_reuseFailAlloc_4211_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4210_;
            }
            13 => {
                v_fn_4218_ = crate::leanh::lean_ctor_get(v_value_4150_, 0);
                v_args_4219_ = crate::leanh::lean_ctor_get(v_value_4150_, 1);
                v_isSharedCheck_4239_ = (!crate::leanh::lean_is_exclusive(v_value_4150_)) as u8;
                if v_isSharedCheck_4239_ == 0 {
                    v___x_4221_ = v_value_4150_;
                    v_isShared_4222_ = v_isSharedCheck_4239_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_args_4219_);
                    crate::leanh::lean_inc(v_fn_4218_);
                    crate::leanh::lean_dec(v_value_4150_);
                    v___x_4221_ = crate::leanh::lean_box(0);
                    v_isShared_4222_ = v_isSharedCheck_4239_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4223_ = 1;
                if v_isShared_4222_ == 0 {
                    v___x_4225_ = v___x_4221_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4238_ = crate::leanh::lean_alloc_ctor(10, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_fn_4218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_args_4219_);
                    v___x_4225_ = v_reuseFailAlloc_4238_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4226_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_4132_);
                v___x_4227_ =
                    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(
                        v___x_4223_,
                        v___x_4225_,
                        v___x_4226_,
                    );
                crate::leanh::lean_dec(v___x_4226_);
                crate::leanh::lean_dec_ref(v___x_4225_);
                if v___x_4227_ == 0 {
                    v___x_4228_ = 2;
                    v___x_4229_ = crate::leanh::lean_box((v___x_4228_) as usize);
                    if v_isShared_4217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4216_, 0, v___x_4229_);
                        v___x_4231_ = v___x_4216_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4229_);
                        v___x_4231_ = v_reuseFailAlloc_4232_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_4233_ = 0;
                    v___x_4234_ = crate::leanh::lean_box((v___x_4233_) as usize);
                    if v_isShared_4217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4216_, 0, v___x_4234_);
                        v___x_4236_ = v___x_4216_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4237_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
                        v___x_4236_ = v_reuseFailAlloc_4237_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_4231_;
            }
            17 => {
                return v___x_4236_;
            }
            18 => {
                v_fvarId_4245_ = crate::leanh::lean_ctor_get(v_value_4150_, 0);
                v_args_4246_ = crate::leanh::lean_ctor_get(v_value_4150_, 1);
                v_isSharedCheck_4266_ = (!crate::leanh::lean_is_exclusive(v_value_4150_)) as u8;
                if v_isSharedCheck_4266_ == 0 {
                    v___x_4248_ = v_value_4150_;
                    v_isShared_4249_ = v_isSharedCheck_4266_;
                    state = 19;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_args_4246_);
                    crate::leanh::lean_inc(v_fvarId_4245_);
                    crate::leanh::lean_dec(v_value_4150_);
                    v___x_4248_ = crate::leanh::lean_box(0);
                    v_isShared_4249_ = v_isSharedCheck_4266_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_4250_ = 1;
                if v_isShared_4249_ == 0 {
                    v___x_4252_ = v___x_4248_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_fvarId_4245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 1, v_args_4246_);
                    v___x_4252_ = v_reuseFailAlloc_4265_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_4253_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_4132_);
                v___x_4254_ =
                    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(
                        v___x_4250_,
                        v___x_4252_,
                        v___x_4253_,
                    );
                crate::leanh::lean_dec(v___x_4253_);
                crate::leanh::lean_dec_ref(v___x_4252_);
                if v___x_4254_ == 0 {
                    v___x_4255_ = 2;
                    v___x_4256_ = crate::leanh::lean_box((v___x_4255_) as usize);
                    if v_isShared_4244_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4256_);
                        v___x_4258_ = v___x_4243_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_4259_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
                        v___x_4258_ = v_reuseFailAlloc_4259_;
                        state = 21;
                        continue;
                    }
                } else {
                    v___x_4260_ = 0;
                    v___x_4261_ = crate::leanh::lean_box((v___x_4260_) as usize);
                    if v_isShared_4244_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4261_);
                        v___x_4263_ = v___x_4243_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_4264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
                        v___x_4263_ = v_reuseFailAlloc_4264_;
                        state = 22;
                        continue;
                    }
                }
            }
            21 => {
                return v___x_4258_;
            }
            22 => {
                return v___x_4263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(
    mut v_instr_4269_: *mut crate::leanh::LeanObject,
    mut v_x_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
    mut v_a_4274_: *mut crate::leanh::LeanObject,
    mut v_a_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4277_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(
        v_instr_4269_,
        v_x_4270_,
        v_a_4271_,
        v_a_4272_,
        v_a_4273_,
        v_a_4274_,
        v_a_4275_,
    );
    crate::leanh::lean_dec(v_a_4275_);
    crate::leanh::lean_dec_ref(v_a_4274_);
    crate::leanh::lean_dec(v_a_4273_);
    crate::leanh::lean_dec_ref(v_a_4272_);
    crate::leanh::lean_dec_ref(v_a_4271_);
    return v_res_4277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(
    mut v_x_4278_: *mut crate::leanh::LeanObject,
    mut v_as_4279_: *mut crate::leanh::LeanObject,
    mut v_sz_4280_: usize,
    mut v_i_4281_: usize,
    mut v_b_4282_: *mut crate::leanh::LeanObject,
    mut v___y_4283_: *mut crate::leanh::LeanObject,
    mut v___y_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_4278_, v_as_4279_, v_sz_4280_, v_i_4281_, v_b_4282_);
    return v___x_4289_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(
    mut v_x_4290_: *mut crate::leanh::LeanObject,
    mut v_as_4291_: *mut crate::leanh::LeanObject,
    mut v_sz_4292_: *mut crate::leanh::LeanObject,
    mut v_i_4293_: *mut crate::leanh::LeanObject,
    mut v_b_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
    mut v___y_4297_: *mut crate::leanh::LeanObject,
    mut v___y_4298_: *mut crate::leanh::LeanObject,
    mut v___y_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4301_: usize = 0;
    let mut v_i_boxed_4302_: usize = 0;
    let mut v_res_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4301_ = crate::leanh::lean_unbox_usize(v_sz_4292_);
    crate::leanh::lean_dec(v_sz_4292_);
    v_i_boxed_4302_ = crate::leanh::lean_unbox_usize(v_i_4293_);
    crate::leanh::lean_dec(v_i_4293_);
    v_res_4303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(v_x_4290_, v_as_4291_, v_sz_boxed_4301_, v_i_boxed_4302_, v_b_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
    crate::leanh::lean_dec(v___y_4299_);
    crate::leanh::lean_dec_ref(v___y_4298_);
    crate::leanh::lean_dec(v___y_4297_);
    crate::leanh::lean_dec_ref(v___y_4296_);
    crate::leanh::lean_dec_ref(v___y_4295_);
    crate::leanh::lean_dec_ref(v_as_4291_);
    crate::leanh::lean_dec(v_x_4290_);
    return v_res_4303_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(
    mut v_alt_4304_: *mut crate::leanh::LeanObject,
    mut v_f_4305_: *mut crate::leanh::LeanObject,
    mut v___y_4306_: *mut crate::leanh::LeanObject,
    mut v___y_4307_: *mut crate::leanh::LeanObject,
    mut v___y_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
    mut v___y_4310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4318_: u8 = 0;
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v_a_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4327_: u8 = 0;
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4331_: u8 = 0;
    let mut v_code_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_alt_4304_) {
                0 => {
                    v_code_4332_ = crate::leanh::lean_ctor_get(v_alt_4304_, 2);
                    crate::leanh::lean_inc_ref(v_code_4332_);
                    v___y_4313_ = v_code_4332_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_4333_ = crate::leanh::lean_ctor_get(v_alt_4304_, 1);
                    crate::leanh::lean_inc_ref(v_code_4333_);
                    v___y_4313_ = v_code_4333_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_4334_ = crate::leanh::lean_ctor_get(v_alt_4304_, 0);
                    crate::leanh::lean_inc_ref(v_code_4334_);
                    v___y_4313_ = v_code_4334_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                crate::leanh::lean_inc(v___y_4310_);
                crate::leanh::lean_inc_ref(v___y_4309_);
                crate::leanh::lean_inc(v___y_4308_);
                crate::leanh::lean_inc_ref(v___y_4307_);
                crate::leanh::lean_inc_ref(v___y_4306_);
                v___x_4314_ = crate::leanh::lean_apply_7(
                    v_f_4305_,
                    v___y_4313_,
                    v___y_4306_,
                    v___y_4307_,
                    v___y_4308_,
                    v___y_4309_,
                    v___y_4310_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4314_) == 0 {
                    v_a_4315_ = crate::leanh::lean_ctor_get(v___x_4314_, 0);
                    v_isSharedCheck_4323_ = (!crate::leanh::lean_is_exclusive(v___x_4314_)) as u8;
                    if v_isSharedCheck_4323_ == 0 {
                        v___x_4317_ = v___x_4314_;
                        v_isShared_4318_ = v_isSharedCheck_4323_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4315_);
                        crate::leanh::lean_dec(v___x_4314_);
                        v___x_4317_ = crate::leanh::lean_box(0);
                        v_isShared_4318_ = v_isSharedCheck_4323_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_alt_4304_);
                    v_a_4324_ = crate::leanh::lean_ctor_get(v___x_4314_, 0);
                    v_isSharedCheck_4331_ = (!crate::leanh::lean_is_exclusive(v___x_4314_)) as u8;
                    if v_isSharedCheck_4331_ == 0 {
                        v___x_4326_ = v___x_4314_;
                        v_isShared_4327_ = v_isSharedCheck_4331_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4324_);
                        crate::leanh::lean_dec(v___x_4314_);
                        v___x_4326_ = crate::leanh::lean_box(0);
                        v_isShared_4327_ = v_isSharedCheck_4331_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4319_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_4304_, v_a_4315_);
                if v_isShared_4318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4317_, 0, v___x_4319_);
                    v___x_4321_ = v___x_4317_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4319_);
                    v___x_4321_ = v_reuseFailAlloc_4322_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4321_;
            }
            4 => {
                if v_isShared_4327_ == 0 {
                    v___x_4329_ = v___x_4326_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
                    v___x_4329_ = v_reuseFailAlloc_4330_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(
    mut v_alt_4335_: *mut crate::leanh::LeanObject,
    mut v_f_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
    mut v___y_4342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4343_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_4335_, v_f_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
    crate::leanh::lean_dec(v___y_4341_);
    crate::leanh::lean_dec_ref(v___y_4340_);
    crate::leanh::lean_dec(v___y_4339_);
    crate::leanh::lean_dec_ref(v___y_4338_);
    crate::leanh::lean_dec_ref(v___y_4337_);
    return v_res_4343_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(
    mut v_x_4344_: *mut crate::leanh::LeanObject,
    mut v_info_4345_: *mut crate::leanh::LeanObject,
    mut v_c_4346_: *mut crate::leanh::LeanObject,
    mut v_a_4347_: *mut crate::leanh::LeanObject,
    mut v_a_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4353_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(
        v_x_4344_,
        v_info_4345_,
        v_c_4346_,
        v_a_4347_,
        v_a_4348_,
        v_a_4349_,
        v_a_4350_,
        v_a_4351_,
    );
    crate::leanh::lean_dec(v_a_4351_);
    crate::leanh::lean_dec_ref(v_a_4350_);
    crate::leanh::lean_dec(v_a_4349_);
    crate::leanh::lean_dec_ref(v_a_4348_);
    crate::leanh::lean_dec_ref(v_a_4347_);
    return v_res_4353_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(
    mut v_x_4354_: *mut crate::leanh::LeanObject,
    mut v_info_4355_: *mut crate::leanh::LeanObject,
    mut v_i_4356_: *mut crate::leanh::LeanObject,
    mut v_as_4357_: *mut crate::leanh::LeanObject,
    mut v___y_4358_: *mut crate::leanh::LeanObject,
    mut v___y_4359_: *mut crate::leanh::LeanObject,
    mut v___y_4360_: *mut crate::leanh::LeanObject,
    mut v___y_4361_: *mut crate::leanh::LeanObject,
    mut v___y_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: u8 = 0;
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: usize = 0;
    let mut v___x_4372_: usize = 0;
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4364_ = lean_array_get_size(v_as_4357_);
                v___x_4365_ = lean_nat_dec_lt(v_i_4356_, v___x_4364_);
                if v___x_4365_ == 0 {
                    crate::leanh::lean_dec(v_i_4356_);
                    crate::leanh::lean_dec_ref(v_info_4355_);
                    crate::leanh::lean_dec(v_x_4354_);
                    v___x_4366_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4366_, 0, v_as_4357_);
                    return v___x_4366_;
                } else {
                    v_a_4367_ = lean_array_fget_borrowed(v_as_4357_, v_i_4356_);
                    crate::leanh::lean_inc_ref(v_info_4355_);
                    crate::leanh::lean_inc(v_x_4354_);
                    v___x_4368_ = crate::leanh::lean_alloc_closure(
                        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed
                            as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_4368_, 0, v_x_4354_);
                    crate::leanh::lean_closure_set(v___x_4368_, 1, v_info_4355_);
                    crate::leanh::lean_inc(v_a_4367_);
                    v___x_4369_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_a_4367_, v___x_4368_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
                    if crate::leanh::lean_obj_tag(v___x_4369_) == 0 {
                        v_a_4370_ = crate::leanh::lean_ctor_get(v___x_4369_, 0);
                        crate::leanh::lean_inc(v_a_4370_);
                        crate::leanh::lean_dec_ref_known(v___x_4369_, 1);
                        v___x_4371_ = lean_ptr_addr(v_a_4367_);
                        v___x_4372_ = lean_ptr_addr(v_a_4370_);
                        v___x_4373_ = lean_usize_dec_eq(v___x_4371_, v___x_4372_);
                        if v___x_4373_ == 0 {
                            v___x_4374_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4375_ = lean_nat_add(v_i_4356_, v___x_4374_);
                            v___x_4376_ = lean_array_fset(v_as_4357_, v_i_4356_, v_a_4370_);
                            crate::leanh::lean_dec(v_i_4356_);
                            v_i_4356_ = v___x_4375_;
                            v_as_4357_ = v___x_4376_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4370_);
                            v___x_4378_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4379_ = lean_nat_add(v_i_4356_, v___x_4378_);
                            crate::leanh::lean_dec(v_i_4356_);
                            v_i_4356_ = v___x_4379_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_as_4357_);
                        crate::leanh::lean_dec(v_i_4356_);
                        crate::leanh::lean_dec_ref(v_info_4355_);
                        crate::leanh::lean_dec(v_x_4354_);
                        v_a_4381_ = crate::leanh::lean_ctor_get(v___x_4369_, 0);
                        v_isSharedCheck_4388_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4369_)) as u8;
                        if v_isSharedCheck_4388_ == 0 {
                            v___x_4383_ = v___x_4369_;
                            v_isShared_4384_ = v_isSharedCheck_4388_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4381_);
                            crate::leanh::lean_dec(v___x_4369_);
                            v___x_4383_ = crate::leanh::lean_box(0);
                            v_isShared_4384_ = v_isSharedCheck_4388_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4384_ == 0 {
                    v___x_4386_ = v___x_4383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4387_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
                    v___x_4386_ = v_reuseFailAlloc_4387_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2;
    v___x_4391_ = crate::leanh::lean_unsigned_to_nat(61);
    v___x_4392_ = crate::leanh::lean_unsigned_to_nat(247);
    v___x_4393_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0;
    v___x_4394_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4;
    v___x_4395_ = l_mkPanicMessageWithDecl(
        v___x_4394_,
        v___x_4393_,
        v___x_4392_,
        v___x_4391_,
        v___x_4390_,
    );
    return v___x_4395_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(
    mut v_x_4396_: *mut crate::leanh::LeanObject,
    mut v_info_4397_: *mut crate::leanh::LeanObject,
    mut v_c_4398_: *mut crate::leanh::LeanObject,
    mut v_a_4399_: *mut crate::leanh::LeanObject,
    mut v_a_4400_: *mut crate::leanh::LeanObject,
    mut v_a_4401_: *mut crate::leanh::LeanObject,
    mut v_a_4402_: *mut crate::leanh::LeanObject,
    mut v_a_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u8 = 0;
    let mut v_instr_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: u8 = 0;
    let mut v___x_4410_: u8 = 0;
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4415_: u8 = 0;
    let mut v___y_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: u8 = 0;
    let mut v_fst_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v___y_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4448_: usize = 0;
    let mut v___x_4449_: usize = 0;
    let mut v___x_4450_: u8 = 0;
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut v_unused_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4464_: u8 = 0;
    let mut v___y_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: usize = 0;
    let mut v___x_4473_: usize = 0;
    let mut v___x_4474_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4481_: u8 = 0;
    let mut v_unused_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v_a_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4488_: u8 = 0;
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4492_: u8 = 0;
    let mut v___x_4493_: usize = 0;
    let mut v___x_4494_: usize = 0;
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4498_: u8 = 0;
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_unused_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v_a_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v_unused_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: usize = 0;
    let mut v___x_4518_: usize = 0;
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4522_: u8 = 0;
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4526_: u8 = 0;
    let mut v_unused_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v___x_4548_: u8 = 0;
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4553_: u8 = 0;
    let mut v___y_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4563_: u8 = 0;
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4570_: u8 = 0;
    let mut v_unused_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: usize = 0;
    let mut v___x_4574_: usize = 0;
    let mut v___x_4575_: u8 = 0;
    let mut v___x_4576_: usize = 0;
    let mut v___x_4577_: usize = 0;
    let mut v___x_4578_: u8 = 0;
    let mut v_isSharedCheck_4579_: u8 = 0;
    let mut v_a_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut v_isSharedCheck_4588_: u8 = 0;
    let mut v_unused_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4594_: u8 = 0;
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4599_: u8 = 0;
    let mut v_a_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4603_: u8 = 0;
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4607_: u8 = 0;
    let mut v_cases_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4613_: u8 = 0;
    let mut v___x_4614_: u8 = 0;
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4625_: u8 = 0;
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___y_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: usize = 0;
    let mut v___x_4639_: usize = 0;
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4643_: u8 = 0;
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4650_: u8 = 0;
    let mut v_unused_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4652_: u8 = 0;
    let mut v_a_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4656_: u8 = 0;
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut v_isSharedCheck_4661_: u8 = 0;
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_a_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut v_a_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4688_: u8 = 0;
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4693_: u8 = 0;
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut v_a_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4702_: u8 = 0;
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4706_: u8 = 0;
    let mut v_fvarId_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: u8 = 0;
    let mut v_instr_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4714_: u8 = 0;
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4719_: u8 = 0;
    let mut v___y_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: u8 = 0;
    let mut v_fst_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4732_: u8 = 0;
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4737_: u8 = 0;
    let mut v___y_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: usize = 0;
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: u8 = 0;
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4757_: u8 = 0;
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4761_: u8 = 0;
    let mut v_unused_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4770_: u8 = 0;
    let mut v___y_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: usize = 0;
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: u8 = 0;
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4783_: u8 = 0;
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v_unused_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4792_: u8 = 0;
    let mut v_a_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut v___x_4801_: usize = 0;
    let mut v___x_4802_: usize = 0;
    let mut v___x_4803_: u8 = 0;
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4806_: u8 = 0;
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4810_: u8 = 0;
    let mut v_unused_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_a_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4823_: u8 = 0;
    let mut v_isSharedCheck_4824_: u8 = 0;
    let mut v_unused_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: usize = 0;
    let mut v___x_4828_: usize = 0;
    let mut v___x_4829_: u8 = 0;
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4832_: u8 = 0;
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4836_: u8 = 0;
    let mut v_unused_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4841_: u8 = 0;
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: u8 = 0;
    let mut v_instr_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: u8 = 0;
    let mut v___x_4854_: u8 = 0;
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4859_: u8 = 0;
    let mut v___y_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: u8 = 0;
    let mut v_fst_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4877_: u8 = 0;
    let mut v___y_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: u8 = 0;
    let mut v___x_4892_: usize = 0;
    let mut v___x_4893_: usize = 0;
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4897_: u8 = 0;
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4901_: u8 = 0;
    let mut v_unused_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v___y_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: usize = 0;
    let mut v___x_4921_: usize = 0;
    let mut v___x_4922_: u8 = 0;
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4925_: u8 = 0;
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4929_: u8 = 0;
    let mut v_unused_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4936_: u8 = 0;
    let mut v_a_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4940_: u8 = 0;
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4944_: u8 = 0;
    let mut v___x_4945_: usize = 0;
    let mut v___x_4946_: usize = 0;
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4950_: u8 = 0;
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4954_: u8 = 0;
    let mut v_unused_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut v_a_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4969_: u8 = 0;
    let mut v_isSharedCheck_4970_: u8 = 0;
    let mut v_unused_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: usize = 0;
    let mut v___x_4974_: usize = 0;
    let mut v___x_4975_: u8 = 0;
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_unused_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4989_: u8 = 0;
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_c_4398_) {
                    0 => {
                        v_decl_4405_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        v_k_4406_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                        v___x_4407_ = 1;
                        v_instr_4408_ =
                            l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_4407_, v_c_4398_);
                        crate::leanh::lean_inc(v_x_4396_);
                        v___x_4409_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_4408_, v_x_4396_);
                        v___x_4410_ = 1;
                        if v___x_4409_ == 0 {
                            crate::leanh::lean_inc_ref(v_k_4406_);
                            crate::leanh::lean_inc_ref(v_info_4397_);
                            crate::leanh::lean_inc(v_x_4396_);
                            v___x_4411_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_4396_, v_info_4397_, v_k_4406_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
                            if crate::leanh::lean_obj_tag(v___x_4411_) == 0 {
                                v_a_4412_ = crate::leanh::lean_ctor_get(v___x_4411_, 0);
                                v_isSharedCheck_4529_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4411_)) as u8;
                                if v_isSharedCheck_4529_ == 0 {
                                    v___x_4414_ = v___x_4411_;
                                    v_isShared_4415_ = v_isSharedCheck_4529_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4412_);
                                    crate::leanh::lean_dec(v___x_4411_);
                                    v___x_4414_ = crate::leanh::lean_box(0);
                                    v_isShared_4415_ = v_isSharedCheck_4529_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_instr_4408_);
                                crate::leanh::lean_dec_ref_known(v_c_4398_, 2);
                                crate::leanh::lean_dec_ref(v_info_4397_);
                                crate::leanh::lean_dec(v_x_4396_);
                                return v___x_4411_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_instr_4408_);
                            crate::leanh::lean_dec_ref(v_info_4397_);
                            crate::leanh::lean_dec(v_x_4396_);
                            v___x_4530_ = crate::leanh::lean_box((v___x_4410_) as usize);
                            v___x_4531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4531_, 0, v_c_4398_);
                            crate::leanh::lean_ctor_set(v___x_4531_, 1, v___x_4530_);
                            v___x_4532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4532_, 0, v___x_4531_);
                            return v___x_4532_;
                        }
                    }
                    2 => {
                        v_decl_4533_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        v_k_4534_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                        crate::leanh::lean_inc_ref(v_k_4534_);
                        crate::leanh::lean_inc_ref(v_info_4397_);
                        crate::leanh::lean_inc(v_x_4396_);
                        v___x_4535_ =
                            l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(
                                v_x_4396_,
                                v_info_4397_,
                                v_k_4534_,
                                v_a_4399_,
                                v_a_4400_,
                                v_a_4401_,
                                v_a_4402_,
                                v_a_4403_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4535_) == 0 {
                            v_a_4536_ = crate::leanh::lean_ctor_get(v___x_4535_, 0);
                            crate::leanh::lean_inc(v_a_4536_);
                            crate::leanh::lean_dec_ref_known(v___x_4535_, 1);
                            v_fst_4537_ = crate::leanh::lean_ctor_get(v_a_4536_, 0);
                            crate::leanh::lean_inc(v_fst_4537_);
                            v_snd_4538_ = crate::leanh::lean_ctor_get(v_a_4536_, 1);
                            crate::leanh::lean_inc(v_snd_4538_);
                            crate::leanh::lean_dec(v_a_4536_);
                            v_params_4539_ = crate::leanh::lean_ctor_get(v_decl_4533_, 2);
                            v_type_4540_ = crate::leanh::lean_ctor_get(v_decl_4533_, 3);
                            v_value_4541_ = crate::leanh::lean_ctor_get(v_decl_4533_, 4);
                            crate::leanh::lean_inc_ref(v_value_4541_);
                            v___x_4542_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_4396_, v_info_4397_, v_value_4541_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
                            if crate::leanh::lean_obj_tag(v___x_4542_) == 0 {
                                v_a_4543_ = crate::leanh::lean_ctor_get(v___x_4542_, 0);
                                crate::leanh::lean_inc(v_a_4543_);
                                crate::leanh::lean_dec_ref_known(v___x_4542_, 1);
                                v_fst_4544_ = crate::leanh::lean_ctor_get(v_a_4543_, 0);
                                v_isSharedCheck_4588_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_4543_)) as u8;
                                if v_isSharedCheck_4588_ == 0 {
                                    v_unused_4589_ = crate::leanh::lean_ctor_get(v_a_4543_, 1);
                                    crate::leanh::lean_dec(v_unused_4589_);
                                    v___x_4546_ = v_a_4543_;
                                    v_isShared_4547_ = v_isSharedCheck_4588_;
                                    state = 25;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_fst_4544_);
                                    crate::leanh::lean_dec(v_a_4543_);
                                    v___x_4546_ = crate::leanh::lean_box(0);
                                    v_isShared_4547_ = v_isSharedCheck_4588_;
                                    state = 25;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_4538_);
                                crate::leanh::lean_dec(v_fst_4537_);
                                crate::leanh::lean_dec_ref_known(v_c_4398_, 2);
                                return v___x_4542_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_4398_, 2);
                            crate::leanh::lean_dec_ref(v_info_4397_);
                            crate::leanh::lean_dec(v_x_4396_);
                            return v___x_4535_;
                        }
                    }
                    3 => {
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_inc_ref(v_c_4398_);
                        v___x_4590_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(
                            v_c_4398_, v_x_4396_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4590_) == 0 {
                            v_a_4591_ = crate::leanh::lean_ctor_get(v___x_4590_, 0);
                            v_isSharedCheck_4599_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4590_)) as u8;
                            if v_isSharedCheck_4599_ == 0 {
                                v___x_4593_ = v___x_4590_;
                                v_isShared_4594_ = v_isSharedCheck_4599_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4591_);
                                crate::leanh::lean_dec(v___x_4590_);
                                v___x_4593_ = crate::leanh::lean_box(0);
                                v_isShared_4594_ = v_isSharedCheck_4599_;
                                state = 35;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_4398_, 2);
                            v_a_4600_ = crate::leanh::lean_ctor_get(v___x_4590_, 0);
                            v_isSharedCheck_4607_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4590_)) as u8;
                            if v_isSharedCheck_4607_ == 0 {
                                v___x_4602_ = v___x_4590_;
                                v_isShared_4603_ = v_isSharedCheck_4607_;
                                state = 37;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4600_);
                                crate::leanh::lean_dec(v___x_4590_);
                                v___x_4602_ = crate::leanh::lean_box(0);
                                v_isShared_4603_ = v_isSharedCheck_4607_;
                                state = 37;
                                continue;
                            }
                        }
                    }
                    4 => {
                        v_cases_4608_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        crate::leanh::lean_inc_ref(v_cases_4608_);
                        crate::leanh::lean_inc(v_x_4396_);
                        crate::leanh::lean_inc_ref(v_c_4398_);
                        v___x_4609_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(
                            v_c_4398_, v_x_4396_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4609_) == 0 {
                            v_a_4610_ = crate::leanh::lean_ctor_get(v___x_4609_, 0);
                            v_isSharedCheck_4662_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4609_)) as u8;
                            if v_isSharedCheck_4662_ == 0 {
                                v___x_4612_ = v___x_4609_;
                                v_isShared_4613_ = v_isSharedCheck_4662_;
                                state = 39;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4610_);
                                crate::leanh::lean_dec(v___x_4609_);
                                v___x_4612_ = crate::leanh::lean_box(0);
                                v_isShared_4613_ = v_isSharedCheck_4662_;
                                state = 39;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_4398_, 1);
                            crate::leanh::lean_dec_ref(v_cases_4608_);
                            crate::leanh::lean_dec_ref(v_info_4397_);
                            crate::leanh::lean_dec(v_x_4396_);
                            v_a_4663_ = crate::leanh::lean_ctor_get(v___x_4609_, 0);
                            v_isSharedCheck_4670_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4609_)) as u8;
                            if v_isSharedCheck_4670_ == 0 {
                                v___x_4665_ = v___x_4609_;
                                v_isShared_4666_ = v_isSharedCheck_4670_;
                                state = 50;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4663_);
                                crate::leanh::lean_dec(v___x_4609_);
                                v___x_4665_ = crate::leanh::lean_box(0);
                                v_isShared_4666_ = v_isSharedCheck_4670_;
                                state = 50;
                                continue;
                            }
                        }
                    }
                    5 => {
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_inc_ref(v_c_4398_);
                        v___x_4671_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(
                            v_c_4398_, v_x_4396_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4671_) == 0 {
                            v_a_4672_ = crate::leanh::lean_ctor_get(v___x_4671_, 0);
                            v_isSharedCheck_4680_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4671_)) as u8;
                            if v_isSharedCheck_4680_ == 0 {
                                v___x_4674_ = v___x_4671_;
                                v_isShared_4675_ = v_isSharedCheck_4680_;
                                state = 52;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4672_);
                                crate::leanh::lean_dec(v___x_4671_);
                                v___x_4674_ = crate::leanh::lean_box(0);
                                v_isShared_4675_ = v_isSharedCheck_4680_;
                                state = 52;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_4398_, 1);
                            v_a_4681_ = crate::leanh::lean_ctor_get(v___x_4671_, 0);
                            v_isSharedCheck_4688_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4671_)) as u8;
                            if v_isSharedCheck_4688_ == 0 {
                                v___x_4683_ = v___x_4671_;
                                v_isShared_4684_ = v_isSharedCheck_4688_;
                                state = 54;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4681_);
                                crate::leanh::lean_dec(v___x_4671_);
                                v___x_4683_ = crate::leanh::lean_box(0);
                                v_isShared_4684_ = v_isSharedCheck_4688_;
                                state = 54;
                                continue;
                            }
                        }
                    }
                    6 => {
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_inc_ref(v_c_4398_);
                        v___x_4689_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(
                            v_c_4398_, v_x_4396_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4689_) == 0 {
                            v_a_4690_ = crate::leanh::lean_ctor_get(v___x_4689_, 0);
                            v_isSharedCheck_4698_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4689_)) as u8;
                            if v_isSharedCheck_4698_ == 0 {
                                v___x_4692_ = v___x_4689_;
                                v_isShared_4693_ = v_isSharedCheck_4698_;
                                state = 56;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4690_);
                                crate::leanh::lean_dec(v___x_4689_);
                                v___x_4692_ = crate::leanh::lean_box(0);
                                v_isShared_4693_ = v_isSharedCheck_4698_;
                                state = 56;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_4398_, 1);
                            v_a_4699_ = crate::leanh::lean_ctor_get(v___x_4689_, 0);
                            v_isSharedCheck_4706_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4689_)) as u8;
                            if v_isSharedCheck_4706_ == 0 {
                                v___x_4701_ = v___x_4689_;
                                v_isShared_4702_ = v_isSharedCheck_4706_;
                                state = 58;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4699_);
                                crate::leanh::lean_dec(v___x_4689_);
                                v___x_4701_ = crate::leanh::lean_box(0);
                                v_isShared_4702_ = v_isSharedCheck_4706_;
                                state = 58;
                                continue;
                            }
                        }
                    }
                    8 => {
                        v_fvarId_4707_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        v_i_4708_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                        v_y_4709_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                        v_k_4710_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                        v___x_4711_ = 1;
                        v_instr_4712_ =
                            l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_4711_, v_c_4398_);
                        crate::leanh::lean_inc(v_x_4396_);
                        v___x_4713_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_4712_, v_x_4396_);
                        v___x_4714_ = 1;
                        if v___x_4713_ == 0 {
                            crate::leanh::lean_inc_ref(v_k_4710_);
                            crate::leanh::lean_inc_ref(v_info_4397_);
                            crate::leanh::lean_inc(v_x_4396_);
                            v___x_4715_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_4396_, v_info_4397_, v_k_4710_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
                            if crate::leanh::lean_obj_tag(v___x_4715_) == 0 {
                                v_a_4716_ = crate::leanh::lean_ctor_get(v___x_4715_, 0);
                                v_isSharedCheck_4841_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4715_)) as u8;
                                if v_isSharedCheck_4841_ == 0 {
                                    v___x_4718_ = v___x_4715_;
                                    v_isShared_4719_ = v_isSharedCheck_4841_;
                                    state = 60;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4716_);
                                    crate::leanh::lean_dec(v___x_4715_);
                                    v___x_4718_ = crate::leanh::lean_box(0);
                                    v_isShared_4719_ = v_isSharedCheck_4841_;
                                    state = 60;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_instr_4712_);
                                crate::leanh::lean_dec_ref_known(v_c_4398_, 4);
                                crate::leanh::lean_dec_ref(v_info_4397_);
                                crate::leanh::lean_dec(v_x_4396_);
                                return v___x_4715_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_instr_4712_);
                            crate::leanh::lean_dec_ref(v_info_4397_);
                            crate::leanh::lean_dec(v_x_4396_);
                            v___x_4842_ = crate::leanh::lean_box((v___x_4714_) as usize);
                            v___x_4843_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4843_, 0, v_c_4398_);
                            crate::leanh::lean_ctor_set(v___x_4843_, 1, v___x_4842_);
                            v___x_4844_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4844_, 0, v___x_4843_);
                            return v___x_4844_;
                        }
                    }
                    9 => {
                        v_fvarId_4845_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        v_i_4846_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                        v_offset_4847_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                        v_y_4848_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                        v_ty_4849_ = crate::leanh::lean_ctor_get(v_c_4398_, 4);
                        v_k_4850_ = crate::leanh::lean_ctor_get(v_c_4398_, 5);
                        v___x_4851_ = 1;
                        v_instr_4852_ =
                            l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_4851_, v_c_4398_);
                        crate::leanh::lean_inc(v_x_4396_);
                        v___x_4853_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_4852_, v_x_4396_);
                        v___x_4854_ = 1;
                        if v___x_4853_ == 0 {
                            crate::leanh::lean_inc_ref(v_k_4850_);
                            crate::leanh::lean_inc_ref(v_info_4397_);
                            crate::leanh::lean_inc(v_x_4396_);
                            v___x_4855_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_4396_, v_info_4397_, v_k_4850_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
                            if crate::leanh::lean_obj_tag(v___x_4855_) == 0 {
                                v_a_4856_ = crate::leanh::lean_ctor_get(v___x_4855_, 0);
                                v_isSharedCheck_4989_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4855_)) as u8;
                                if v_isSharedCheck_4989_ == 0 {
                                    v___x_4858_ = v___x_4855_;
                                    v_isShared_4859_ = v_isSharedCheck_4989_;
                                    state = 84;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4856_);
                                    crate::leanh::lean_dec(v___x_4855_);
                                    v___x_4858_ = crate::leanh::lean_box(0);
                                    v_isShared_4859_ = v_isSharedCheck_4989_;
                                    state = 84;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_instr_4852_);
                                crate::leanh::lean_dec_ref_known(v_c_4398_, 6);
                                crate::leanh::lean_dec_ref(v_info_4397_);
                                crate::leanh::lean_dec(v_x_4396_);
                                return v___x_4855_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_instr_4852_);
                            crate::leanh::lean_dec_ref(v_info_4397_);
                            crate::leanh::lean_dec(v_x_4396_);
                            v___x_4990_ = crate::leanh::lean_box((v___x_4854_) as usize);
                            v___x_4991_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4991_, 0, v_c_4398_);
                            crate::leanh::lean_ctor_set(v___x_4991_, 1, v___x_4990_);
                            v___x_4992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4992_, 0, v___x_4991_);
                            return v___x_4992_;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_c_4398_);
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_dec(v_x_4396_);
                        v___x_4993_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1);
                        v___x_4994_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_4993_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
                        return v___x_4994_;
                    }
                }
            }
            1 => {
                v_snd_4423_ = crate::leanh::lean_ctor_get(v_a_4412_, 1);
                v___x_4424_ = (crate::leanh::lean_unbox(v_snd_4423_) as u8);
                if v___x_4424_ == 0 {
                    crate::leanh::lean_inc(v_snd_4423_);
                    crate::leanh::lean_del_object(v___x_4414_);
                    v_fst_4425_ = crate::leanh::lean_ctor_get(v_a_4412_, 0);
                    v_isSharedCheck_4514_ = (!crate::leanh::lean_is_exclusive(v_a_4412_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v_unused_4515_ = crate::leanh::lean_ctor_get(v_a_4412_, 1);
                        crate::leanh::lean_dec(v_unused_4515_);
                        v___x_4427_ = v_a_4412_;
                        v_isShared_4428_ = v_isSharedCheck_4514_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4425_);
                        crate::leanh::lean_dec(v_a_4412_);
                        v___x_4427_ = crate::leanh::lean_box(0);
                        v_isShared_4428_ = v_isSharedCheck_4514_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_instr_4408_);
                    crate::leanh::lean_dec_ref(v_info_4397_);
                    crate::leanh::lean_dec(v_x_4396_);
                    v_fst_4516_ = crate::leanh::lean_ctor_get(v_a_4412_, 0);
                    crate::leanh::lean_inc(v_fst_4516_);
                    crate::leanh::lean_dec(v_a_4412_);
                    v___x_4517_ = lean_ptr_addr(v_k_4406_);
                    v___x_4518_ = lean_ptr_addr(v_fst_4516_);
                    v___x_4519_ = lean_usize_dec_eq(v___x_4517_, v___x_4518_);
                    if v___x_4519_ == 0 {
                        crate::leanh::lean_inc_ref(v_decl_4405_);
                        v_isSharedCheck_4526_ = (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                        if v_isSharedCheck_4526_ == 0 {
                            v_unused_4527_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                            crate::leanh::lean_dec(v_unused_4527_);
                            v_unused_4528_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                            crate::leanh::lean_dec(v_unused_4528_);
                            v___x_4521_ = v_c_4398_;
                            v_isShared_4522_ = v_isSharedCheck_4526_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_c_4398_);
                            v___x_4521_ = crate::leanh::lean_box(0);
                            v_isShared_4522_ = v_isSharedCheck_4526_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_4516_);
                        v___y_4417_ = v_c_4398_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4418_ = crate::leanh::lean_box((v___x_4410_) as usize);
                v___x_4419_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4419_, 0, v___y_4417_);
                crate::leanh::lean_ctor_set(v___x_4419_, 1, v___x_4418_);
                if v_isShared_4415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4414_, 0, v___x_4419_);
                    v___x_4421_ = v___x_4414_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
                    v___x_4421_ = v_reuseFailAlloc_4422_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4421_;
            }
            4 => {
                crate::leanh::lean_inc(v_x_4396_);
                v___x_4429_ =
                    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(
                        v_instr_4408_,
                        v_x_4396_,
                        v_a_4399_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4429_) == 0 {
                    v_a_4430_ = crate::leanh::lean_ctor_get(v___x_4429_, 0);
                    v_isSharedCheck_4505_ = (!crate::leanh::lean_is_exclusive(v___x_4429_)) as u8;
                    if v_isSharedCheck_4505_ == 0 {
                        v___x_4432_ = v___x_4429_;
                        v_isShared_4433_ = v_isSharedCheck_4505_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4430_);
                        crate::leanh::lean_dec(v___x_4429_);
                        v___x_4432_ = crate::leanh::lean_box(0);
                        v_isShared_4433_ = v_isSharedCheck_4505_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4427_);
                    crate::leanh::lean_dec(v_fst_4425_);
                    crate::leanh::lean_dec(v_snd_4423_);
                    crate::leanh::lean_dec_ref_known(v_c_4398_, 2);
                    crate::leanh::lean_dec_ref(v_info_4397_);
                    crate::leanh::lean_dec(v_x_4396_);
                    v_a_4506_ = crate::leanh::lean_ctor_get(v___x_4429_, 0);
                    v_isSharedCheck_4513_ = (!crate::leanh::lean_is_exclusive(v___x_4429_)) as u8;
                    if v_isSharedCheck_4513_ == 0 {
                        v___x_4508_ = v___x_4429_;
                        v_isShared_4509_ = v_isSharedCheck_4513_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4506_);
                        crate::leanh::lean_dec(v___x_4429_);
                        v___x_4508_ = crate::leanh::lean_box(0);
                        v_isShared_4509_ = v_isSharedCheck_4513_;
                        state = 21;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4447_ = (crate::leanh::lean_unbox(v_a_4430_) as u8);
                crate::leanh::lean_dec(v_a_4430_);
                match v___x_4447_ {
                    0 => {
                        crate::leanh::lean_del_object(v___x_4432_);
                        crate::leanh::lean_del_object(v___x_4427_);
                        crate::leanh::lean_dec(v_snd_4423_);
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_dec(v_x_4396_);
                        v___x_4448_ = lean_ptr_addr(v_k_4406_);
                        v___x_4449_ = lean_ptr_addr(v_fst_4425_);
                        v___x_4450_ = lean_usize_dec_eq(v___x_4448_, v___x_4449_);
                        if v___x_4450_ == 0 {
                            crate::leanh::lean_inc_ref(v_decl_4405_);
                            v_isSharedCheck_4457_ =
                                (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                            if v_isSharedCheck_4457_ == 0 {
                                v_unused_4458_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                                crate::leanh::lean_dec(v_unused_4458_);
                                v_unused_4459_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                                crate::leanh::lean_dec(v_unused_4459_);
                                v___x_4452_ = v_c_4398_;
                                v_isShared_4453_ = v_isSharedCheck_4457_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_c_4398_);
                                v___x_4452_ = crate::leanh::lean_box(0);
                                v_isShared_4453_ = v_isSharedCheck_4457_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_4425_);
                            v___y_4443_ = v_c_4398_;
                            state = 9;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_4432_);
                        crate::leanh::lean_del_object(v___x_4427_);
                        crate::leanh::lean_dec(v_snd_4423_);
                        v___x_4460_ =
                            l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(
                                v_x_4396_,
                                v_info_4397_,
                                v_fst_4425_,
                                v_a_4399_,
                                v_a_4400_,
                                v_a_4401_,
                                v_a_4402_,
                                v_a_4403_,
                            );
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        if crate::leanh::lean_obj_tag(v___x_4460_) == 0 {
                            v_a_4461_ = crate::leanh::lean_ctor_get(v___x_4460_, 0);
                            v_isSharedCheck_4484_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4460_)) as u8;
                            if v_isSharedCheck_4484_ == 0 {
                                v___x_4463_ = v___x_4460_;
                                v_isShared_4464_ = v_isSharedCheck_4484_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4461_);
                                crate::leanh::lean_dec(v___x_4460_);
                                v___x_4463_ = crate::leanh::lean_box(0);
                                v_isShared_4464_ = v_isSharedCheck_4484_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_4398_, 2);
                            v_a_4485_ = crate::leanh::lean_ctor_get(v___x_4460_, 0);
                            v_isSharedCheck_4492_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4460_)) as u8;
                            if v_isSharedCheck_4492_ == 0 {
                                v___x_4487_ = v___x_4460_;
                                v_isShared_4488_ = v_isSharedCheck_4492_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4485_);
                                crate::leanh::lean_dec(v___x_4460_);
                                v___x_4487_ = crate::leanh::lean_box(0);
                                v_isShared_4488_ = v_isSharedCheck_4492_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_dec(v_x_4396_);
                        v___x_4493_ = lean_ptr_addr(v_k_4406_);
                        v___x_4494_ = lean_ptr_addr(v_fst_4425_);
                        v___x_4495_ = lean_usize_dec_eq(v___x_4493_, v___x_4494_);
                        if v___x_4495_ == 0 {
                            crate::leanh::lean_inc_ref(v_decl_4405_);
                            v_isSharedCheck_4502_ =
                                (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                            if v_isSharedCheck_4502_ == 0 {
                                v_unused_4503_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                                crate::leanh::lean_dec(v_unused_4503_);
                                v_unused_4504_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                                crate::leanh::lean_dec(v_unused_4504_);
                                v___x_4497_ = v_c_4398_;
                                v_isShared_4498_ = v_isSharedCheck_4502_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_c_4398_);
                                v___x_4497_ = crate::leanh::lean_box(0);
                                v_isShared_4498_ = v_isSharedCheck_4502_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_4425_);
                            v___y_4435_ = v_c_4398_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_4428_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4427_, 0, v___y_4435_);
                    v___x_4437_ = v___x_4427_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___y_4435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_snd_4423_);
                    v___x_4437_ = v_reuseFailAlloc_4441_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4432_, 0, v___x_4437_);
                    v___x_4439_ = v___x_4432_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
                    v___x_4439_ = v_reuseFailAlloc_4440_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4439_;
            }
            9 => {
                v___x_4444_ = crate::leanh::lean_box((v___x_4410_) as usize);
                v___x_4445_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4445_, 0, v___y_4443_);
                crate::leanh::lean_ctor_set(v___x_4445_, 1, v___x_4444_);
                v___x_4446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4446_, 0, v___x_4445_);
                return v___x_4446_;
            }
            10 => {
                if v_isShared_4453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4452_, 1, v_fst_4425_);
                    v___x_4455_ = v___x_4452_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4456_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_decl_4405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_fst_4425_);
                    v___x_4455_ = v_reuseFailAlloc_4456_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_4443_ = v___x_4455_;
                state = 9;
                continue;
            }
            12 => {
                v___x_4472_ = lean_ptr_addr(v_k_4406_);
                v___x_4473_ = lean_ptr_addr(v_a_4461_);
                v___x_4474_ = lean_usize_dec_eq(v___x_4472_, v___x_4473_);
                if v___x_4474_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_4405_);
                    v_isSharedCheck_4481_ = (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                    if v_isSharedCheck_4481_ == 0 {
                        v_unused_4482_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                        crate::leanh::lean_dec(v_unused_4482_);
                        v_unused_4483_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        crate::leanh::lean_dec(v_unused_4483_);
                        v___x_4476_ = v_c_4398_;
                        v_isShared_4477_ = v_isSharedCheck_4481_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_4398_);
                        v___x_4476_ = crate::leanh::lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4481_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4461_);
                    v___y_4466_ = v_c_4398_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4467_ = crate::leanh::lean_box((v___x_4410_) as usize);
                v___x_4468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4468_, 0, v___y_4466_);
                crate::leanh::lean_ctor_set(v___x_4468_, 1, v___x_4467_);
                if v_isShared_4464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4463_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4463_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4470_;
            }
            15 => {
                if v_isShared_4477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4476_, 1, v_a_4461_);
                    v___x_4479_ = v___x_4476_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4480_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_decl_4405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_a_4461_);
                    v___x_4479_ = v_reuseFailAlloc_4480_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_4466_ = v___x_4479_;
                state = 13;
                continue;
            }
            17 => {
                if v_isShared_4488_ == 0 {
                    v___x_4490_ = v___x_4487_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
                    v___x_4490_ = v_reuseFailAlloc_4491_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4490_;
            }
            19 => {
                if v_isShared_4498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4497_, 1, v_fst_4425_);
                    v___x_4500_ = v___x_4497_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_decl_4405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 1, v_fst_4425_);
                    v___x_4500_ = v_reuseFailAlloc_4501_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___y_4435_ = v___x_4500_;
                state = 6;
                continue;
            }
            21 => {
                if v_isShared_4509_ == 0 {
                    v___x_4511_ = v___x_4508_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
                    v___x_4511_ = v_reuseFailAlloc_4512_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4511_;
            }
            23 => {
                if v_isShared_4522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4521_, 1, v_fst_4516_);
                    v___x_4524_ = v___x_4521_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_decl_4405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_fst_4516_);
                    v___x_4524_ = v_reuseFailAlloc_4525_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___y_4417_ = v___x_4524_;
                state = 2;
                continue;
            }
            25 => {
                v___x_4548_ = 1;
                crate::leanh::lean_inc_ref(v_params_4539_);
                crate::leanh::lean_inc_ref(v_type_4540_);
                crate::leanh::lean_inc_ref(v_decl_4533_);
                v___x_4549_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4548_, v_decl_4533_, v_type_4540_, v_params_4539_, v_fst_4544_, v_a_4401_);
                if crate::leanh::lean_obj_tag(v___x_4549_) == 0 {
                    v_a_4550_ = crate::leanh::lean_ctor_get(v___x_4549_, 0);
                    v_isSharedCheck_4579_ = (!crate::leanh::lean_is_exclusive(v___x_4549_)) as u8;
                    if v_isSharedCheck_4579_ == 0 {
                        v___x_4552_ = v___x_4549_;
                        v_isShared_4553_ = v_isSharedCheck_4579_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4550_);
                        crate::leanh::lean_dec(v___x_4549_);
                        v___x_4552_ = crate::leanh::lean_box(0);
                        v_isShared_4553_ = v_isSharedCheck_4579_;
                        state = 26;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4546_);
                    crate::leanh::lean_dec(v_snd_4538_);
                    crate::leanh::lean_dec(v_fst_4537_);
                    crate::leanh::lean_dec_ref_known(v_c_4398_, 2);
                    v_a_4580_ = crate::leanh::lean_ctor_get(v___x_4549_, 0);
                    v_isSharedCheck_4587_ = (!crate::leanh::lean_is_exclusive(v___x_4549_)) as u8;
                    if v_isSharedCheck_4587_ == 0 {
                        v___x_4582_ = v___x_4549_;
                        v_isShared_4583_ = v_isSharedCheck_4587_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4580_);
                        crate::leanh::lean_dec(v___x_4549_);
                        v___x_4582_ = crate::leanh::lean_box(0);
                        v_isShared_4583_ = v_isSharedCheck_4587_;
                        state = 33;
                        continue;
                    }
                }
            }
            26 => {
                v___x_4573_ = lean_ptr_addr(v_k_4534_);
                v___x_4574_ = lean_ptr_addr(v_fst_4537_);
                v___x_4575_ = lean_usize_dec_eq(v___x_4573_, v___x_4574_);
                if v___x_4575_ == 0 {
                    v___y_4563_ = v___x_4575_;
                    state = 30;
                    continue;
                } else {
                    v___x_4576_ = lean_ptr_addr(v_decl_4533_);
                    v___x_4577_ = lean_ptr_addr(v_a_4550_);
                    v___x_4578_ = lean_usize_dec_eq(v___x_4576_, v___x_4577_);
                    v___y_4563_ = v___x_4578_;
                    state = 30;
                    continue;
                }
            }
            27 => {
                if v_isShared_4547_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4546_, 1, v_snd_4538_);
                    crate::leanh::lean_ctor_set(v___x_4546_, 0, v___y_4555_);
                    v___x_4557_ = v___x_4546_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___y_4555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_snd_4538_);
                    v___x_4557_ = v_reuseFailAlloc_4561_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_4553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4552_, 0, v___x_4557_);
                    v___x_4559_ = v___x_4552_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4560_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
                    v___x_4559_ = v_reuseFailAlloc_4560_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4559_;
            }
            30 => {
                if v___y_4563_ == 0 {
                    v_isSharedCheck_4570_ = (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                    if v_isSharedCheck_4570_ == 0 {
                        v_unused_4571_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                        crate::leanh::lean_dec(v_unused_4571_);
                        v_unused_4572_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        crate::leanh::lean_dec(v_unused_4572_);
                        v___x_4565_ = v_c_4398_;
                        v_isShared_4566_ = v_isSharedCheck_4570_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_4398_);
                        v___x_4565_ = crate::leanh::lean_box(0);
                        v_isShared_4566_ = v_isSharedCheck_4570_;
                        state = 31;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4550_);
                    crate::leanh::lean_dec(v_fst_4537_);
                    v___y_4555_ = v_c_4398_;
                    state = 27;
                    continue;
                }
            }
            31 => {
                if v_isShared_4566_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4565_, 1, v_fst_4537_);
                    crate::leanh::lean_ctor_set(v___x_4565_, 0, v_a_4550_);
                    v___x_4568_ = v___x_4565_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4569_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4569_, 1, v_fst_4537_);
                    v___x_4568_ = v_reuseFailAlloc_4569_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___y_4555_ = v___x_4568_;
                state = 27;
                continue;
            }
            33 => {
                if v_isShared_4583_ == 0 {
                    v___x_4585_ = v___x_4582_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
                    v___x_4585_ = v_reuseFailAlloc_4586_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4585_;
            }
            35 => {
                v___x_4595_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4595_, 0, v_c_4398_);
                crate::leanh::lean_ctor_set(v___x_4595_, 1, v_a_4591_);
                if v_isShared_4594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4593_, 0, v___x_4595_);
                    v___x_4597_ = v___x_4593_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4595_);
                    v___x_4597_ = v_reuseFailAlloc_4598_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4597_;
            }
            37 => {
                if v_isShared_4603_ == 0 {
                    v___x_4605_ = v___x_4602_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
                    v___x_4605_ = v_reuseFailAlloc_4606_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4605_;
            }
            39 => {
                v___x_4614_ = (crate::leanh::lean_unbox(v_a_4610_) as u8);
                if v___x_4614_ == 0 {
                    crate::leanh::lean_dec_ref(v_cases_4608_);
                    crate::leanh::lean_dec_ref(v_info_4397_);
                    crate::leanh::lean_dec(v_x_4396_);
                    v___x_4615_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4615_, 0, v_c_4398_);
                    crate::leanh::lean_ctor_set(v___x_4615_, 1, v_a_4610_);
                    if v_isShared_4613_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4612_, 0, v___x_4615_);
                        v___x_4617_ = v___x_4612_;
                        state = 40;
                        continue;
                    } else {
                        v_reuseFailAlloc_4618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
                        v___x_4617_ = v_reuseFailAlloc_4618_;
                        state = 40;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4612_);
                    v_typeName_4619_ = crate::leanh::lean_ctor_get(v_cases_4608_, 0);
                    v_resultType_4620_ = crate::leanh::lean_ctor_get(v_cases_4608_, 1);
                    v_discr_4621_ = crate::leanh::lean_ctor_get(v_cases_4608_, 2);
                    v_alts_4622_ = crate::leanh::lean_ctor_get(v_cases_4608_, 3);
                    v_isSharedCheck_4661_ = (!crate::leanh::lean_is_exclusive(v_cases_4608_)) as u8;
                    if v_isSharedCheck_4661_ == 0 {
                        v___x_4624_ = v_cases_4608_;
                        v_isShared_4625_ = v_isSharedCheck_4661_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_4622_);
                        crate::leanh::lean_inc(v_discr_4621_);
                        crate::leanh::lean_inc(v_resultType_4620_);
                        crate::leanh::lean_inc(v_typeName_4619_);
                        crate::leanh::lean_dec(v_cases_4608_);
                        v___x_4624_ = crate::leanh::lean_box(0);
                        v_isShared_4625_ = v_isSharedCheck_4661_;
                        state = 41;
                        continue;
                    }
                }
            }
            40 => {
                return v___x_4617_;
            }
            41 => {
                v___x_4626_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_4622_);
                v___x_4627_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_4396_, v_info_4397_, v___x_4626_, v_alts_4622_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
                if crate::leanh::lean_obj_tag(v___x_4627_) == 0 {
                    v_a_4628_ = crate::leanh::lean_ctor_get(v___x_4627_, 0);
                    v_isSharedCheck_4652_ = (!crate::leanh::lean_is_exclusive(v___x_4627_)) as u8;
                    if v_isSharedCheck_4652_ == 0 {
                        v___x_4630_ = v___x_4627_;
                        v_isShared_4631_ = v_isSharedCheck_4652_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4628_);
                        crate::leanh::lean_dec(v___x_4627_);
                        v___x_4630_ = crate::leanh::lean_box(0);
                        v_isShared_4631_ = v_isSharedCheck_4652_;
                        state = 42;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4624_);
                    crate::leanh::lean_dec_ref(v_alts_4622_);
                    crate::leanh::lean_dec(v_discr_4621_);
                    crate::leanh::lean_dec_ref(v_resultType_4620_);
                    crate::leanh::lean_dec(v_typeName_4619_);
                    crate::leanh::lean_dec(v_a_4610_);
                    crate::leanh::lean_dec_ref_known(v_c_4398_, 1);
                    v_a_4653_ = crate::leanh::lean_ctor_get(v___x_4627_, 0);
                    v_isSharedCheck_4660_ = (!crate::leanh::lean_is_exclusive(v___x_4627_)) as u8;
                    if v_isSharedCheck_4660_ == 0 {
                        v___x_4655_ = v___x_4627_;
                        v_isShared_4656_ = v_isSharedCheck_4660_;
                        state = 48;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4653_);
                        crate::leanh::lean_dec(v___x_4627_);
                        v___x_4655_ = crate::leanh::lean_box(0);
                        v_isShared_4656_ = v_isSharedCheck_4660_;
                        state = 48;
                        continue;
                    }
                }
            }
            42 => {
                v___x_4638_ = lean_ptr_addr(v_alts_4622_);
                crate::leanh::lean_dec_ref(v_alts_4622_);
                v___x_4639_ = lean_ptr_addr(v_a_4628_);
                v___x_4640_ = lean_usize_dec_eq(v___x_4638_, v___x_4639_);
                if v___x_4640_ == 0 {
                    v_isSharedCheck_4650_ = (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                    if v_isSharedCheck_4650_ == 0 {
                        v_unused_4651_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        crate::leanh::lean_dec(v_unused_4651_);
                        v___x_4642_ = v_c_4398_;
                        v_isShared_4643_ = v_isSharedCheck_4650_;
                        state = 45;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_4398_);
                        v___x_4642_ = crate::leanh::lean_box(0);
                        v_isShared_4643_ = v_isSharedCheck_4650_;
                        state = 45;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4628_);
                    crate::leanh::lean_del_object(v___x_4624_);
                    crate::leanh::lean_dec(v_discr_4621_);
                    crate::leanh::lean_dec_ref(v_resultType_4620_);
                    crate::leanh::lean_dec(v_typeName_4619_);
                    v___y_4633_ = v_c_4398_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_4634_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4634_, 0, v___y_4633_);
                crate::leanh::lean_ctor_set(v___x_4634_, 1, v_a_4610_);
                if v_isShared_4631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4630_, 0, v___x_4634_);
                    v___x_4636_ = v___x_4630_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
                    v___x_4636_ = v_reuseFailAlloc_4637_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4636_;
            }
            45 => {
                if v_isShared_4625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4624_, 3, v_a_4628_);
                    v___x_4645_ = v___x_4624_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4649_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_typeName_4619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_resultType_4620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 2, v_discr_4621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 3, v_a_4628_);
                    v___x_4645_ = v_reuseFailAlloc_4649_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_4643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4642_, 0, v___x_4645_);
                    v___x_4647_ = v___x_4642_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4648_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
                    v___x_4647_ = v_reuseFailAlloc_4648_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___y_4633_ = v___x_4647_;
                state = 43;
                continue;
            }
            48 => {
                if v_isShared_4656_ == 0 {
                    v___x_4658_ = v___x_4655_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
                    v___x_4658_ = v_reuseFailAlloc_4659_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_4658_;
            }
            50 => {
                if v_isShared_4666_ == 0 {
                    v___x_4668_ = v___x_4665_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
                    v___x_4668_ = v_reuseFailAlloc_4669_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_4668_;
            }
            52 => {
                v___x_4676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4676_, 0, v_c_4398_);
                crate::leanh::lean_ctor_set(v___x_4676_, 1, v_a_4672_);
                if v_isShared_4675_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4674_, 0, v___x_4676_);
                    v___x_4678_ = v___x_4674_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4679_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
                    v___x_4678_ = v_reuseFailAlloc_4679_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_4678_;
            }
            54 => {
                if v_isShared_4684_ == 0 {
                    v___x_4686_ = v___x_4683_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_4687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
                    v___x_4686_ = v_reuseFailAlloc_4687_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_4686_;
            }
            56 => {
                v___x_4694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4694_, 0, v_c_4398_);
                crate::leanh::lean_ctor_set(v___x_4694_, 1, v_a_4690_);
                if v_isShared_4693_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4692_, 0, v___x_4694_);
                    v___x_4696_ = v___x_4692_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4694_);
                    v___x_4696_ = v_reuseFailAlloc_4697_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_4696_;
            }
            58 => {
                if v_isShared_4702_ == 0 {
                    v___x_4704_ = v___x_4701_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_4705_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
                    v___x_4704_ = v_reuseFailAlloc_4705_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_4704_;
            }
            60 => {
                v_snd_4727_ = crate::leanh::lean_ctor_get(v_a_4716_, 1);
                v___x_4728_ = (crate::leanh::lean_unbox(v_snd_4727_) as u8);
                if v___x_4728_ == 0 {
                    crate::leanh::lean_inc(v_snd_4727_);
                    crate::leanh::lean_del_object(v___x_4718_);
                    v_fst_4729_ = crate::leanh::lean_ctor_get(v_a_4716_, 0);
                    v_isSharedCheck_4824_ = (!crate::leanh::lean_is_exclusive(v_a_4716_)) as u8;
                    if v_isSharedCheck_4824_ == 0 {
                        v_unused_4825_ = crate::leanh::lean_ctor_get(v_a_4716_, 1);
                        crate::leanh::lean_dec(v_unused_4825_);
                        v___x_4731_ = v_a_4716_;
                        v_isShared_4732_ = v_isSharedCheck_4824_;
                        state = 63;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4729_);
                        crate::leanh::lean_dec(v_a_4716_);
                        v___x_4731_ = crate::leanh::lean_box(0);
                        v_isShared_4732_ = v_isSharedCheck_4824_;
                        state = 63;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_instr_4712_);
                    crate::leanh::lean_dec_ref(v_info_4397_);
                    crate::leanh::lean_dec(v_x_4396_);
                    v_fst_4826_ = crate::leanh::lean_ctor_get(v_a_4716_, 0);
                    crate::leanh::lean_inc(v_fst_4826_);
                    crate::leanh::lean_dec(v_a_4716_);
                    v___x_4827_ = lean_ptr_addr(v_k_4710_);
                    v___x_4828_ = lean_ptr_addr(v_fst_4826_);
                    v___x_4829_ = lean_usize_dec_eq(v___x_4827_, v___x_4828_);
                    if v___x_4829_ == 0 {
                        crate::leanh::lean_inc(v_y_4709_);
                        crate::leanh::lean_inc(v_i_4708_);
                        crate::leanh::lean_inc(v_fvarId_4707_);
                        v_isSharedCheck_4836_ = (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                        if v_isSharedCheck_4836_ == 0 {
                            v_unused_4837_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                            crate::leanh::lean_dec(v_unused_4837_);
                            v_unused_4838_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                            crate::leanh::lean_dec(v_unused_4838_);
                            v_unused_4839_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                            crate::leanh::lean_dec(v_unused_4839_);
                            v_unused_4840_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                            crate::leanh::lean_dec(v_unused_4840_);
                            v___x_4831_ = v_c_4398_;
                            v_isShared_4832_ = v_isSharedCheck_4836_;
                            state = 82;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_c_4398_);
                            v___x_4831_ = crate::leanh::lean_box(0);
                            v_isShared_4832_ = v_isSharedCheck_4836_;
                            state = 82;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_4826_);
                        v___y_4721_ = v_c_4398_;
                        state = 61;
                        continue;
                    }
                }
            }
            61 => {
                v___x_4722_ = crate::leanh::lean_box((v___x_4714_) as usize);
                v___x_4723_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4723_, 0, v___y_4721_);
                crate::leanh::lean_ctor_set(v___x_4723_, 1, v___x_4722_);
                if v_isShared_4719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4718_, 0, v___x_4723_);
                    v___x_4725_ = v___x_4718_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4723_);
                    v___x_4725_ = v_reuseFailAlloc_4726_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_4725_;
            }
            63 => {
                crate::leanh::lean_inc(v_x_4396_);
                v___x_4733_ =
                    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(
                        v_instr_4712_,
                        v_x_4396_,
                        v_a_4399_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4733_) == 0 {
                    v_a_4734_ = crate::leanh::lean_ctor_get(v___x_4733_, 0);
                    v_isSharedCheck_4815_ = (!crate::leanh::lean_is_exclusive(v___x_4733_)) as u8;
                    if v_isSharedCheck_4815_ == 0 {
                        v___x_4736_ = v___x_4733_;
                        v_isShared_4737_ = v_isSharedCheck_4815_;
                        state = 64;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4734_);
                        crate::leanh::lean_dec(v___x_4733_);
                        v___x_4736_ = crate::leanh::lean_box(0);
                        v_isShared_4737_ = v_isSharedCheck_4815_;
                        state = 64;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4731_);
                    crate::leanh::lean_dec(v_fst_4729_);
                    crate::leanh::lean_dec(v_snd_4727_);
                    crate::leanh::lean_dec_ref_known(v_c_4398_, 4);
                    crate::leanh::lean_dec_ref(v_info_4397_);
                    crate::leanh::lean_dec(v_x_4396_);
                    v_a_4816_ = crate::leanh::lean_ctor_get(v___x_4733_, 0);
                    v_isSharedCheck_4823_ = (!crate::leanh::lean_is_exclusive(v___x_4733_)) as u8;
                    if v_isSharedCheck_4823_ == 0 {
                        v___x_4818_ = v___x_4733_;
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 80;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4816_);
                        crate::leanh::lean_dec(v___x_4733_);
                        v___x_4818_ = crate::leanh::lean_box(0);
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 80;
                        continue;
                    }
                }
            }
            64 => {
                v___x_4751_ = (crate::leanh::lean_unbox(v_a_4734_) as u8);
                crate::leanh::lean_dec(v_a_4734_);
                match v___x_4751_ {
                    0 => {
                        crate::leanh::lean_del_object(v___x_4736_);
                        crate::leanh::lean_del_object(v___x_4731_);
                        crate::leanh::lean_dec(v_snd_4727_);
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_dec(v_x_4396_);
                        v___x_4752_ = lean_ptr_addr(v_k_4710_);
                        v___x_4753_ = lean_ptr_addr(v_fst_4729_);
                        v___x_4754_ = lean_usize_dec_eq(v___x_4752_, v___x_4753_);
                        if v___x_4754_ == 0 {
                            crate::leanh::lean_inc(v_y_4709_);
                            crate::leanh::lean_inc(v_i_4708_);
                            crate::leanh::lean_inc(v_fvarId_4707_);
                            v_isSharedCheck_4761_ =
                                (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                            if v_isSharedCheck_4761_ == 0 {
                                v_unused_4762_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                                crate::leanh::lean_dec(v_unused_4762_);
                                v_unused_4763_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                                crate::leanh::lean_dec(v_unused_4763_);
                                v_unused_4764_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                                crate::leanh::lean_dec(v_unused_4764_);
                                v_unused_4765_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                                crate::leanh::lean_dec(v_unused_4765_);
                                v___x_4756_ = v_c_4398_;
                                v_isShared_4757_ = v_isSharedCheck_4761_;
                                state = 69;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_c_4398_);
                                v___x_4756_ = crate::leanh::lean_box(0);
                                v_isShared_4757_ = v_isSharedCheck_4761_;
                                state = 69;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_4729_);
                            v___y_4747_ = v_c_4398_;
                            state = 68;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_4736_);
                        crate::leanh::lean_del_object(v___x_4731_);
                        crate::leanh::lean_dec(v_snd_4727_);
                        v___x_4766_ =
                            l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(
                                v_x_4396_,
                                v_info_4397_,
                                v_fst_4729_,
                                v_a_4399_,
                                v_a_4400_,
                                v_a_4401_,
                                v_a_4402_,
                                v_a_4403_,
                            );
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        if crate::leanh::lean_obj_tag(v___x_4766_) == 0 {
                            v_a_4767_ = crate::leanh::lean_ctor_get(v___x_4766_, 0);
                            v_isSharedCheck_4792_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4766_)) as u8;
                            if v_isSharedCheck_4792_ == 0 {
                                v___x_4769_ = v___x_4766_;
                                v_isShared_4770_ = v_isSharedCheck_4792_;
                                state = 71;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4767_);
                                crate::leanh::lean_dec(v___x_4766_);
                                v___x_4769_ = crate::leanh::lean_box(0);
                                v_isShared_4770_ = v_isSharedCheck_4792_;
                                state = 71;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_4398_, 4);
                            v_a_4793_ = crate::leanh::lean_ctor_get(v___x_4766_, 0);
                            v_isSharedCheck_4800_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4766_)) as u8;
                            if v_isSharedCheck_4800_ == 0 {
                                v___x_4795_ = v___x_4766_;
                                v_isShared_4796_ = v_isSharedCheck_4800_;
                                state = 76;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4793_);
                                crate::leanh::lean_dec(v___x_4766_);
                                v___x_4795_ = crate::leanh::lean_box(0);
                                v_isShared_4796_ = v_isSharedCheck_4800_;
                                state = 76;
                                continue;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_dec(v_x_4396_);
                        v___x_4801_ = lean_ptr_addr(v_k_4710_);
                        v___x_4802_ = lean_ptr_addr(v_fst_4729_);
                        v___x_4803_ = lean_usize_dec_eq(v___x_4801_, v___x_4802_);
                        if v___x_4803_ == 0 {
                            crate::leanh::lean_inc(v_y_4709_);
                            crate::leanh::lean_inc(v_i_4708_);
                            crate::leanh::lean_inc(v_fvarId_4707_);
                            v_isSharedCheck_4810_ =
                                (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                            if v_isSharedCheck_4810_ == 0 {
                                v_unused_4811_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                                crate::leanh::lean_dec(v_unused_4811_);
                                v_unused_4812_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                                crate::leanh::lean_dec(v_unused_4812_);
                                v_unused_4813_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                                crate::leanh::lean_dec(v_unused_4813_);
                                v_unused_4814_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                                crate::leanh::lean_dec(v_unused_4814_);
                                v___x_4805_ = v_c_4398_;
                                v_isShared_4806_ = v_isSharedCheck_4810_;
                                state = 78;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_c_4398_);
                                v___x_4805_ = crate::leanh::lean_box(0);
                                v_isShared_4806_ = v_isSharedCheck_4810_;
                                state = 78;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_4729_);
                            v___y_4739_ = v_c_4398_;
                            state = 65;
                            continue;
                        }
                    }
                }
            }
            65 => {
                if v_isShared_4732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4731_, 0, v___y_4739_);
                    v___x_4741_ = v___x_4731_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_4745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___y_4739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_snd_4727_);
                    v___x_4741_ = v_reuseFailAlloc_4745_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                if v_isShared_4737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4741_);
                    v___x_4743_ = v___x_4736_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4741_);
                    v___x_4743_ = v_reuseFailAlloc_4744_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4743_;
            }
            68 => {
                v___x_4748_ = crate::leanh::lean_box((v___x_4714_) as usize);
                v___x_4749_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4749_, 0, v___y_4747_);
                crate::leanh::lean_ctor_set(v___x_4749_, 1, v___x_4748_);
                v___x_4750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4750_, 0, v___x_4749_);
                return v___x_4750_;
            }
            69 => {
                if v_isShared_4757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4756_, 3, v_fst_4729_);
                    v___x_4759_ = v___x_4756_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_4760_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_fvarId_4707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 1, v_i_4708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 2, v_y_4709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 3, v_fst_4729_);
                    v___x_4759_ = v_reuseFailAlloc_4760_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                v___y_4747_ = v___x_4759_;
                state = 68;
                continue;
            }
            71 => {
                v___x_4778_ = lean_ptr_addr(v_k_4710_);
                v___x_4779_ = lean_ptr_addr(v_a_4767_);
                v___x_4780_ = lean_usize_dec_eq(v___x_4778_, v___x_4779_);
                if v___x_4780_ == 0 {
                    crate::leanh::lean_inc(v_y_4709_);
                    crate::leanh::lean_inc(v_i_4708_);
                    crate::leanh::lean_inc(v_fvarId_4707_);
                    v_isSharedCheck_4787_ = (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                    if v_isSharedCheck_4787_ == 0 {
                        v_unused_4788_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                        crate::leanh::lean_dec(v_unused_4788_);
                        v_unused_4789_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                        crate::leanh::lean_dec(v_unused_4789_);
                        v_unused_4790_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                        crate::leanh::lean_dec(v_unused_4790_);
                        v_unused_4791_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        crate::leanh::lean_dec(v_unused_4791_);
                        v___x_4782_ = v_c_4398_;
                        v_isShared_4783_ = v_isSharedCheck_4787_;
                        state = 74;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_4398_);
                        v___x_4782_ = crate::leanh::lean_box(0);
                        v_isShared_4783_ = v_isSharedCheck_4787_;
                        state = 74;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4767_);
                    v___y_4772_ = v_c_4398_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                v___x_4773_ = crate::leanh::lean_box((v___x_4714_) as usize);
                v___x_4774_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4774_, 0, v___y_4772_);
                crate::leanh::lean_ctor_set(v___x_4774_, 1, v___x_4773_);
                if v_isShared_4770_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4769_, 0, v___x_4774_);
                    v___x_4776_ = v___x_4769_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_4777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4774_);
                    v___x_4776_ = v_reuseFailAlloc_4777_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_4776_;
            }
            74 => {
                if v_isShared_4783_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4782_, 3, v_a_4767_);
                    v___x_4785_ = v___x_4782_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_fvarId_4707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_i_4708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 2, v_y_4709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 3, v_a_4767_);
                    v___x_4785_ = v_reuseFailAlloc_4786_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                v___y_4772_ = v___x_4785_;
                state = 72;
                continue;
            }
            76 => {
                if v_isShared_4796_ == 0 {
                    v___x_4798_ = v___x_4795_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_4799_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
                    v___x_4798_ = v_reuseFailAlloc_4799_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_4798_;
            }
            78 => {
                if v_isShared_4806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4805_, 3, v_fst_4729_);
                    v___x_4808_ = v___x_4805_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_4809_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_fvarId_4707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_i_4708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4809_, 2, v_y_4709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4809_, 3, v_fst_4729_);
                    v___x_4808_ = v_reuseFailAlloc_4809_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___y_4739_ = v___x_4808_;
                state = 65;
                continue;
            }
            80 => {
                if v_isShared_4819_ == 0 {
                    v___x_4821_ = v___x_4818_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_4822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
                    v___x_4821_ = v_reuseFailAlloc_4822_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_4821_;
            }
            82 => {
                if v_isShared_4832_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4831_, 3, v_fst_4826_);
                    v___x_4834_ = v___x_4831_;
                    state = 83;
                    continue;
                } else {
                    v_reuseFailAlloc_4835_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_fvarId_4707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_i_4708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 2, v_y_4709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 3, v_fst_4826_);
                    v___x_4834_ = v_reuseFailAlloc_4835_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                v___y_4721_ = v___x_4834_;
                state = 61;
                continue;
            }
            84 => {
                v_snd_4867_ = crate::leanh::lean_ctor_get(v_a_4856_, 1);
                v___x_4868_ = (crate::leanh::lean_unbox(v_snd_4867_) as u8);
                if v___x_4868_ == 0 {
                    crate::leanh::lean_inc(v_snd_4867_);
                    crate::leanh::lean_del_object(v___x_4858_);
                    v_fst_4869_ = crate::leanh::lean_ctor_get(v_a_4856_, 0);
                    v_isSharedCheck_4970_ = (!crate::leanh::lean_is_exclusive(v_a_4856_)) as u8;
                    if v_isSharedCheck_4970_ == 0 {
                        v_unused_4971_ = crate::leanh::lean_ctor_get(v_a_4856_, 1);
                        crate::leanh::lean_dec(v_unused_4971_);
                        v___x_4871_ = v_a_4856_;
                        v_isShared_4872_ = v_isSharedCheck_4970_;
                        state = 87;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4869_);
                        crate::leanh::lean_dec(v_a_4856_);
                        v___x_4871_ = crate::leanh::lean_box(0);
                        v_isShared_4872_ = v_isSharedCheck_4970_;
                        state = 87;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_instr_4852_);
                    crate::leanh::lean_dec_ref(v_info_4397_);
                    crate::leanh::lean_dec(v_x_4396_);
                    v_fst_4972_ = crate::leanh::lean_ctor_get(v_a_4856_, 0);
                    crate::leanh::lean_inc(v_fst_4972_);
                    crate::leanh::lean_dec(v_a_4856_);
                    v___x_4973_ = lean_ptr_addr(v_k_4850_);
                    v___x_4974_ = lean_ptr_addr(v_fst_4972_);
                    v___x_4975_ = lean_usize_dec_eq(v___x_4973_, v___x_4974_);
                    if v___x_4975_ == 0 {
                        crate::leanh::lean_inc_ref(v_ty_4849_);
                        crate::leanh::lean_inc(v_y_4848_);
                        crate::leanh::lean_inc(v_offset_4847_);
                        crate::leanh::lean_inc(v_i_4846_);
                        crate::leanh::lean_inc(v_fvarId_4845_);
                        v_isSharedCheck_4982_ = (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                        if v_isSharedCheck_4982_ == 0 {
                            v_unused_4983_ = crate::leanh::lean_ctor_get(v_c_4398_, 5);
                            crate::leanh::lean_dec(v_unused_4983_);
                            v_unused_4984_ = crate::leanh::lean_ctor_get(v_c_4398_, 4);
                            crate::leanh::lean_dec(v_unused_4984_);
                            v_unused_4985_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                            crate::leanh::lean_dec(v_unused_4985_);
                            v_unused_4986_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                            crate::leanh::lean_dec(v_unused_4986_);
                            v_unused_4987_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                            crate::leanh::lean_dec(v_unused_4987_);
                            v_unused_4988_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                            crate::leanh::lean_dec(v_unused_4988_);
                            v___x_4977_ = v_c_4398_;
                            v_isShared_4978_ = v_isSharedCheck_4982_;
                            state = 106;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_c_4398_);
                            v___x_4977_ = crate::leanh::lean_box(0);
                            v_isShared_4978_ = v_isSharedCheck_4982_;
                            state = 106;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_4972_);
                        v___y_4861_ = v_c_4398_;
                        state = 85;
                        continue;
                    }
                }
            }
            85 => {
                v___x_4862_ = crate::leanh::lean_box((v___x_4854_) as usize);
                v___x_4863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4863_, 0, v___y_4861_);
                crate::leanh::lean_ctor_set(v___x_4863_, 1, v___x_4862_);
                if v_isShared_4859_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4858_, 0, v___x_4863_);
                    v___x_4865_ = v___x_4858_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_4866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4863_);
                    v___x_4865_ = v_reuseFailAlloc_4866_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_4865_;
            }
            87 => {
                crate::leanh::lean_inc(v_x_4396_);
                v___x_4873_ =
                    l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(
                        v_instr_4852_,
                        v_x_4396_,
                        v_a_4399_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4873_) == 0 {
                    v_a_4874_ = crate::leanh::lean_ctor_get(v___x_4873_, 0);
                    v_isSharedCheck_4961_ = (!crate::leanh::lean_is_exclusive(v___x_4873_)) as u8;
                    if v_isSharedCheck_4961_ == 0 {
                        v___x_4876_ = v___x_4873_;
                        v_isShared_4877_ = v_isSharedCheck_4961_;
                        state = 88;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4874_);
                        crate::leanh::lean_dec(v___x_4873_);
                        v___x_4876_ = crate::leanh::lean_box(0);
                        v_isShared_4877_ = v_isSharedCheck_4961_;
                        state = 88;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4871_);
                    crate::leanh::lean_dec(v_fst_4869_);
                    crate::leanh::lean_dec(v_snd_4867_);
                    crate::leanh::lean_dec_ref_known(v_c_4398_, 6);
                    crate::leanh::lean_dec_ref(v_info_4397_);
                    crate::leanh::lean_dec(v_x_4396_);
                    v_a_4962_ = crate::leanh::lean_ctor_get(v___x_4873_, 0);
                    v_isSharedCheck_4969_ = (!crate::leanh::lean_is_exclusive(v___x_4873_)) as u8;
                    if v_isSharedCheck_4969_ == 0 {
                        v___x_4964_ = v___x_4873_;
                        v_isShared_4965_ = v_isSharedCheck_4969_;
                        state = 104;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4962_);
                        crate::leanh::lean_dec(v___x_4873_);
                        v___x_4964_ = crate::leanh::lean_box(0);
                        v_isShared_4965_ = v_isSharedCheck_4969_;
                        state = 104;
                        continue;
                    }
                }
            }
            88 => {
                v___x_4891_ = (crate::leanh::lean_unbox(v_a_4874_) as u8);
                crate::leanh::lean_dec(v_a_4874_);
                match v___x_4891_ {
                    0 => {
                        crate::leanh::lean_del_object(v___x_4876_);
                        crate::leanh::lean_del_object(v___x_4871_);
                        crate::leanh::lean_dec(v_snd_4867_);
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_dec(v_x_4396_);
                        v___x_4892_ = lean_ptr_addr(v_k_4850_);
                        v___x_4893_ = lean_ptr_addr(v_fst_4869_);
                        v___x_4894_ = lean_usize_dec_eq(v___x_4892_, v___x_4893_);
                        if v___x_4894_ == 0 {
                            crate::leanh::lean_inc_ref(v_ty_4849_);
                            crate::leanh::lean_inc(v_y_4848_);
                            crate::leanh::lean_inc(v_offset_4847_);
                            crate::leanh::lean_inc(v_i_4846_);
                            crate::leanh::lean_inc(v_fvarId_4845_);
                            v_isSharedCheck_4901_ =
                                (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                            if v_isSharedCheck_4901_ == 0 {
                                v_unused_4902_ = crate::leanh::lean_ctor_get(v_c_4398_, 5);
                                crate::leanh::lean_dec(v_unused_4902_);
                                v_unused_4903_ = crate::leanh::lean_ctor_get(v_c_4398_, 4);
                                crate::leanh::lean_dec(v_unused_4903_);
                                v_unused_4904_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                                crate::leanh::lean_dec(v_unused_4904_);
                                v_unused_4905_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                                crate::leanh::lean_dec(v_unused_4905_);
                                v_unused_4906_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                                crate::leanh::lean_dec(v_unused_4906_);
                                v_unused_4907_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                                crate::leanh::lean_dec(v_unused_4907_);
                                v___x_4896_ = v_c_4398_;
                                v_isShared_4897_ = v_isSharedCheck_4901_;
                                state = 93;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_c_4398_);
                                v___x_4896_ = crate::leanh::lean_box(0);
                                v_isShared_4897_ = v_isSharedCheck_4901_;
                                state = 93;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_4869_);
                            v___y_4887_ = v_c_4398_;
                            state = 92;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_4876_);
                        crate::leanh::lean_del_object(v___x_4871_);
                        crate::leanh::lean_dec(v_snd_4867_);
                        v___x_4908_ =
                            l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(
                                v_x_4396_,
                                v_info_4397_,
                                v_fst_4869_,
                                v_a_4399_,
                                v_a_4400_,
                                v_a_4401_,
                                v_a_4402_,
                                v_a_4403_,
                            );
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        if crate::leanh::lean_obj_tag(v___x_4908_) == 0 {
                            v_a_4909_ = crate::leanh::lean_ctor_get(v___x_4908_, 0);
                            v_isSharedCheck_4936_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4908_)) as u8;
                            if v_isSharedCheck_4936_ == 0 {
                                v___x_4911_ = v___x_4908_;
                                v_isShared_4912_ = v_isSharedCheck_4936_;
                                state = 95;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4909_);
                                crate::leanh::lean_dec(v___x_4908_);
                                v___x_4911_ = crate::leanh::lean_box(0);
                                v_isShared_4912_ = v_isSharedCheck_4936_;
                                state = 95;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_4398_, 6);
                            v_a_4937_ = crate::leanh::lean_ctor_get(v___x_4908_, 0);
                            v_isSharedCheck_4944_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4908_)) as u8;
                            if v_isSharedCheck_4944_ == 0 {
                                v___x_4939_ = v___x_4908_;
                                v_isShared_4940_ = v_isSharedCheck_4944_;
                                state = 100;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4937_);
                                crate::leanh::lean_dec(v___x_4908_);
                                v___x_4939_ = crate::leanh::lean_box(0);
                                v_isShared_4940_ = v_isSharedCheck_4944_;
                                state = 100;
                                continue;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_info_4397_);
                        crate::leanh::lean_dec(v_x_4396_);
                        v___x_4945_ = lean_ptr_addr(v_k_4850_);
                        v___x_4946_ = lean_ptr_addr(v_fst_4869_);
                        v___x_4947_ = lean_usize_dec_eq(v___x_4945_, v___x_4946_);
                        if v___x_4947_ == 0 {
                            crate::leanh::lean_inc_ref(v_ty_4849_);
                            crate::leanh::lean_inc(v_y_4848_);
                            crate::leanh::lean_inc(v_offset_4847_);
                            crate::leanh::lean_inc(v_i_4846_);
                            crate::leanh::lean_inc(v_fvarId_4845_);
                            v_isSharedCheck_4954_ =
                                (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                            if v_isSharedCheck_4954_ == 0 {
                                v_unused_4955_ = crate::leanh::lean_ctor_get(v_c_4398_, 5);
                                crate::leanh::lean_dec(v_unused_4955_);
                                v_unused_4956_ = crate::leanh::lean_ctor_get(v_c_4398_, 4);
                                crate::leanh::lean_dec(v_unused_4956_);
                                v_unused_4957_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                                crate::leanh::lean_dec(v_unused_4957_);
                                v_unused_4958_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                                crate::leanh::lean_dec(v_unused_4958_);
                                v_unused_4959_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                                crate::leanh::lean_dec(v_unused_4959_);
                                v_unused_4960_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                                crate::leanh::lean_dec(v_unused_4960_);
                                v___x_4949_ = v_c_4398_;
                                v_isShared_4950_ = v_isSharedCheck_4954_;
                                state = 102;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_c_4398_);
                                v___x_4949_ = crate::leanh::lean_box(0);
                                v_isShared_4950_ = v_isSharedCheck_4954_;
                                state = 102;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_4869_);
                            v___y_4879_ = v_c_4398_;
                            state = 89;
                            continue;
                        }
                    }
                }
            }
            89 => {
                if v_isShared_4872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4871_, 0, v___y_4879_);
                    v___x_4881_ = v___x_4871_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_4885_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___y_4879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_snd_4867_);
                    v___x_4881_ = v_reuseFailAlloc_4885_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_4877_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4876_, 0, v___x_4881_);
                    v___x_4883_ = v___x_4876_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_4884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
                    v___x_4883_ = v_reuseFailAlloc_4884_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_4883_;
            }
            92 => {
                v___x_4888_ = crate::leanh::lean_box((v___x_4854_) as usize);
                v___x_4889_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4889_, 0, v___y_4887_);
                crate::leanh::lean_ctor_set(v___x_4889_, 1, v___x_4888_);
                v___x_4890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4890_, 0, v___x_4889_);
                return v___x_4890_;
            }
            93 => {
                if v_isShared_4897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4896_, 5, v_fst_4869_);
                    v___x_4899_ = v___x_4896_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_4900_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_fvarId_4845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4900_, 1, v_i_4846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4900_, 2, v_offset_4847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4900_, 3, v_y_4848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4900_, 4, v_ty_4849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4900_, 5, v_fst_4869_);
                    v___x_4899_ = v_reuseFailAlloc_4900_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                v___y_4887_ = v___x_4899_;
                state = 92;
                continue;
            }
            95 => {
                v___x_4920_ = lean_ptr_addr(v_k_4850_);
                v___x_4921_ = lean_ptr_addr(v_a_4909_);
                v___x_4922_ = lean_usize_dec_eq(v___x_4920_, v___x_4921_);
                if v___x_4922_ == 0 {
                    crate::leanh::lean_inc_ref(v_ty_4849_);
                    crate::leanh::lean_inc(v_y_4848_);
                    crate::leanh::lean_inc(v_offset_4847_);
                    crate::leanh::lean_inc(v_i_4846_);
                    crate::leanh::lean_inc(v_fvarId_4845_);
                    v_isSharedCheck_4929_ = (!crate::leanh::lean_is_exclusive(v_c_4398_)) as u8;
                    if v_isSharedCheck_4929_ == 0 {
                        v_unused_4930_ = crate::leanh::lean_ctor_get(v_c_4398_, 5);
                        crate::leanh::lean_dec(v_unused_4930_);
                        v_unused_4931_ = crate::leanh::lean_ctor_get(v_c_4398_, 4);
                        crate::leanh::lean_dec(v_unused_4931_);
                        v_unused_4932_ = crate::leanh::lean_ctor_get(v_c_4398_, 3);
                        crate::leanh::lean_dec(v_unused_4932_);
                        v_unused_4933_ = crate::leanh::lean_ctor_get(v_c_4398_, 2);
                        crate::leanh::lean_dec(v_unused_4933_);
                        v_unused_4934_ = crate::leanh::lean_ctor_get(v_c_4398_, 1);
                        crate::leanh::lean_dec(v_unused_4934_);
                        v_unused_4935_ = crate::leanh::lean_ctor_get(v_c_4398_, 0);
                        crate::leanh::lean_dec(v_unused_4935_);
                        v___x_4924_ = v_c_4398_;
                        v_isShared_4925_ = v_isSharedCheck_4929_;
                        state = 98;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_4398_);
                        v___x_4924_ = crate::leanh::lean_box(0);
                        v_isShared_4925_ = v_isSharedCheck_4929_;
                        state = 98;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4909_);
                    v___y_4914_ = v_c_4398_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                v___x_4915_ = crate::leanh::lean_box((v___x_4854_) as usize);
                v___x_4916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4916_, 0, v___y_4914_);
                crate::leanh::lean_ctor_set(v___x_4916_, 1, v___x_4915_);
                if v_isShared_4912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4911_, 0, v___x_4916_);
                    v___x_4918_ = v___x_4911_;
                    state = 97;
                    continue;
                } else {
                    v_reuseFailAlloc_4919_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4916_);
                    v___x_4918_ = v_reuseFailAlloc_4919_;
                    state = 97;
                    continue;
                }
            }
            97 => {
                return v___x_4918_;
            }
            98 => {
                if v_isShared_4925_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4924_, 5, v_a_4909_);
                    v___x_4927_ = v___x_4924_;
                    state = 99;
                    continue;
                } else {
                    v_reuseFailAlloc_4928_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_fvarId_4845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 1, v_i_4846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 2, v_offset_4847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 3, v_y_4848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 4, v_ty_4849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 5, v_a_4909_);
                    v___x_4927_ = v_reuseFailAlloc_4928_;
                    state = 99;
                    continue;
                }
            }
            99 => {
                v___y_4914_ = v___x_4927_;
                state = 96;
                continue;
            }
            100 => {
                if v_isShared_4940_ == 0 {
                    v___x_4942_ = v___x_4939_;
                    state = 101;
                    continue;
                } else {
                    v_reuseFailAlloc_4943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_a_4937_);
                    v___x_4942_ = v_reuseFailAlloc_4943_;
                    state = 101;
                    continue;
                }
            }
            101 => {
                return v___x_4942_;
            }
            102 => {
                if v_isShared_4950_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4949_, 5, v_fst_4869_);
                    v___x_4952_ = v___x_4949_;
                    state = 103;
                    continue;
                } else {
                    v_reuseFailAlloc_4953_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_fvarId_4845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 1, v_i_4846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 2, v_offset_4847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 3, v_y_4848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 4, v_ty_4849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 5, v_fst_4869_);
                    v___x_4952_ = v_reuseFailAlloc_4953_;
                    state = 103;
                    continue;
                }
            }
            103 => {
                v___y_4879_ = v___x_4952_;
                state = 89;
                continue;
            }
            104 => {
                if v_isShared_4965_ == 0 {
                    v___x_4967_ = v___x_4964_;
                    state = 105;
                    continue;
                } else {
                    v_reuseFailAlloc_4968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
                    v___x_4967_ = v_reuseFailAlloc_4968_;
                    state = 105;
                    continue;
                }
            }
            105 => {
                return v___x_4967_;
            }
            106 => {
                if v_isShared_4978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4977_, 5, v_fst_4972_);
                    v___x_4980_ = v___x_4977_;
                    state = 107;
                    continue;
                } else {
                    v_reuseFailAlloc_4981_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_fvarId_4845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_i_4846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 2, v_offset_4847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 3, v_y_4848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 4, v_ty_4849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 5, v_fst_4972_);
                    v___x_4980_ = v_reuseFailAlloc_4981_;
                    state = 107;
                    continue;
                }
            }
            107 => {
                v___y_4861_ = v___x_4980_;
                state = 85;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(
    mut v_x_4995_: *mut crate::leanh::LeanObject,
    mut v_info_4996_: *mut crate::leanh::LeanObject,
    mut v_c_4997_: *mut crate::leanh::LeanObject,
    mut v_a_4998_: *mut crate::leanh::LeanObject,
    mut v_a_4999_: *mut crate::leanh::LeanObject,
    mut v_a_5000_: *mut crate::leanh::LeanObject,
    mut v_a_5001_: *mut crate::leanh::LeanObject,
    mut v_a_5002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5008_: u8 = 0;
    let mut v_snd_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: u8 = 0;
    let mut v_fst_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_a_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5021_: u8 = 0;
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_info_4996_);
                crate::leanh::lean_inc(v_x_4995_);
                v___x_5004_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(
                    v_x_4995_,
                    v_info_4996_,
                    v_c_4997_,
                    v_a_4998_,
                    v_a_4999_,
                    v_a_5000_,
                    v_a_5001_,
                    v_a_5002_,
                );
                if crate::leanh::lean_obj_tag(v___x_5004_) == 0 {
                    v_a_5005_ = crate::leanh::lean_ctor_get(v___x_5004_, 0);
                    v_isSharedCheck_5017_ = (!crate::leanh::lean_is_exclusive(v___x_5004_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v___x_5007_ = v___x_5004_;
                        v_isShared_5008_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5005_);
                        crate::leanh::lean_dec(v___x_5004_);
                        v___x_5007_ = crate::leanh::lean_box(0);
                        v_isShared_5008_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_4996_);
                    crate::leanh::lean_dec(v_x_4995_);
                    v_a_5018_ = crate::leanh::lean_ctor_get(v___x_5004_, 0);
                    v_isSharedCheck_5025_ = (!crate::leanh::lean_is_exclusive(v___x_5004_)) as u8;
                    if v_isSharedCheck_5025_ == 0 {
                        v___x_5020_ = v___x_5004_;
                        v_isShared_5021_ = v_isSharedCheck_5025_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5018_);
                        crate::leanh::lean_dec(v___x_5004_);
                        v___x_5020_ = crate::leanh::lean_box(0);
                        v_isShared_5021_ = v_isSharedCheck_5025_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5009_ = crate::leanh::lean_ctor_get(v_a_5005_, 1);
                v___x_5010_ = (crate::leanh::lean_unbox(v_snd_5009_) as u8);
                if v___x_5010_ == 0 {
                    crate::leanh::lean_del_object(v___x_5007_);
                    v_fst_5011_ = crate::leanh::lean_ctor_get(v_a_5005_, 0);
                    crate::leanh::lean_inc(v_fst_5011_);
                    crate::leanh::lean_dec(v_a_5005_);
                    v___x_5012_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(
                        v_x_4995_,
                        v_info_4996_,
                        v_fst_5011_,
                        v_a_4998_,
                        v_a_4999_,
                        v_a_5000_,
                        v_a_5001_,
                        v_a_5002_,
                    );
                    crate::leanh::lean_dec_ref(v_info_4996_);
                    return v___x_5012_;
                } else {
                    crate::leanh::lean_dec_ref(v_info_4996_);
                    crate::leanh::lean_dec(v_x_4995_);
                    v_fst_5013_ = crate::leanh::lean_ctor_get(v_a_5005_, 0);
                    crate::leanh::lean_inc(v_fst_5013_);
                    crate::leanh::lean_dec(v_a_5005_);
                    if v_isShared_5008_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5007_, 0, v_fst_5013_);
                        v___x_5015_ = v___x_5007_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_fst_5013_);
                        v___x_5015_ = v_reuseFailAlloc_5016_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5015_;
            }
            3 => {
                if v_isShared_5021_ == 0 {
                    v___x_5023_ = v___x_5020_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
                    v___x_5023_ = v_reuseFailAlloc_5024_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(
    mut v_x_5026_: *mut crate::leanh::LeanObject,
    mut v_info_5027_: *mut crate::leanh::LeanObject,
    mut v_i_5028_: *mut crate::leanh::LeanObject,
    mut v_as_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5036_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_5026_, v_info_5027_, v_i_5028_, v_as_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
    crate::leanh::lean_dec(v___y_5034_);
    crate::leanh::lean_dec_ref(v___y_5033_);
    crate::leanh::lean_dec(v___y_5032_);
    crate::leanh::lean_dec_ref(v___y_5031_);
    crate::leanh::lean_dec_ref(v___y_5030_);
    return v_res_5036_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(
    mut v_x_5037_: *mut crate::leanh::LeanObject,
    mut v_info_5038_: *mut crate::leanh::LeanObject,
    mut v_c_5039_: *mut crate::leanh::LeanObject,
    mut v_a_5040_: *mut crate::leanh::LeanObject,
    mut v_a_5041_: *mut crate::leanh::LeanObject,
    mut v_a_5042_: *mut crate::leanh::LeanObject,
    mut v_a_5043_: *mut crate::leanh::LeanObject,
    mut v_a_5044_: *mut crate::leanh::LeanObject,
    mut v_a_5045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5046_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(
        v_x_5037_,
        v_info_5038_,
        v_c_5039_,
        v_a_5040_,
        v_a_5041_,
        v_a_5042_,
        v_a_5043_,
        v_a_5044_,
    );
    crate::leanh::lean_dec(v_a_5044_);
    crate::leanh::lean_dec_ref(v_a_5043_);
    crate::leanh::lean_dec(v_a_5042_);
    crate::leanh::lean_dec_ref(v_a_5041_);
    crate::leanh::lean_dec_ref(v_a_5040_);
    return v_res_5046_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(
    mut v_pu_5047_: u8,
    mut v_alt_5048_: *mut crate::leanh::LeanObject,
    mut v_f_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5056_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_5048_, v_f_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
    return v___x_5056_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(
    mut v_pu_5057_: *mut crate::leanh::LeanObject,
    mut v_alt_5058_: *mut crate::leanh::LeanObject,
    mut v_f_5059_: *mut crate::leanh::LeanObject,
    mut v___y_5060_: *mut crate::leanh::LeanObject,
    mut v___y_5061_: *mut crate::leanh::LeanObject,
    mut v___y_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5066_: u8 = 0;
    let mut v_res_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5066_ = (crate::leanh::lean_unbox(v_pu_5057_) as u8);
    v_res_5067_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(v_pu_boxed_5066_, v_alt_5058_, v_f_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
    crate::leanh::lean_dec(v___y_5064_);
    crate::leanh::lean_dec_ref(v___y_5063_);
    crate::leanh::lean_dec(v___y_5062_);
    crate::leanh::lean_dec_ref(v___y_5061_);
    crate::leanh::lean_dec_ref(v___y_5060_);
    return v_res_5067_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(
    mut v_msg_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
    mut v___y_5072_: *mut crate::leanh::LeanObject,
    mut v___y_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5080_: u8 = 0;
    let mut v_toFunctor_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5087_: u8 = 0;
    let mut v___f_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620__overap_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5109_: u8 = 0;
    let mut v_unused_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5111_: u8 = 0;
    let mut v_unused_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
                v___x_5076_ = l_StateRefT_x27_instMonad___redArg(v___x_5075_);
                v_toApplicative_5077_ = crate::leanh::lean_ctor_get(v___x_5076_, 0);
                v_isSharedCheck_5111_ = (!crate::leanh::lean_is_exclusive(v___x_5076_)) as u8;
                if v_isSharedCheck_5111_ == 0 {
                    v_unused_5112_ = crate::leanh::lean_ctor_get(v___x_5076_, 1);
                    crate::leanh::lean_dec(v_unused_5112_);
                    v___x_5079_ = v___x_5076_;
                    v_isShared_5080_ = v_isSharedCheck_5111_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5077_);
                    crate::leanh::lean_dec(v___x_5076_);
                    v___x_5079_ = crate::leanh::lean_box(0);
                    v_isShared_5080_ = v_isSharedCheck_5111_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5081_ = crate::leanh::lean_ctor_get(v_toApplicative_5077_, 0);
                v_toSeq_5082_ = crate::leanh::lean_ctor_get(v_toApplicative_5077_, 2);
                v_toSeqLeft_5083_ = crate::leanh::lean_ctor_get(v_toApplicative_5077_, 3);
                v_toSeqRight_5084_ = crate::leanh::lean_ctor_get(v_toApplicative_5077_, 4);
                v_isSharedCheck_5109_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5077_)) as u8;
                if v_isSharedCheck_5109_ == 0 {
                    v_unused_5110_ = crate::leanh::lean_ctor_get(v_toApplicative_5077_, 1);
                    crate::leanh::lean_dec(v_unused_5110_);
                    v___x_5086_ = v_toApplicative_5077_;
                    v_isShared_5087_ = v_isSharedCheck_5109_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5084_);
                    crate::leanh::lean_inc(v_toSeqLeft_5083_);
                    crate::leanh::lean_inc(v_toSeq_5082_);
                    crate::leanh::lean_inc(v_toFunctor_5081_);
                    crate::leanh::lean_dec(v_toApplicative_5077_);
                    v___x_5086_ = crate::leanh::lean_box(0);
                    v_isShared_5087_ = v_isSharedCheck_5109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5088_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1;
                v___f_5089_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_5081_);
                v___f_5090_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5090_, 0, v_toFunctor_5081_);
                v___f_5091_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5091_, 0, v_toFunctor_5081_);
                v___x_5092_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5092_, 0, v___f_5090_);
                crate::leanh::lean_ctor_set(v___x_5092_, 1, v___f_5091_);
                v___f_5093_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5093_, 0, v_toSeqRight_5084_);
                v___f_5094_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5094_, 0, v_toSeqLeft_5083_);
                v___f_5095_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5095_, 0, v_toSeq_5082_);
                if v_isShared_5087_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5086_, 4, v___f_5093_);
                    crate::leanh::lean_ctor_set(v___x_5086_, 3, v___f_5094_);
                    crate::leanh::lean_ctor_set(v___x_5086_, 2, v___f_5095_);
                    crate::leanh::lean_ctor_set(v___x_5086_, 1, v___f_5088_);
                    crate::leanh::lean_ctor_set(v___x_5086_, 0, v___x_5092_);
                    v___x_5097_ = v___x_5086_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5108_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 1, v___f_5088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 2, v___f_5095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 3, v___f_5094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 4, v___f_5093_);
                    v___x_5097_ = v_reuseFailAlloc_5108_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5079_, 1, v___f_5089_);
                    crate::leanh::lean_ctor_set(v___x_5079_, 0, v___x_5097_);
                    v___x_5099_ = v___x_5079_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5107_, 1, v___f_5089_);
                    v___x_5099_ = v_reuseFailAlloc_5107_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5100_ = l_StateRefT_x27_instMonad___redArg(v___x_5099_);
                v___x_5101_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
                v___x_5102_ = l_instInhabitedOfMonad___redArg(v___x_5100_, v___x_5101_);
                v___f_5103_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5103_, 0, v___x_5102_);
                v___f_5104_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5104_, 0, v___f_5103_);
                v___x_5620__overap_5105_ = lean_panic_fn_borrowed(v___f_5104_, v_msg_5068_);
                crate::leanh::lean_dec_ref(v___f_5104_);
                crate::leanh::lean_inc(v___y_5073_);
                crate::leanh::lean_inc_ref(v___y_5072_);
                crate::leanh::lean_inc(v___y_5071_);
                crate::leanh::lean_inc_ref(v___y_5070_);
                crate::leanh::lean_inc_ref(v___y_5069_);
                v___x_5106_ = crate::leanh::lean_apply_6(
                    v___x_5620__overap_5105_,
                    v___y_5069_,
                    v___y_5070_,
                    v___y_5071_,
                    v___y_5072_,
                    v___y_5073_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(
    mut v_msg_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5120_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v_msg_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
    crate::leanh::lean_dec(v___y_5118_);
    crate::leanh::lean_dec_ref(v___y_5117_);
    crate::leanh::lean_dec(v___y_5116_);
    crate::leanh::lean_dec_ref(v___y_5115_);
    crate::leanh::lean_dec_ref(v___y_5114_);
    return v_res_5120_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(
    mut v_a_5121_: *mut crate::leanh::LeanObject,
    mut v_fallback_5122_: *mut crate::leanh::LeanObject,
    mut v_x_5123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5123_) == 0 {
                    crate::leanh::lean_inc(v_fallback_5122_);
                    return v_fallback_5122_;
                } else {
                    v_key_5124_ = crate::leanh::lean_ctor_get(v_x_5123_, 0);
                    v_value_5125_ = crate::leanh::lean_ctor_get(v_x_5123_, 1);
                    v_tail_5126_ = crate::leanh::lean_ctor_get(v_x_5123_, 2);
                    v___x_5127_ = l_Lean_instBEqFVarId_beq(v_key_5124_, v_a_5121_);
                    if v___x_5127_ == 0 {
                        v_x_5123_ = v_tail_5126_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5125_);
                        return v_value_5125_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(
    mut v_a_5129_: *mut crate::leanh::LeanObject,
    mut v_fallback_5130_: *mut crate::leanh::LeanObject,
    mut v_x_5131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5132_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_5129_, v_fallback_5130_, v_x_5131_);
    crate::leanh::lean_dec(v_x_5131_);
    crate::leanh::lean_dec(v_fallback_5130_);
    crate::leanh::lean_dec(v_a_5129_);
    return v_res_5132_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(
    mut v_m_5133_: *mut crate::leanh::LeanObject,
    mut v_a_5134_: *mut crate::leanh::LeanObject,
    mut v_fallback_5135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: u64 = 0;
    let mut v___x_5139_: u64 = 0;
    let mut v___x_5140_: u64 = 0;
    let mut v_fold_5141_: u64 = 0;
    let mut v___x_5142_: u64 = 0;
    let mut v___x_5143_: u64 = 0;
    let mut v___x_5144_: u64 = 0;
    let mut v___x_5145_: usize = 0;
    let mut v___x_5146_: usize = 0;
    let mut v___x_5147_: usize = 0;
    let mut v___x_5148_: usize = 0;
    let mut v___x_5149_: usize = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5136_ = crate::leanh::lean_ctor_get(v_m_5133_, 1);
    v___x_5137_ = lean_array_get_size(v_buckets_5136_);
    v___x_5138_ = l_Lean_instHashableFVarId_hash(v_a_5134_);
    v___x_5139_ = 32u64;
    v___x_5140_ = lean_uint64_shift_right(v___x_5138_, v___x_5139_);
    v_fold_5141_ = lean_uint64_xor(v___x_5138_, v___x_5140_);
    v___x_5142_ = 16u64;
    v___x_5143_ = lean_uint64_shift_right(v_fold_5141_, v___x_5142_);
    v___x_5144_ = lean_uint64_xor(v_fold_5141_, v___x_5143_);
    v___x_5145_ = lean_uint64_to_usize(v___x_5144_);
    v___x_5146_ = lean_usize_of_nat(v___x_5137_);
    v___x_5147_ = 1usize;
    v___x_5148_ = lean_usize_sub(v___x_5146_, v___x_5147_);
    v___x_5149_ = lean_usize_land(v___x_5145_, v___x_5148_);
    v___x_5150_ = lean_array_uget_borrowed(v_buckets_5136_, v___x_5149_);
    v___x_5151_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_5134_, v_fallback_5135_, v___x_5150_);
    return v___x_5151_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(
    mut v_m_5152_: *mut crate::leanh::LeanObject,
    mut v_a_5153_: *mut crate::leanh::LeanObject,
    mut v_fallback_5154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_5152_, v_a_5153_, v_fallback_5154_);
    crate::leanh::lean_dec(v_fallback_5154_);
    crate::leanh::lean_dec(v_a_5153_);
    crate::leanh::lean_dec_ref(v_m_5152_);
    return v_res_5155_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(
    mut v_x_5156_: *mut crate::leanh::LeanObject,
    mut v_x_5157_: *mut crate::leanh::LeanObject,
    mut v_x_5158_: *mut crate::leanh::LeanObject,
    mut v_x_5159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: u8 = 0;
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: u8 = 0;
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5160_ = crate::leanh::lean_ctor_get(v_x_5156_, 0);
                v_vs_5161_ = crate::leanh::lean_ctor_get(v_x_5156_, 1);
                v_isSharedCheck_5185_ = (!crate::leanh::lean_is_exclusive(v_x_5156_)) as u8;
                if v_isSharedCheck_5185_ == 0 {
                    v___x_5163_ = v_x_5156_;
                    v_isShared_5164_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_5161_);
                    crate::leanh::lean_inc(v_ks_5160_);
                    crate::leanh::lean_dec(v_x_5156_);
                    v___x_5163_ = crate::leanh::lean_box(0);
                    v_isShared_5164_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5165_ = lean_array_get_size(v_ks_5160_);
                v___x_5166_ = lean_nat_dec_lt(v_x_5157_, v___x_5165_);
                if v___x_5166_ == 0 {
                    crate::leanh::lean_dec(v_x_5157_);
                    v___x_5167_ = lean_array_push(v_ks_5160_, v_x_5158_);
                    v___x_5168_ = lean_array_push(v_vs_5161_, v_x_5159_);
                    if v_isShared_5164_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5163_, 1, v___x_5168_);
                        crate::leanh::lean_ctor_set(v___x_5163_, 0, v___x_5167_);
                        v___x_5170_ = v___x_5163_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5171_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5167_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 1, v___x_5168_);
                        v___x_5170_ = v_reuseFailAlloc_5171_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5172_ = lean_array_fget_borrowed(v_ks_5160_, v_x_5157_);
                    v___x_5173_ = l_Lean_instBEqFVarId_beq(v_x_5158_, v_k_x27_5172_);
                    if v___x_5173_ == 0 {
                        if v_isShared_5164_ == 0 {
                            v___x_5175_ = v___x_5163_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5179_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_ks_5160_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5179_, 1, v_vs_5161_);
                            v___x_5175_ = v_reuseFailAlloc_5179_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5180_ = lean_array_fset(v_ks_5160_, v_x_5157_, v_x_5158_);
                        v___x_5181_ = lean_array_fset(v_vs_5161_, v_x_5157_, v_x_5159_);
                        crate::leanh::lean_dec(v_x_5157_);
                        if v_isShared_5164_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5163_, 1, v___x_5181_);
                            crate::leanh::lean_ctor_set(v___x_5163_, 0, v___x_5180_);
                            v___x_5183_ = v___x_5163_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5184_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5180_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 1, v___x_5181_);
                            v___x_5183_ = v_reuseFailAlloc_5184_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5170_;
            }
            3 => {
                v___x_5176_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5177_ = lean_nat_add(v_x_5157_, v___x_5176_);
                crate::leanh::lean_dec(v_x_5157_);
                v_x_5156_ = v___x_5175_;
                v_x_5157_ = v___x_5177_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(
    mut v_n_5186_: *mut crate::leanh::LeanObject,
    mut v_k_5187_: *mut crate::leanh::LeanObject,
    mut v_v_5188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5189_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5190_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_n_5186_, v___x_5189_, v_k_5187_, v_v_5188_);
    return v___x_5190_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_5191_: usize = 0;
    let mut v___x_5192_: usize = 0;
    let mut v___x_5193_: usize = 0;
    v___x_5191_ = 5usize;
    v___x_5192_ = 1usize;
    v___x_5193_ = lean_usize_shift_left(v___x_5192_, v___x_5191_);
    return v___x_5193_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_5194_: usize = 0;
    let mut v___x_5195_: usize = 0;
    let mut v___x_5196_: usize = 0;
    v___x_5194_ = 1usize;
    v___x_5195_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0);
    v___x_5196_ = lean_usize_sub(v___x_5195_, v___x_5194_);
    return v___x_5196_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5197_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5197_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(
    mut v_x_5198_: *mut crate::leanh::LeanObject,
    mut v_x_5199_: usize,
    mut v_x_5200_: usize,
    mut v_x_5201_: *mut crate::leanh::LeanObject,
    mut v_x_5202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: usize = 0;
    let mut v___x_5205_: usize = 0;
    let mut v___x_5206_: usize = 0;
    let mut v___x_5207_: usize = 0;
    let mut v_j_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: u8 = 0;
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5213_: u8 = 0;
    let mut v_v_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5227_: u8 = 0;
    let mut v___x_5228_: u8 = 0;
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5234_: u8 = 0;
    let mut v_node_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5239_: usize = 0;
    let mut v___x_5240_: usize = 0;
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5245_: u8 = 0;
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5247_: u8 = 0;
    let mut v_unused_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5253_: u8 = 0;
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5258_: u8 = 0;
    let mut v_ks_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: usize = 0;
    let mut v___x_5265_: u8 = 0;
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: u8 = 0;
    let mut v_reuseFailAlloc_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5198_) == 0 {
                    v_es_5203_ = crate::leanh::lean_ctor_get(v_x_5198_, 0);
                    v___x_5204_ = 5usize;
                    v___x_5205_ = 1usize;
                    v___x_5206_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1);
                    v___x_5207_ = lean_usize_land(v_x_5199_, v___x_5206_);
                    v_j_5208_ = lean_usize_to_nat(v___x_5207_);
                    v___x_5209_ = lean_array_get_size(v_es_5203_);
                    v___x_5210_ = lean_nat_dec_lt(v_j_5208_, v___x_5209_);
                    if v___x_5210_ == 0 {
                        crate::leanh::lean_dec(v_j_5208_);
                        crate::leanh::lean_dec(v_x_5202_);
                        crate::leanh::lean_dec(v_x_5201_);
                        return v_x_5198_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_5203_);
                        v_isSharedCheck_5247_ = (!crate::leanh::lean_is_exclusive(v_x_5198_)) as u8;
                        if v_isSharedCheck_5247_ == 0 {
                            v_unused_5248_ = crate::leanh::lean_ctor_get(v_x_5198_, 0);
                            crate::leanh::lean_dec(v_unused_5248_);
                            v___x_5212_ = v_x_5198_;
                            v_isShared_5213_ = v_isSharedCheck_5247_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_5198_);
                            v___x_5212_ = crate::leanh::lean_box(0);
                            v_isShared_5213_ = v_isSharedCheck_5247_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5249_ = crate::leanh::lean_ctor_get(v_x_5198_, 0);
                    v_vs_5250_ = crate::leanh::lean_ctor_get(v_x_5198_, 1);
                    v_isSharedCheck_5270_ = (!crate::leanh::lean_is_exclusive(v_x_5198_)) as u8;
                    if v_isSharedCheck_5270_ == 0 {
                        v___x_5252_ = v_x_5198_;
                        v_isShared_5253_ = v_isSharedCheck_5270_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5250_);
                        crate::leanh::lean_inc(v_ks_5249_);
                        crate::leanh::lean_dec(v_x_5198_);
                        v___x_5252_ = crate::leanh::lean_box(0);
                        v_isShared_5253_ = v_isSharedCheck_5270_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5214_ = lean_array_fget(v_es_5203_, v_j_5208_);
                v___x_5215_ = crate::leanh::lean_box(0);
                v_xs_x27_5216_ = lean_array_fset(v_es_5203_, v_j_5208_, v___x_5215_);
                match crate::leanh::lean_obj_tag(v_v_5214_) {
                    0 => {
                        v_key_5223_ = crate::leanh::lean_ctor_get(v_v_5214_, 0);
                        v_val_5224_ = crate::leanh::lean_ctor_get(v_v_5214_, 1);
                        v_isSharedCheck_5234_ = (!crate::leanh::lean_is_exclusive(v_v_5214_)) as u8;
                        if v_isSharedCheck_5234_ == 0 {
                            v___x_5226_ = v_v_5214_;
                            v_isShared_5227_ = v_isSharedCheck_5234_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5224_);
                            crate::leanh::lean_inc(v_key_5223_);
                            crate::leanh::lean_dec(v_v_5214_);
                            v___x_5226_ = crate::leanh::lean_box(0);
                            v_isShared_5227_ = v_isSharedCheck_5234_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5235_ = crate::leanh::lean_ctor_get(v_v_5214_, 0);
                        v_isSharedCheck_5245_ = (!crate::leanh::lean_is_exclusive(v_v_5214_)) as u8;
                        if v_isSharedCheck_5245_ == 0 {
                            v___x_5237_ = v_v_5214_;
                            v_isShared_5238_ = v_isSharedCheck_5245_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_5235_);
                            crate::leanh::lean_dec(v_v_5214_);
                            v___x_5237_ = crate::leanh::lean_box(0);
                            v_isShared_5238_ = v_isSharedCheck_5245_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5246_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5246_, 0, v_x_5201_);
                        crate::leanh::lean_ctor_set(v___x_5246_, 1, v_x_5202_);
                        v___y_5218_ = v___x_5246_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5219_ = lean_array_fset(v_xs_x27_5216_, v_j_5208_, v___y_5218_);
                crate::leanh::lean_dec(v_j_5208_);
                if v_isShared_5213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5212_, 0, v___x_5219_);
                    v___x_5221_ = v___x_5212_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5219_);
                    v___x_5221_ = v_reuseFailAlloc_5222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5221_;
            }
            4 => {
                v___x_5228_ = l_Lean_instBEqFVarId_beq(v_x_5201_, v_key_5223_);
                if v___x_5228_ == 0 {
                    crate::leanh::lean_del_object(v___x_5226_);
                    v___x_5229_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5223_,
                        v_val_5224_,
                        v_x_5201_,
                        v_x_5202_,
                    );
                    v___x_5230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5230_, 0, v___x_5229_);
                    v___y_5218_ = v___x_5230_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_5224_);
                    crate::leanh::lean_dec(v_key_5223_);
                    if v_isShared_5227_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5226_, 1, v_x_5202_);
                        crate::leanh::lean_ctor_set(v___x_5226_, 0, v_x_5201_);
                        v___x_5232_ = v___x_5226_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_x_5201_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 1, v_x_5202_);
                        v___x_5232_ = v_reuseFailAlloc_5233_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5218_ = v___x_5232_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5239_ = lean_usize_shift_right(v_x_5199_, v___x_5204_);
                v___x_5240_ = lean_usize_add(v_x_5200_, v___x_5205_);
                v___x_5241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_node_5235_, v___x_5239_, v___x_5240_, v_x_5201_, v_x_5202_);
                if v_isShared_5238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5237_, 0, v___x_5241_);
                    v___x_5243_ = v___x_5237_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5241_);
                    v___x_5243_ = v_reuseFailAlloc_5244_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5218_ = v___x_5243_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5253_ == 0 {
                    v___x_5255_ = v___x_5252_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5269_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_ks_5249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5269_, 1, v_vs_5250_);
                    v___x_5255_ = v_reuseFailAlloc_5269_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5256_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v___x_5255_, v_x_5201_, v_x_5202_);
                v___x_5264_ = 7usize;
                v___x_5265_ = lean_usize_dec_le(v___x_5264_, v_x_5200_);
                if v___x_5265_ == 0 {
                    v___x_5266_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5256_);
                    v___x_5267_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5268_ = lean_nat_dec_lt(v___x_5266_, v___x_5267_);
                    crate::leanh::lean_dec(v___x_5266_);
                    v___y_5258_ = v___x_5268_;
                    state = 10;
                    continue;
                } else {
                    v___y_5258_ = v___x_5265_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5258_ == 0 {
                    v_ks_5259_ = crate::leanh::lean_ctor_get(v_newNode_5256_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5259_);
                    v_vs_5260_ = crate::leanh::lean_ctor_get(v_newNode_5256_, 1);
                    crate::leanh::lean_inc_ref(v_vs_5260_);
                    crate::leanh::lean_dec_ref(v_newNode_5256_);
                    v___x_5261_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5262_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2);
                    v___x_5263_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_x_5200_, v_ks_5259_, v_vs_5260_, v___x_5261_, v___x_5262_);
                    crate::leanh::lean_dec_ref(v_vs_5260_);
                    crate::leanh::lean_dec_ref(v_ks_5259_);
                    return v___x_5263_;
                } else {
                    return v_newNode_5256_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(
    mut v_depth_5271_: usize,
    mut v_keys_5272_: *mut crate::leanh::LeanObject,
    mut v_vals_5273_: *mut crate::leanh::LeanObject,
    mut v_i_5274_: *mut crate::leanh::LeanObject,
    mut v_entries_5275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: u8 = 0;
    let mut v_k_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: u64 = 0;
    let mut v_h_5281_: usize = 0;
    let mut v___x_5282_: usize = 0;
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: usize = 0;
    let mut v___x_5285_: usize = 0;
    let mut v___x_5286_: usize = 0;
    let mut v_h_5287_: usize = 0;
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5276_ = lean_array_get_size(v_keys_5272_);
                v___x_5277_ = lean_nat_dec_lt(v_i_5274_, v___x_5276_);
                if v___x_5277_ == 0 {
                    crate::leanh::lean_dec(v_i_5274_);
                    return v_entries_5275_;
                } else {
                    v_k_5278_ = lean_array_fget_borrowed(v_keys_5272_, v_i_5274_);
                    v_v_5279_ = lean_array_fget_borrowed(v_vals_5273_, v_i_5274_);
                    v___x_5280_ = l_Lean_instHashableFVarId_hash(v_k_5278_);
                    v_h_5281_ = lean_uint64_to_usize(v___x_5280_);
                    v___x_5282_ = 5usize;
                    v___x_5283_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5284_ = 1usize;
                    v___x_5285_ = lean_usize_sub(v_depth_5271_, v___x_5284_);
                    v___x_5286_ = lean_usize_mul(v___x_5282_, v___x_5285_);
                    v_h_5287_ = lean_usize_shift_right(v_h_5281_, v___x_5286_);
                    v___x_5288_ = lean_nat_add(v_i_5274_, v___x_5283_);
                    crate::leanh::lean_dec(v_i_5274_);
                    crate::leanh::lean_inc(v_v_5279_);
                    crate::leanh::lean_inc(v_k_5278_);
                    v___x_5289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_entries_5275_, v_h_5287_, v_depth_5271_, v_k_5278_, v_v_5279_);
                    v_i_5274_ = v___x_5288_;
                    v_entries_5275_ = v___x_5289_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_depth_5291_: *mut crate::leanh::LeanObject,
    mut v_keys_5292_: *mut crate::leanh::LeanObject,
    mut v_vals_5293_: *mut crate::leanh::LeanObject,
    mut v_i_5294_: *mut crate::leanh::LeanObject,
    mut v_entries_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5296_: usize = 0;
    let mut v_res_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5296_ = crate::leanh::lean_unbox_usize(v_depth_5291_);
    crate::leanh::lean_dec(v_depth_5291_);
    v_res_5297_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_boxed_5296_, v_keys_5292_, v_vals_5293_, v_i_5294_, v_entries_5295_);
    crate::leanh::lean_dec_ref(v_vals_5293_);
    crate::leanh::lean_dec_ref(v_keys_5292_);
    return v_res_5297_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(
    mut v_x_5298_: *mut crate::leanh::LeanObject,
    mut v_x_5299_: *mut crate::leanh::LeanObject,
    mut v_x_5300_: *mut crate::leanh::LeanObject,
    mut v_x_5301_: *mut crate::leanh::LeanObject,
    mut v_x_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6248__boxed_5303_: usize = 0;
    let mut v_x_6249__boxed_5304_: usize = 0;
    let mut v_res_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6248__boxed_5303_ = crate::leanh::lean_unbox_usize(v_x_5299_);
    crate::leanh::lean_dec(v_x_5299_);
    v_x_6249__boxed_5304_ = crate::leanh::lean_unbox_usize(v_x_5300_);
    crate::leanh::lean_dec(v_x_5300_);
    v_res_5305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_5298_, v_x_6248__boxed_5303_, v_x_6249__boxed_5304_, v_x_5301_, v_x_5302_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(
    mut v_x_5306_: *mut crate::leanh::LeanObject,
    mut v_x_5307_: *mut crate::leanh::LeanObject,
    mut v_x_5308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5309_: u64 = 0;
    let mut v___x_5310_: usize = 0;
    let mut v___x_5311_: usize = 0;
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5309_ = l_Lean_instHashableFVarId_hash(v_x_5307_);
    v___x_5310_ = lean_uint64_to_usize(v___x_5309_);
    v___x_5311_ = 1usize;
    v___x_5312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_5306_, v___x_5310_, v___x_5311_, v_x_5307_, v_x_5308_);
    return v___x_5312_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(
    mut v_keys_5313_: *mut crate::leanh::LeanObject,
    mut v_i_5314_: *mut crate::leanh::LeanObject,
    mut v_k_5315_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: u8 = 0;
    let mut v_k_x27_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: u8 = 0;
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5316_ = lean_array_get_size(v_keys_5313_);
                v___x_5317_ = lean_nat_dec_lt(v_i_5314_, v___x_5316_);
                if v___x_5317_ == 0 {
                    crate::leanh::lean_dec(v_i_5314_);
                    return v___x_5317_;
                } else {
                    v_k_x27_5318_ = lean_array_fget_borrowed(v_keys_5313_, v_i_5314_);
                    v___x_5319_ = l_Lean_instBEqFVarId_beq(v_k_5315_, v_k_x27_5318_);
                    if v___x_5319_ == 0 {
                        v___x_5320_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5321_ = lean_nat_add(v_i_5314_, v___x_5320_);
                        crate::leanh::lean_dec(v_i_5314_);
                        v_i_5314_ = v___x_5321_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_5314_);
                        return v___x_5319_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_keys_5323_: *mut crate::leanh::LeanObject,
    mut v_i_5324_: *mut crate::leanh::LeanObject,
    mut v_k_5325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5326_: u8 = 0;
    let mut v_r_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5326_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_5323_, v_i_5324_, v_k_5325_);
    crate::leanh::lean_dec(v_k_5325_);
    crate::leanh::lean_dec_ref(v_keys_5323_);
    v_r_5327_ = crate::leanh::lean_box((v_res_5326_) as usize);
    return v_r_5327_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(
    mut v_x_5328_: *mut crate::leanh::LeanObject,
    mut v_x_5329_: usize,
    mut v_x_5330_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: usize = 0;
    let mut v___x_5334_: usize = 0;
    let mut v___x_5335_: usize = 0;
    let mut v_j_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: u8 = 0;
    let mut v_node_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: usize = 0;
    let mut v___x_5343_: u8 = 0;
    let mut v_ks_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5328_) == 0 {
                    v_es_5331_ = crate::leanh::lean_ctor_get(v_x_5328_, 0);
                    v___x_5332_ = crate::leanh::lean_box(2);
                    v___x_5333_ = 5usize;
                    v___x_5334_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1);
                    v___x_5335_ = lean_usize_land(v_x_5329_, v___x_5334_);
                    v_j_5336_ = lean_usize_to_nat(v___x_5335_);
                    v___x_5337_ = lean_array_get_borrowed(v___x_5332_, v_es_5331_, v_j_5336_);
                    crate::leanh::lean_dec(v_j_5336_);
                    match crate::leanh::lean_obj_tag(v___x_5337_) {
                        0 => {
                            v_key_5338_ = crate::leanh::lean_ctor_get(v___x_5337_, 0);
                            v___x_5339_ = l_Lean_instBEqFVarId_beq(v_x_5330_, v_key_5338_);
                            return v___x_5339_;
                        }
                        1 => {
                            v_node_5340_ = crate::leanh::lean_ctor_get(v___x_5337_, 0);
                            v___x_5341_ = lean_usize_shift_right(v_x_5329_, v___x_5333_);
                            v_x_5328_ = v_node_5340_;
                            v_x_5329_ = v___x_5341_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5343_ = 0;
                            return v___x_5343_;
                        }
                    }
                } else {
                    v_ks_5344_ = crate::leanh::lean_ctor_get(v_x_5328_, 0);
                    v___x_5345_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5346_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_ks_5344_, v___x_5345_, v_x_5330_);
                    return v___x_5346_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(
    mut v_x_5347_: *mut crate::leanh::LeanObject,
    mut v_x_5348_: *mut crate::leanh::LeanObject,
    mut v_x_5349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6442__boxed_5350_: usize = 0;
    let mut v_res_5351_: u8 = 0;
    let mut v_r_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6442__boxed_5350_ = crate::leanh::lean_unbox_usize(v_x_5348_);
    crate::leanh::lean_dec(v_x_5348_);
    v_res_5351_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_5347_, v_x_6442__boxed_5350_, v_x_5349_);
    crate::leanh::lean_dec(v_x_5349_);
    crate::leanh::lean_dec_ref(v_x_5347_);
    v_r_5352_ = crate::leanh::lean_box((v_res_5351_) as usize);
    return v_r_5352_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(
    mut v_x_5353_: *mut crate::leanh::LeanObject,
    mut v_x_5354_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5355_: u64 = 0;
    let mut v___x_5356_: usize = 0;
    let mut v___x_5357_: u8 = 0;
    v___x_5355_ = l_Lean_instHashableFVarId_hash(v_x_5354_);
    v___x_5356_ = lean_uint64_to_usize(v___x_5355_);
    v___x_5357_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_5353_, v___x_5356_, v_x_5354_);
    return v___x_5357_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(
    mut v_x_5358_: *mut crate::leanh::LeanObject,
    mut v_x_5359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5360_: u8 = 0;
    let mut v_r_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5360_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_5358_, v_x_5359_);
    crate::leanh::lean_dec(v_x_5359_);
    crate::leanh::lean_dec_ref(v_x_5358_);
    v_r_5361_ = crate::leanh::lean_box((v_res_5360_) as usize);
    return v_r_5361_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5363_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2;
    v___x_5364_ = crate::leanh::lean_unsigned_to_nat(59);
    v___x_5365_ = crate::leanh::lean_unsigned_to_nat(281);
    v___x_5366_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0;
    v___x_5367_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4;
    v___x_5368_ = l_mkPanicMessageWithDecl(
        v___x_5367_,
        v___x_5366_,
        v___x_5365_,
        v___x_5364_,
        v___x_5363_,
    );
    return v___x_5368_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(
    mut v_c_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
    mut v_a_5371_: *mut crate::leanh::LeanObject,
    mut v_a_5372_: *mut crate::leanh::LeanObject,
    mut v_a_5373_: *mut crate::leanh::LeanObject,
    mut v_a_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5382_: u8 = 0;
    let mut v___x_5383_: usize = 0;
    let mut v___x_5384_: usize = 0;
    let mut v___x_5385_: u8 = 0;
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5388_: u8 = 0;
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5395_: u8 = 0;
    let mut v_unused_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5401_: u8 = 0;
    let mut v_decl_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: u8 = 0;
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___y_5418_: u8 = 0;
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v_unused_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: usize = 0;
    let mut v___x_5435_: usize = 0;
    let mut v___x_5436_: u8 = 0;
    let mut v___x_5437_: usize = 0;
    let mut v___x_5438_: usize = 0;
    let mut v___x_5439_: u8 = 0;
    let mut v_isSharedCheck_5440_: u8 = 0;
    let mut v_a_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5444_: u8 = 0;
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5448_: u8 = 0;
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5457_: u8 = 0;
    let mut v_alreadyFound_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relaxedReuse_5459_: u8 = 0;
    let mut v_ownedness_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: u8 = 0;
    let mut v___x_5462_: u8 = 0;
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: u8 = 0;
    let mut v___x_5466_: u8 = 0;
    let mut v___x_5467_: u8 = 0;
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5471_: usize = 0;
    let mut v___x_5472_: usize = 0;
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5477_: u8 = 0;
    let mut v___x_5478_: usize = 0;
    let mut v___x_5479_: usize = 0;
    let mut v___x_5480_: u8 = 0;
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5483_: u8 = 0;
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5493_: u8 = 0;
    let mut v_unused_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5498_: u8 = 0;
    let mut v_a_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5502_: u8 = 0;
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut v_isSharedCheck_5507_: u8 = 0;
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5519_: usize = 0;
    let mut v___x_5520_: usize = 0;
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut v_unused_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5539_: u8 = 0;
    let mut v_fvarId_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5551_: usize = 0;
    let mut v___x_5552_: usize = 0;
    let mut v___x_5553_: u8 = 0;
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5556_: u8 = 0;
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5563_: u8 = 0;
    let mut v_unused_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5573_: u8 = 0;
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_c_5369_) {
                0 => {
                    v_decl_5376_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                    v_k_5377_ = crate::leanh::lean_ctor_get(v_c_5369_, 1);
                    crate::leanh::lean_inc_ref(v_k_5377_);
                    v___x_5378_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_5377_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
                    if crate::leanh::lean_obj_tag(v___x_5378_) == 0 {
                        v_a_5379_ = crate::leanh::lean_ctor_get(v___x_5378_, 0);
                        v_isSharedCheck_5401_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5378_)) as u8;
                        if v_isSharedCheck_5401_ == 0 {
                            v___x_5381_ = v___x_5378_;
                            v_isShared_5382_ = v_isSharedCheck_5401_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5379_);
                            crate::leanh::lean_dec(v___x_5378_);
                            v___x_5381_ = crate::leanh::lean_box(0);
                            v_isShared_5382_ = v_isSharedCheck_5401_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_c_5369_, 2);
                        return v___x_5378_;
                    }
                }
                2 => {
                    v_decl_5402_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                    v_k_5403_ = crate::leanh::lean_ctor_get(v_c_5369_, 1);
                    v_params_5404_ = crate::leanh::lean_ctor_get(v_decl_5402_, 2);
                    v_type_5405_ = crate::leanh::lean_ctor_get(v_decl_5402_, 3);
                    v_value_5406_ = crate::leanh::lean_ctor_get(v_decl_5402_, 4);
                    crate::leanh::lean_inc_ref(v_value_5406_);
                    v___x_5407_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_value_5406_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
                    if crate::leanh::lean_obj_tag(v___x_5407_) == 0 {
                        v_a_5408_ = crate::leanh::lean_ctor_get(v___x_5407_, 0);
                        crate::leanh::lean_inc(v_a_5408_);
                        crate::leanh::lean_dec_ref_known(v___x_5407_, 1);
                        v___x_5409_ = 1;
                        crate::leanh::lean_inc_ref(v_params_5404_);
                        crate::leanh::lean_inc_ref(v_type_5405_);
                        crate::leanh::lean_inc_ref(v_decl_5402_);
                        v___x_5410_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5409_, v_decl_5402_, v_type_5405_, v_params_5404_, v_a_5408_, v_a_5372_);
                        if crate::leanh::lean_obj_tag(v___x_5410_) == 0 {
                            v_a_5411_ = crate::leanh::lean_ctor_get(v___x_5410_, 0);
                            crate::leanh::lean_inc(v_a_5411_);
                            crate::leanh::lean_dec_ref_known(v___x_5410_, 1);
                            crate::leanh::lean_inc_ref(v_k_5403_);
                            v___x_5412_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_5403_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
                            if crate::leanh::lean_obj_tag(v___x_5412_) == 0 {
                                v_a_5413_ = crate::leanh::lean_ctor_get(v___x_5412_, 0);
                                v_isSharedCheck_5440_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5412_)) as u8;
                                if v_isSharedCheck_5440_ == 0 {
                                    v___x_5415_ = v___x_5412_;
                                    v_isShared_5416_ = v_isSharedCheck_5440_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5413_);
                                    crate::leanh::lean_dec(v___x_5412_);
                                    v___x_5415_ = crate::leanh::lean_box(0);
                                    v_isShared_5416_ = v_isSharedCheck_5440_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5411_);
                                crate::leanh::lean_dec_ref_known(v_c_5369_, 2);
                                return v___x_5412_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_c_5369_, 2);
                            v_a_5441_ = crate::leanh::lean_ctor_get(v___x_5410_, 0);
                            v_isSharedCheck_5448_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5410_)) as u8;
                            if v_isSharedCheck_5448_ == 0 {
                                v___x_5443_ = v___x_5410_;
                                v_isShared_5444_ = v_isSharedCheck_5448_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5441_);
                                crate::leanh::lean_dec(v___x_5410_);
                                v___x_5443_ = crate::leanh::lean_box(0);
                                v_isShared_5444_ = v_isSharedCheck_5448_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_c_5369_, 2);
                        return v___x_5407_;
                    }
                }
                3 => {
                    v___x_5449_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5449_, 0, v_c_5369_);
                    return v___x_5449_;
                }
                4 => {
                    v_cases_5450_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                    crate::leanh::lean_inc_ref(v_cases_5450_);
                    v_typeName_5451_ = crate::leanh::lean_ctor_get(v_cases_5450_, 0);
                    v_resultType_5452_ = crate::leanh::lean_ctor_get(v_cases_5450_, 1);
                    v_discr_5453_ = crate::leanh::lean_ctor_get(v_cases_5450_, 2);
                    v_alts_5454_ = crate::leanh::lean_ctor_get(v_cases_5450_, 3);
                    v_isSharedCheck_5507_ = (!crate::leanh::lean_is_exclusive(v_cases_5450_)) as u8;
                    if v_isSharedCheck_5507_ == 0 {
                        v___x_5456_ = v_cases_5450_;
                        v_isShared_5457_ = v_isSharedCheck_5507_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_5454_);
                        crate::leanh::lean_inc(v_discr_5453_);
                        crate::leanh::lean_inc(v_resultType_5452_);
                        crate::leanh::lean_inc(v_typeName_5451_);
                        crate::leanh::lean_dec(v_cases_5450_);
                        v___x_5456_ = crate::leanh::lean_box(0);
                        v_isShared_5457_ = v_isSharedCheck_5507_;
                        state = 14;
                        continue;
                    }
                }
                5 => {
                    v___x_5508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5508_, 0, v_c_5369_);
                    return v___x_5508_;
                }
                6 => {
                    v___x_5509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5509_, 0, v_c_5369_);
                    return v___x_5509_;
                }
                8 => {
                    v_fvarId_5510_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                    v_i_5511_ = crate::leanh::lean_ctor_get(v_c_5369_, 1);
                    v_y_5512_ = crate::leanh::lean_ctor_get(v_c_5369_, 2);
                    v_k_5513_ = crate::leanh::lean_ctor_get(v_c_5369_, 3);
                    crate::leanh::lean_inc_ref(v_k_5513_);
                    v___x_5514_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_5513_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
                    if crate::leanh::lean_obj_tag(v___x_5514_) == 0 {
                        v_a_5515_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                        v_isSharedCheck_5539_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5514_)) as u8;
                        if v_isSharedCheck_5539_ == 0 {
                            v___x_5517_ = v___x_5514_;
                            v_isShared_5518_ = v_isSharedCheck_5539_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5515_);
                            crate::leanh::lean_dec(v___x_5514_);
                            v___x_5517_ = crate::leanh::lean_box(0);
                            v_isShared_5518_ = v_isSharedCheck_5539_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_c_5369_, 4);
                        return v___x_5514_;
                    }
                }
                9 => {
                    v_fvarId_5540_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                    v_i_5541_ = crate::leanh::lean_ctor_get(v_c_5369_, 1);
                    v_offset_5542_ = crate::leanh::lean_ctor_get(v_c_5369_, 2);
                    v_y_5543_ = crate::leanh::lean_ctor_get(v_c_5369_, 3);
                    v_ty_5544_ = crate::leanh::lean_ctor_get(v_c_5369_, 4);
                    v_k_5545_ = crate::leanh::lean_ctor_get(v_c_5369_, 5);
                    crate::leanh::lean_inc_ref(v_k_5545_);
                    v___x_5546_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_5545_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
                    if crate::leanh::lean_obj_tag(v___x_5546_) == 0 {
                        v_a_5547_ = crate::leanh::lean_ctor_get(v___x_5546_, 0);
                        v_isSharedCheck_5573_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5546_)) as u8;
                        if v_isSharedCheck_5573_ == 0 {
                            v___x_5549_ = v___x_5546_;
                            v_isShared_5550_ = v_isSharedCheck_5573_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5547_);
                            crate::leanh::lean_dec(v___x_5546_);
                            v___x_5549_ = crate::leanh::lean_box(0);
                            v_isShared_5550_ = v_isSharedCheck_5573_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_c_5369_, 6);
                        return v___x_5546_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_c_5369_);
                    v___x_5574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
                    v___x_5575_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v___x_5574_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
                    return v___x_5575_;
                }
            },
            1 => {
                v___x_5383_ = lean_ptr_addr(v_k_5377_);
                v___x_5384_ = lean_ptr_addr(v_a_5379_);
                v___x_5385_ = lean_usize_dec_eq(v___x_5383_, v___x_5384_);
                if v___x_5385_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_5376_);
                    v_isSharedCheck_5395_ = (!crate::leanh::lean_is_exclusive(v_c_5369_)) as u8;
                    if v_isSharedCheck_5395_ == 0 {
                        v_unused_5396_ = crate::leanh::lean_ctor_get(v_c_5369_, 1);
                        crate::leanh::lean_dec(v_unused_5396_);
                        v_unused_5397_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                        crate::leanh::lean_dec(v_unused_5397_);
                        v___x_5387_ = v_c_5369_;
                        v_isShared_5388_ = v_isSharedCheck_5395_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_5369_);
                        v___x_5387_ = crate::leanh::lean_box(0);
                        v_isShared_5388_ = v_isSharedCheck_5395_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5379_);
                    if v_isShared_5382_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5381_, 0, v_c_5369_);
                        v___x_5399_ = v___x_5381_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5400_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_c_5369_);
                        v___x_5399_ = v_reuseFailAlloc_5400_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5387_, 1, v_a_5379_);
                    v___x_5390_ = v___x_5387_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5394_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_decl_5376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5394_, 1, v_a_5379_);
                    v___x_5390_ = v_reuseFailAlloc_5394_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5382_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5381_, 0, v___x_5390_);
                    v___x_5392_ = v___x_5381_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5393_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5390_);
                    v___x_5392_ = v_reuseFailAlloc_5393_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5392_;
            }
            5 => {
                return v___x_5399_;
            }
            6 => {
                v___x_5434_ = lean_ptr_addr(v_k_5403_);
                v___x_5435_ = lean_ptr_addr(v_a_5413_);
                v___x_5436_ = lean_usize_dec_eq(v___x_5434_, v___x_5435_);
                if v___x_5436_ == 0 {
                    v___y_5418_ = v___x_5436_;
                    state = 7;
                    continue;
                } else {
                    v___x_5437_ = lean_ptr_addr(v_decl_5402_);
                    v___x_5438_ = lean_ptr_addr(v_a_5411_);
                    v___x_5439_ = lean_usize_dec_eq(v___x_5437_, v___x_5438_);
                    v___y_5418_ = v___x_5439_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_5418_ == 0 {
                    v_isSharedCheck_5428_ = (!crate::leanh::lean_is_exclusive(v_c_5369_)) as u8;
                    if v_isSharedCheck_5428_ == 0 {
                        v_unused_5429_ = crate::leanh::lean_ctor_get(v_c_5369_, 1);
                        crate::leanh::lean_dec(v_unused_5429_);
                        v_unused_5430_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                        crate::leanh::lean_dec(v_unused_5430_);
                        v___x_5420_ = v_c_5369_;
                        v_isShared_5421_ = v_isSharedCheck_5428_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_5369_);
                        v___x_5420_ = crate::leanh::lean_box(0);
                        v_isShared_5421_ = v_isSharedCheck_5428_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5413_);
                    crate::leanh::lean_dec(v_a_5411_);
                    if v_isShared_5416_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5415_, 0, v_c_5369_);
                        v___x_5432_ = v___x_5415_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_c_5369_);
                        v___x_5432_ = v_reuseFailAlloc_5433_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5421_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5420_, 1, v_a_5413_);
                    crate::leanh::lean_ctor_set(v___x_5420_, 0, v_a_5411_);
                    v___x_5423_ = v___x_5420_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5427_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 1, v_a_5413_);
                    v___x_5423_ = v_reuseFailAlloc_5427_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5416_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5415_, 0, v___x_5423_);
                    v___x_5425_ = v___x_5415_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5423_);
                    v___x_5425_ = v_reuseFailAlloc_5426_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5425_;
            }
            11 => {
                return v___x_5432_;
            }
            12 => {
                if v_isShared_5444_ == 0 {
                    v___x_5446_ = v___x_5443_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5447_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_a_5441_);
                    v___x_5446_ = v_reuseFailAlloc_5447_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5446_;
            }
            14 => {
                v_alreadyFound_5458_ = crate::leanh::lean_ctor_get(v_a_5370_, 0);
                v_relaxedReuse_5459_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5370_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_ownedness_5460_ = crate::leanh::lean_ctor_get(v_a_5370_, 1);
                v___x_5461_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_alreadyFound_5458_, v_discr_5453_);
                v___x_5462_ = 0;
                v___x_5463_ = crate::leanh::lean_box((v___x_5462_) as usize);
                v___x_5464_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_ownedness_5460_, v_discr_5453_, v___x_5463_);
                crate::leanh::lean_dec(v___x_5463_);
                v___x_5465_ = 1;
                v___x_5466_ = (crate::leanh::lean_unbox(v___x_5464_) as u8);
                crate::leanh::lean_dec(v___x_5464_);
                v___x_5467_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_5466_, v___x_5465_);
                v___x_5468_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_discr_5453_, 2);
                crate::leanh::lean_inc_ref(v_alreadyFound_5458_);
                v___x_5469_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_alreadyFound_5458_, v_discr_5453_, v___x_5468_);
                crate::leanh::lean_inc_ref(v_ownedness_5460_);
                v___x_5470_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5470_, 0, v___x_5469_);
                crate::leanh::lean_ctor_set(v___x_5470_, 1, v_ownedness_5460_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5470_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_relaxedReuse_5459_,
                );
                v_sz_5471_ = lean_array_size(v_alts_5454_);
                v___x_5472_ = 0usize;
                crate::leanh::lean_inc_ref(v_alts_5454_);
                v___x_5473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_5467_, v_discr_5453_, v___x_5461_, v_sz_5471_, v___x_5472_, v_alts_5454_, v___x_5470_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
                crate::leanh::lean_dec_ref_known(v___x_5470_, 2);
                if crate::leanh::lean_obj_tag(v___x_5473_) == 0 {
                    v_a_5474_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                    v_isSharedCheck_5498_ = (!crate::leanh::lean_is_exclusive(v___x_5473_)) as u8;
                    if v_isSharedCheck_5498_ == 0 {
                        v___x_5476_ = v___x_5473_;
                        v_isShared_5477_ = v_isSharedCheck_5498_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5474_);
                        crate::leanh::lean_dec(v___x_5473_);
                        v___x_5476_ = crate::leanh::lean_box(0);
                        v_isShared_5477_ = v_isSharedCheck_5498_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5456_);
                    crate::leanh::lean_dec_ref(v_alts_5454_);
                    crate::leanh::lean_dec(v_discr_5453_);
                    crate::leanh::lean_dec_ref(v_resultType_5452_);
                    crate::leanh::lean_dec(v_typeName_5451_);
                    crate::leanh::lean_dec_ref_known(v_c_5369_, 1);
                    v_a_5499_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                    v_isSharedCheck_5506_ = (!crate::leanh::lean_is_exclusive(v___x_5473_)) as u8;
                    if v_isSharedCheck_5506_ == 0 {
                        v___x_5501_ = v___x_5473_;
                        v_isShared_5502_ = v_isSharedCheck_5506_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5499_);
                        crate::leanh::lean_dec(v___x_5473_);
                        v___x_5501_ = crate::leanh::lean_box(0);
                        v_isShared_5502_ = v_isSharedCheck_5506_;
                        state = 21;
                        continue;
                    }
                }
            }
            15 => {
                v___x_5478_ = lean_ptr_addr(v_alts_5454_);
                crate::leanh::lean_dec_ref(v_alts_5454_);
                v___x_5479_ = lean_ptr_addr(v_a_5474_);
                v___x_5480_ = lean_usize_dec_eq(v___x_5478_, v___x_5479_);
                if v___x_5480_ == 0 {
                    v_isSharedCheck_5493_ = (!crate::leanh::lean_is_exclusive(v_c_5369_)) as u8;
                    if v_isSharedCheck_5493_ == 0 {
                        v_unused_5494_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                        crate::leanh::lean_dec(v_unused_5494_);
                        v___x_5482_ = v_c_5369_;
                        v_isShared_5483_ = v_isSharedCheck_5493_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_5369_);
                        v___x_5482_ = crate::leanh::lean_box(0);
                        v_isShared_5483_ = v_isSharedCheck_5493_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5474_);
                    crate::leanh::lean_del_object(v___x_5456_);
                    crate::leanh::lean_dec(v_discr_5453_);
                    crate::leanh::lean_dec_ref(v_resultType_5452_);
                    crate::leanh::lean_dec(v_typeName_5451_);
                    if v_isShared_5477_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5476_, 0, v_c_5369_);
                        v___x_5496_ = v___x_5476_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_5497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_c_5369_);
                        v___x_5496_ = v_reuseFailAlloc_5497_;
                        state = 20;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_5457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5456_, 3, v_a_5474_);
                    v___x_5485_ = v___x_5456_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_typeName_5451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 1, v_resultType_5452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 2, v_discr_5453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 3, v_a_5474_);
                    v___x_5485_ = v_reuseFailAlloc_5492_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_5483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5482_, 0, v___x_5485_);
                    v___x_5487_ = v___x_5482_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5485_);
                    v___x_5487_ = v_reuseFailAlloc_5491_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_5477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5476_, 0, v___x_5487_);
                    v___x_5489_ = v___x_5476_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5487_);
                    v___x_5489_ = v_reuseFailAlloc_5490_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5489_;
            }
            20 => {
                return v___x_5496_;
            }
            21 => {
                if v_isShared_5502_ == 0 {
                    v___x_5504_ = v___x_5501_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5499_);
                    v___x_5504_ = v_reuseFailAlloc_5505_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5504_;
            }
            23 => {
                v___x_5519_ = lean_ptr_addr(v_k_5513_);
                v___x_5520_ = lean_ptr_addr(v_a_5515_);
                v___x_5521_ = lean_usize_dec_eq(v___x_5519_, v___x_5520_);
                if v___x_5521_ == 0 {
                    crate::leanh::lean_inc(v_y_5512_);
                    crate::leanh::lean_inc(v_i_5511_);
                    crate::leanh::lean_inc(v_fvarId_5510_);
                    v_isSharedCheck_5531_ = (!crate::leanh::lean_is_exclusive(v_c_5369_)) as u8;
                    if v_isSharedCheck_5531_ == 0 {
                        v_unused_5532_ = crate::leanh::lean_ctor_get(v_c_5369_, 3);
                        crate::leanh::lean_dec(v_unused_5532_);
                        v_unused_5533_ = crate::leanh::lean_ctor_get(v_c_5369_, 2);
                        crate::leanh::lean_dec(v_unused_5533_);
                        v_unused_5534_ = crate::leanh::lean_ctor_get(v_c_5369_, 1);
                        crate::leanh::lean_dec(v_unused_5534_);
                        v_unused_5535_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                        crate::leanh::lean_dec(v_unused_5535_);
                        v___x_5523_ = v_c_5369_;
                        v_isShared_5524_ = v_isSharedCheck_5531_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_5369_);
                        v___x_5523_ = crate::leanh::lean_box(0);
                        v_isShared_5524_ = v_isSharedCheck_5531_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5515_);
                    if v_isShared_5518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5517_, 0, v_c_5369_);
                        v___x_5537_ = v___x_5517_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_5538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_c_5369_);
                        v___x_5537_ = v_reuseFailAlloc_5538_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_5524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5523_, 3, v_a_5515_);
                    v___x_5526_ = v___x_5523_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_fvarId_5510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_i_5511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 2, v_y_5512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 3, v_a_5515_);
                    v___x_5526_ = v_reuseFailAlloc_5530_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_5518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5517_, 0, v___x_5526_);
                    v___x_5528_ = v___x_5517_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5526_);
                    v___x_5528_ = v_reuseFailAlloc_5529_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5528_;
            }
            27 => {
                return v___x_5537_;
            }
            28 => {
                v___x_5551_ = lean_ptr_addr(v_k_5545_);
                v___x_5552_ = lean_ptr_addr(v_a_5547_);
                v___x_5553_ = lean_usize_dec_eq(v___x_5551_, v___x_5552_);
                if v___x_5553_ == 0 {
                    crate::leanh::lean_inc_ref(v_ty_5544_);
                    crate::leanh::lean_inc(v_y_5543_);
                    crate::leanh::lean_inc(v_offset_5542_);
                    crate::leanh::lean_inc(v_i_5541_);
                    crate::leanh::lean_inc(v_fvarId_5540_);
                    v_isSharedCheck_5563_ = (!crate::leanh::lean_is_exclusive(v_c_5369_)) as u8;
                    if v_isSharedCheck_5563_ == 0 {
                        v_unused_5564_ = crate::leanh::lean_ctor_get(v_c_5369_, 5);
                        crate::leanh::lean_dec(v_unused_5564_);
                        v_unused_5565_ = crate::leanh::lean_ctor_get(v_c_5369_, 4);
                        crate::leanh::lean_dec(v_unused_5565_);
                        v_unused_5566_ = crate::leanh::lean_ctor_get(v_c_5369_, 3);
                        crate::leanh::lean_dec(v_unused_5566_);
                        v_unused_5567_ = crate::leanh::lean_ctor_get(v_c_5369_, 2);
                        crate::leanh::lean_dec(v_unused_5567_);
                        v_unused_5568_ = crate::leanh::lean_ctor_get(v_c_5369_, 1);
                        crate::leanh::lean_dec(v_unused_5568_);
                        v_unused_5569_ = crate::leanh::lean_ctor_get(v_c_5369_, 0);
                        crate::leanh::lean_dec(v_unused_5569_);
                        v___x_5555_ = v_c_5369_;
                        v_isShared_5556_ = v_isSharedCheck_5563_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_5369_);
                        v___x_5555_ = crate::leanh::lean_box(0);
                        v_isShared_5556_ = v_isSharedCheck_5563_;
                        state = 29;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5547_);
                    if v_isShared_5550_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5549_, 0, v_c_5369_);
                        v___x_5571_ = v___x_5549_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_5572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_c_5369_);
                        v___x_5571_ = v_reuseFailAlloc_5572_;
                        state = 32;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_5556_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5555_, 5, v_a_5547_);
                    v___x_5558_ = v___x_5555_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5562_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_fvarId_5540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 1, v_i_5541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 2, v_offset_5542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 3, v_y_5543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 4, v_ty_5544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 5, v_a_5547_);
                    v___x_5558_ = v_reuseFailAlloc_5562_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_5550_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5549_, 0, v___x_5558_);
                    v___x_5560_ = v___x_5549_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5561_, 0, v___x_5558_);
                    v___x_5560_ = v_reuseFailAlloc_5561_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5560_;
            }
            32 => {
                return v___x_5571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(
    mut v_c_5576_: *mut crate::leanh::LeanObject,
    mut v_a_5577_: *mut crate::leanh::LeanObject,
    mut v_a_5578_: *mut crate::leanh::LeanObject,
    mut v_a_5579_: *mut crate::leanh::LeanObject,
    mut v_a_5580_: *mut crate::leanh::LeanObject,
    mut v_a_5581_: *mut crate::leanh::LeanObject,
    mut v_a_5582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ =
        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(
            v_c_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_,
        );
    crate::leanh::lean_dec(v_a_5581_);
    crate::leanh::lean_dec_ref(v_a_5580_);
    crate::leanh::lean_dec(v_a_5579_);
    crate::leanh::lean_dec_ref(v_a_5578_);
    crate::leanh::lean_dec_ref(v_a_5577_);
    return v_res_5583_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(
    mut v___x_5584_: u8,
    mut v_discr_5585_: *mut crate::leanh::LeanObject,
    mut v___x_5586_: u8,
    mut v_sz_5587_: usize,
    mut v_i_5588_: usize,
    mut v_bs_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: usize = 0;
    let mut v___x_5605_: usize = 0;
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5618_: u8 = 0;
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5624_: u8 = 0;
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v___x_5636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5596_ = lean_usize_dec_lt(v_i_5588_, v_sz_5587_);
                if v___x_5596_ == 0 {
                    crate::leanh::lean_dec(v_discr_5585_);
                    v___x_5597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5597_, 0, v_bs_5589_);
                    return v___x_5597_;
                } else {
                    v___f_5598_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed as *mut core::ffi::c_void, 7, 0);
                    v_v_5599_ = lean_array_uget(v_bs_5589_, v_i_5588_);
                    v___x_5600_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5601_ = lean_array_uset(v_bs_5589_, v_i_5588_, v___x_5600_);
                    v___x_5619_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_v_5599_, v___f_5598_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_);
                    if crate::leanh::lean_obj_tag(v___x_5619_) == 0 {
                        v_a_5620_ = crate::leanh::lean_ctor_get(v___x_5619_, 0);
                        crate::leanh::lean_inc(v_a_5620_);
                        if crate::leanh::lean_obj_tag(v_a_5620_) == 1 {
                            v_info_5621_ = crate::leanh::lean_ctor_get(v_a_5620_, 0);
                            v_code_5622_ = crate::leanh::lean_ctor_get(v_a_5620_, 1);
                            v___x_5636_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_5621_);
                            if v___x_5636_ == 0 {
                                v___y_5624_ = v___x_5586_;
                                state = 5;
                                continue;
                            } else {
                                v___y_5624_ = v___x_5636_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_5620_, 1);
                            v___y_5609_ = v___x_5619_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_5609_ = v___x_5619_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5604_ = 1usize;
                v___x_5605_ = lean_usize_add(v_i_5588_, v___x_5604_);
                v___x_5606_ = lean_array_uset(v_bs_x27_5601_, v_i_5588_, v_a_5603_);
                v_i_5588_ = v___x_5605_;
                v_bs_5589_ = v___x_5606_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_5609_) == 0 {
                    v_a_5610_ = crate::leanh::lean_ctor_get(v___y_5609_, 0);
                    crate::leanh::lean_inc(v_a_5610_);
                    crate::leanh::lean_dec_ref_known(v___y_5609_, 1);
                    v_a_5603_ = v_a_5610_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_5601_);
                    crate::leanh::lean_dec(v_discr_5585_);
                    v_a_5611_ = crate::leanh::lean_ctor_get(v___y_5609_, 0);
                    v_isSharedCheck_5618_ = (!crate::leanh::lean_is_exclusive(v___y_5609_)) as u8;
                    if v_isSharedCheck_5618_ == 0 {
                        v___x_5613_ = v___y_5609_;
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5611_);
                        crate::leanh::lean_dec(v___y_5609_);
                        v___x_5613_ = crate::leanh::lean_box(0);
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5614_ == 0 {
                    v___x_5616_ = v___x_5613_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
                    v___x_5616_ = v_reuseFailAlloc_5617_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5616_;
            }
            5 => {
                if v___y_5624_ == 0 {
                    if v___x_5584_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5619_, 1);
                        crate::leanh::lean_inc_ref(v_code_5622_);
                        crate::leanh::lean_inc_ref(v_info_5621_);
                        crate::leanh::lean_inc(v_discr_5585_);
                        v___x_5625_ =
                            l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(
                                v_discr_5585_,
                                v_info_5621_,
                                v_code_5622_,
                                v___y_5590_,
                                v___y_5591_,
                                v___y_5592_,
                                v___y_5593_,
                                v___y_5594_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_5625_) == 0 {
                            v_a_5626_ = crate::leanh::lean_ctor_get(v___x_5625_, 0);
                            crate::leanh::lean_inc(v_a_5626_);
                            crate::leanh::lean_dec_ref_known(v___x_5625_, 1);
                            v___x_5627_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5620_, v_a_5626_);
                            v_a_5603_ = v___x_5627_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_5620_, 2);
                            crate::leanh::lean_dec_ref(v_bs_x27_5601_);
                            crate::leanh::lean_dec(v_discr_5585_);
                            v_a_5628_ = crate::leanh::lean_ctor_get(v___x_5625_, 0);
                            v_isSharedCheck_5635_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5625_)) as u8;
                            if v_isSharedCheck_5635_ == 0 {
                                v___x_5630_ = v___x_5625_;
                                v_isShared_5631_ = v_isSharedCheck_5635_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5628_);
                                crate::leanh::lean_dec(v___x_5625_);
                                v___x_5630_ = crate::leanh::lean_box(0);
                                v_isShared_5631_ = v_isSharedCheck_5635_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_5620_, 2);
                        v___y_5609_ = v___x_5619_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_5620_, 2);
                    v___y_5609_ = v___x_5619_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_5631_ == 0 {
                    v___x_5633_ = v___x_5630_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
                    v___x_5633_ = v_reuseFailAlloc_5634_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(
    mut v___x_5637_: *mut crate::leanh::LeanObject,
    mut v_discr_5638_: *mut crate::leanh::LeanObject,
    mut v___x_5639_: *mut crate::leanh::LeanObject,
    mut v_sz_5640_: *mut crate::leanh::LeanObject,
    mut v_i_5641_: *mut crate::leanh::LeanObject,
    mut v_bs_5642_: *mut crate::leanh::LeanObject,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
    mut v___y_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6505__boxed_5649_: u8 = 0;
    let mut v___x_6507__boxed_5650_: u8 = 0;
    let mut v_sz_boxed_5651_: usize = 0;
    let mut v_i_boxed_5652_: usize = 0;
    let mut v_res_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6505__boxed_5649_ = (crate::leanh::lean_unbox(v___x_5637_) as u8);
    v___x_6507__boxed_5650_ = (crate::leanh::lean_unbox(v___x_5639_) as u8);
    v_sz_boxed_5651_ = crate::leanh::lean_unbox_usize(v_sz_5640_);
    crate::leanh::lean_dec(v_sz_5640_);
    v_i_boxed_5652_ = crate::leanh::lean_unbox_usize(v_i_5641_);
    crate::leanh::lean_dec(v_i_5641_);
    v_res_5653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_6505__boxed_5649_, v_discr_5638_, v___x_6507__boxed_5650_, v_sz_boxed_5651_, v_i_boxed_5652_, v_bs_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
    crate::leanh::lean_dec(v___y_5647_);
    crate::leanh::lean_dec_ref(v___y_5646_);
    crate::leanh::lean_dec(v___y_5645_);
    crate::leanh::lean_dec_ref(v___y_5644_);
    crate::leanh::lean_dec_ref(v___y_5643_);
    return v_res_5653_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(
    mut v_00_u03b2_5654_: *mut crate::leanh::LeanObject,
    mut v_x_5655_: *mut crate::leanh::LeanObject,
    mut v_x_5656_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5657_: u8 = 0;
    v___x_5657_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_5655_, v_x_5656_);
    return v___x_5657_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(
    mut v_00_u03b2_5658_: *mut crate::leanh::LeanObject,
    mut v_x_5659_: *mut crate::leanh::LeanObject,
    mut v_x_5660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5661_: u8 = 0;
    let mut v_r_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5661_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(v_00_u03b2_5658_, v_x_5659_, v_x_5660_);
    crate::leanh::lean_dec(v_x_5660_);
    crate::leanh::lean_dec_ref(v_x_5659_);
    v_r_5662_ = crate::leanh::lean_box((v_res_5661_) as usize);
    return v_r_5662_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(
    mut v_00_u03b2_5663_: *mut crate::leanh::LeanObject,
    mut v_m_5664_: *mut crate::leanh::LeanObject,
    mut v_a_5665_: *mut crate::leanh::LeanObject,
    mut v_fallback_5666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_5664_, v_a_5665_, v_fallback_5666_);
    return v___x_5667_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(
    mut v_00_u03b2_5668_: *mut crate::leanh::LeanObject,
    mut v_m_5669_: *mut crate::leanh::LeanObject,
    mut v_a_5670_: *mut crate::leanh::LeanObject,
    mut v_fallback_5671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5672_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(v_00_u03b2_5668_, v_m_5669_, v_a_5670_, v_fallback_5671_);
    crate::leanh::lean_dec(v_fallback_5671_);
    crate::leanh::lean_dec(v_a_5670_);
    crate::leanh::lean_dec_ref(v_m_5669_);
    return v_res_5672_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(
    mut v_00_u03b2_5673_: *mut crate::leanh::LeanObject,
    mut v_x_5674_: *mut crate::leanh::LeanObject,
    mut v_x_5675_: *mut crate::leanh::LeanObject,
    mut v_x_5676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5677_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_x_5674_, v_x_5675_, v_x_5676_);
    return v___x_5677_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(
    mut v_00_u03b2_5678_: *mut crate::leanh::LeanObject,
    mut v_x_5679_: *mut crate::leanh::LeanObject,
    mut v_x_5680_: usize,
    mut v_x_5681_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5682_: u8 = 0;
    v___x_5682_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_5679_, v_x_5680_, v_x_5681_);
    return v___x_5682_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(
    mut v_00_u03b2_5683_: *mut crate::leanh::LeanObject,
    mut v_x_5684_: *mut crate::leanh::LeanObject,
    mut v_x_5685_: *mut crate::leanh::LeanObject,
    mut v_x_5686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7056__boxed_5687_: usize = 0;
    let mut v_res_5688_: u8 = 0;
    let mut v_r_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7056__boxed_5687_ = crate::leanh::lean_unbox_usize(v_x_5685_);
    crate::leanh::lean_dec(v_x_5685_);
    v_res_5688_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(v_00_u03b2_5683_, v_x_5684_, v_x_7056__boxed_5687_, v_x_5686_);
    crate::leanh::lean_dec(v_x_5686_);
    crate::leanh::lean_dec_ref(v_x_5684_);
    v_r_5689_ = crate::leanh::lean_box((v_res_5688_) as usize);
    return v_r_5689_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(
    mut v_00_u03b2_5690_: *mut crate::leanh::LeanObject,
    mut v_a_5691_: *mut crate::leanh::LeanObject,
    mut v_fallback_5692_: *mut crate::leanh::LeanObject,
    mut v_x_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5694_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_5691_, v_fallback_5692_, v_x_5693_);
    return v___x_5694_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(
    mut v_00_u03b2_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
    mut v_fallback_5697_: *mut crate::leanh::LeanObject,
    mut v_x_5698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5699_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(v_00_u03b2_5695_, v_a_5696_, v_fallback_5697_, v_x_5698_);
    crate::leanh::lean_dec(v_x_5698_);
    crate::leanh::lean_dec(v_fallback_5697_);
    crate::leanh::lean_dec(v_a_5696_);
    return v_res_5699_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(
    mut v_00_u03b2_5700_: *mut crate::leanh::LeanObject,
    mut v_x_5701_: *mut crate::leanh::LeanObject,
    mut v_x_5702_: usize,
    mut v_x_5703_: usize,
    mut v_x_5704_: *mut crate::leanh::LeanObject,
    mut v_x_5705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_5701_, v_x_5702_, v_x_5703_, v_x_5704_, v_x_5705_);
    return v___x_5706_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(
    mut v_00_u03b2_5707_: *mut crate::leanh::LeanObject,
    mut v_x_5708_: *mut crate::leanh::LeanObject,
    mut v_x_5709_: *mut crate::leanh::LeanObject,
    mut v_x_5710_: *mut crate::leanh::LeanObject,
    mut v_x_5711_: *mut crate::leanh::LeanObject,
    mut v_x_5712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7072__boxed_5713_: usize = 0;
    let mut v_x_7073__boxed_5714_: usize = 0;
    let mut v_res_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7072__boxed_5713_ = crate::leanh::lean_unbox_usize(v_x_5709_);
    crate::leanh::lean_dec(v_x_5709_);
    v_x_7073__boxed_5714_ = crate::leanh::lean_unbox_usize(v_x_5710_);
    crate::leanh::lean_dec(v_x_5710_);
    v_res_5715_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(v_00_u03b2_5707_, v_x_5708_, v_x_7072__boxed_5713_, v_x_7073__boxed_5714_, v_x_5711_, v_x_5712_);
    return v_res_5715_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5716_: *mut crate::leanh::LeanObject,
    mut v_keys_5717_: *mut crate::leanh::LeanObject,
    mut v_vals_5718_: *mut crate::leanh::LeanObject,
    mut v_heq_5719_: *mut crate::leanh::LeanObject,
    mut v_i_5720_: *mut crate::leanh::LeanObject,
    mut v_k_5721_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5722_: u8 = 0;
    v___x_5722_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_5717_, v_i_5720_, v_k_5721_);
    return v___x_5722_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5723_: *mut crate::leanh::LeanObject,
    mut v_keys_5724_: *mut crate::leanh::LeanObject,
    mut v_vals_5725_: *mut crate::leanh::LeanObject,
    mut v_heq_5726_: *mut crate::leanh::LeanObject,
    mut v_i_5727_: *mut crate::leanh::LeanObject,
    mut v_k_5728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5729_: u8 = 0;
    let mut v_r_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5729_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(v_00_u03b2_5723_, v_keys_5724_, v_vals_5725_, v_heq_5726_, v_i_5727_, v_k_5728_);
    crate::leanh::lean_dec(v_k_5728_);
    crate::leanh::lean_dec_ref(v_vals_5725_);
    crate::leanh::lean_dec_ref(v_keys_5724_);
    v_r_5730_ = crate::leanh::lean_box((v_res_5729_) as usize);
    return v_r_5730_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(
    mut v_00_u03b2_5731_: *mut crate::leanh::LeanObject,
    mut v_n_5732_: *mut crate::leanh::LeanObject,
    mut v_k_5733_: *mut crate::leanh::LeanObject,
    mut v_v_5734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5735_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v_n_5732_, v_k_5733_, v_v_5734_);
    return v___x_5735_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(
    mut v_00_u03b2_5736_: *mut crate::leanh::LeanObject,
    mut v_depth_5737_: usize,
    mut v_keys_5738_: *mut crate::leanh::LeanObject,
    mut v_vals_5739_: *mut crate::leanh::LeanObject,
    mut v_heq_5740_: *mut crate::leanh::LeanObject,
    mut v_i_5741_: *mut crate::leanh::LeanObject,
    mut v_entries_5742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_5737_, v_keys_5738_, v_vals_5739_, v_i_5741_, v_entries_5742_);
    return v___x_5743_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_5744_: *mut crate::leanh::LeanObject,
    mut v_depth_5745_: *mut crate::leanh::LeanObject,
    mut v_keys_5746_: *mut crate::leanh::LeanObject,
    mut v_vals_5747_: *mut crate::leanh::LeanObject,
    mut v_heq_5748_: *mut crate::leanh::LeanObject,
    mut v_i_5749_: *mut crate::leanh::LeanObject,
    mut v_entries_5750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5751_: usize = 0;
    let mut v_res_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5751_ = crate::leanh::lean_unbox_usize(v_depth_5745_);
    crate::leanh::lean_dec(v_depth_5745_);
    v_res_5752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(v_00_u03b2_5744_, v_depth_boxed_5751_, v_keys_5746_, v_vals_5747_, v_heq_5748_, v_i_5749_, v_entries_5750_);
    crate::leanh::lean_dec_ref(v_vals_5747_);
    crate::leanh::lean_dec_ref(v_keys_5746_);
    return v_res_5752_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(
    mut v_00_u03b2_5753_: *mut crate::leanh::LeanObject,
    mut v_x_5754_: *mut crate::leanh::LeanObject,
    mut v_x_5755_: *mut crate::leanh::LeanObject,
    mut v_x_5756_: *mut crate::leanh::LeanObject,
    mut v_x_5757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5758_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_x_5754_, v_x_5755_, v_x_5756_, v_x_5757_);
    return v___x_5758_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(
    mut v_msg_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5773_: u8 = 0;
    let mut v_toFunctor_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5780_: u8 = 0;
    let mut v___f_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5797_: u8 = 0;
    let mut v_toFunctor_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5804_: u8 = 0;
    let mut v___f_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508__overap_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5824_: u8 = 0;
    let mut v_unused_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5826_: u8 = 0;
    let mut v_unused_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5830_: u8 = 0;
    let mut v_unused_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5832_: u8 = 0;
    let mut v_unused_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5768_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
                v___x_5769_ = l_StateRefT_x27_instMonad___redArg(v___x_5768_);
                v_toApplicative_5770_ = crate::leanh::lean_ctor_get(v___x_5769_, 0);
                v_isSharedCheck_5832_ = (!crate::leanh::lean_is_exclusive(v___x_5769_)) as u8;
                if v_isSharedCheck_5832_ == 0 {
                    v_unused_5833_ = crate::leanh::lean_ctor_get(v___x_5769_, 1);
                    crate::leanh::lean_dec(v_unused_5833_);
                    v___x_5772_ = v___x_5769_;
                    v_isShared_5773_ = v_isSharedCheck_5832_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5770_);
                    crate::leanh::lean_dec(v___x_5769_);
                    v___x_5772_ = crate::leanh::lean_box(0);
                    v_isShared_5773_ = v_isSharedCheck_5832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5774_ = crate::leanh::lean_ctor_get(v_toApplicative_5770_, 0);
                v_toSeq_5775_ = crate::leanh::lean_ctor_get(v_toApplicative_5770_, 2);
                v_toSeqLeft_5776_ = crate::leanh::lean_ctor_get(v_toApplicative_5770_, 3);
                v_toSeqRight_5777_ = crate::leanh::lean_ctor_get(v_toApplicative_5770_, 4);
                v_isSharedCheck_5830_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5770_)) as u8;
                if v_isSharedCheck_5830_ == 0 {
                    v_unused_5831_ = crate::leanh::lean_ctor_get(v_toApplicative_5770_, 1);
                    crate::leanh::lean_dec(v_unused_5831_);
                    v___x_5779_ = v_toApplicative_5770_;
                    v_isShared_5780_ = v_isSharedCheck_5830_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5777_);
                    crate::leanh::lean_inc(v_toSeqLeft_5776_);
                    crate::leanh::lean_inc(v_toSeq_5775_);
                    crate::leanh::lean_inc(v_toFunctor_5774_);
                    crate::leanh::lean_dec(v_toApplicative_5770_);
                    v___x_5779_ = crate::leanh::lean_box(0);
                    v_isShared_5780_ = v_isSharedCheck_5830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5781_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1;
                v___f_5782_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_5774_);
                v___f_5783_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5783_, 0, v_toFunctor_5774_);
                v___f_5784_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5784_, 0, v_toFunctor_5774_);
                v___x_5785_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5785_, 0, v___f_5783_);
                crate::leanh::lean_ctor_set(v___x_5785_, 1, v___f_5784_);
                v___f_5786_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5786_, 0, v_toSeqRight_5777_);
                v___f_5787_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5787_, 0, v_toSeqLeft_5776_);
                v___f_5788_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5788_, 0, v_toSeq_5775_);
                if v_isShared_5780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5779_, 4, v___f_5786_);
                    crate::leanh::lean_ctor_set(v___x_5779_, 3, v___f_5787_);
                    crate::leanh::lean_ctor_set(v___x_5779_, 2, v___f_5788_);
                    crate::leanh::lean_ctor_set(v___x_5779_, 1, v___f_5781_);
                    crate::leanh::lean_ctor_set(v___x_5779_, 0, v___x_5785_);
                    v___x_5790_ = v___x_5779_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5829_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5829_, 0, v___x_5785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5829_, 1, v___f_5781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5829_, 2, v___f_5788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5829_, 3, v___f_5787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5829_, 4, v___f_5786_);
                    v___x_5790_ = v_reuseFailAlloc_5829_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5772_, 1, v___f_5782_);
                    crate::leanh::lean_ctor_set(v___x_5772_, 0, v___x_5790_);
                    v___x_5792_ = v___x_5772_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5828_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 1, v___f_5782_);
                    v___x_5792_ = v_reuseFailAlloc_5828_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5793_ = l_StateRefT_x27_instMonad___redArg(v___x_5792_);
                v_toApplicative_5794_ = crate::leanh::lean_ctor_get(v___x_5793_, 0);
                v_isSharedCheck_5826_ = (!crate::leanh::lean_is_exclusive(v___x_5793_)) as u8;
                if v_isSharedCheck_5826_ == 0 {
                    v_unused_5827_ = crate::leanh::lean_ctor_get(v___x_5793_, 1);
                    crate::leanh::lean_dec(v_unused_5827_);
                    v___x_5796_ = v___x_5793_;
                    v_isShared_5797_ = v_isSharedCheck_5826_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5794_);
                    crate::leanh::lean_dec(v___x_5793_);
                    v___x_5796_ = crate::leanh::lean_box(0);
                    v_isShared_5797_ = v_isSharedCheck_5826_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5798_ = crate::leanh::lean_ctor_get(v_toApplicative_5794_, 0);
                v_toSeq_5799_ = crate::leanh::lean_ctor_get(v_toApplicative_5794_, 2);
                v_toSeqLeft_5800_ = crate::leanh::lean_ctor_get(v_toApplicative_5794_, 3);
                v_toSeqRight_5801_ = crate::leanh::lean_ctor_get(v_toApplicative_5794_, 4);
                v_isSharedCheck_5824_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5794_)) as u8;
                if v_isSharedCheck_5824_ == 0 {
                    v_unused_5825_ = crate::leanh::lean_ctor_get(v_toApplicative_5794_, 1);
                    crate::leanh::lean_dec(v_unused_5825_);
                    v___x_5803_ = v_toApplicative_5794_;
                    v_isShared_5804_ = v_isSharedCheck_5824_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5801_);
                    crate::leanh::lean_inc(v_toSeqLeft_5800_);
                    crate::leanh::lean_inc(v_toSeq_5799_);
                    crate::leanh::lean_inc(v_toFunctor_5798_);
                    crate::leanh::lean_dec(v_toApplicative_5794_);
                    v___x_5803_ = crate::leanh::lean_box(0);
                    v_isShared_5804_ = v_isSharedCheck_5824_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5805_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0;
                v___f_5806_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1;
                crate::leanh::lean_inc_ref(v_toFunctor_5798_);
                v___f_5807_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5807_, 0, v_toFunctor_5798_);
                v___f_5808_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5808_, 0, v_toFunctor_5798_);
                v___x_5809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5809_, 0, v___f_5807_);
                crate::leanh::lean_ctor_set(v___x_5809_, 1, v___f_5808_);
                v___f_5810_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5810_, 0, v_toSeqRight_5801_);
                v___f_5811_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5811_, 0, v_toSeqLeft_5800_);
                v___f_5812_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5812_, 0, v_toSeq_5799_);
                if v_isShared_5804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5803_, 4, v___f_5810_);
                    crate::leanh::lean_ctor_set(v___x_5803_, 3, v___f_5811_);
                    crate::leanh::lean_ctor_set(v___x_5803_, 2, v___f_5812_);
                    crate::leanh::lean_ctor_set(v___x_5803_, 1, v___f_5805_);
                    crate::leanh::lean_ctor_set(v___x_5803_, 0, v___x_5809_);
                    v___x_5814_ = v___x_5803_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5823_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 0, v___x_5809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 1, v___f_5805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 2, v___f_5812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 3, v___f_5811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 4, v___f_5810_);
                    v___x_5814_ = v_reuseFailAlloc_5823_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5797_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5796_, 1, v___f_5806_);
                    crate::leanh::lean_ctor_set(v___x_5796_, 0, v___x_5814_);
                    v___x_5816_ = v___x_5796_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5822_, 0, v___x_5814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5822_, 1, v___f_5806_);
                    v___x_5816_ = v_reuseFailAlloc_5822_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5817_ = l_StateRefT_x27_instMonad___redArg(v___x_5816_);
                v___x_5818_ = crate::leanh::lean_box(0);
                v___x_5819_ = l_instInhabitedOfMonad___redArg(v___x_5817_, v___x_5818_);
                v___x_2508__overap_5820_ = lean_panic_fn_borrowed(v___x_5819_, v_msg_5761_);
                crate::leanh::lean_dec(v___x_5819_);
                crate::leanh::lean_inc(v___y_5766_);
                crate::leanh::lean_inc_ref(v___y_5765_);
                crate::leanh::lean_inc(v___y_5764_);
                crate::leanh::lean_inc_ref(v___y_5763_);
                crate::leanh::lean_inc(v___y_5762_);
                v___x_5821_ = crate::leanh::lean_apply_6(
                    v___x_2508__overap_5820_,
                    v___y_5762_,
                    v___y_5763_,
                    v___y_5764_,
                    v___y_5765_,
                    v___y_5766_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(
    mut v_msg_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
    mut v___y_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
    mut v___y_5840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5841_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
    crate::leanh::lean_dec(v___y_5839_);
    crate::leanh::lean_dec_ref(v___y_5838_);
    crate::leanh::lean_dec(v___y_5837_);
    crate::leanh::lean_dec_ref(v___y_5836_);
    crate::leanh::lean_dec(v___y_5835_);
    return v_res_5841_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5843_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2;
    v___x_5844_ = crate::leanh::lean_unsigned_to_nat(61);
    v___x_5845_ = crate::leanh::lean_unsigned_to_nat(304);
    v___x_5846_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0;
    v___x_5847_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4;
    v___x_5848_ = l_mkPanicMessageWithDecl(
        v___x_5847_,
        v___x_5846_,
        v___x_5845_,
        v___x_5844_,
        v___x_5843_,
    );
    return v___x_5848_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(
    mut v_c_5849_: *mut crate::leanh::LeanObject,
    mut v_a_5850_: *mut crate::leanh::LeanObject,
    mut v_a_5851_: *mut crate::leanh::LeanObject,
    mut v_a_5852_: *mut crate::leanh::LeanObject,
    mut v_a_5853_: *mut crate::leanh::LeanObject,
    mut v_a_5854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5877_: u8 = 0;
    let mut v_alts_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: u8 = 0;
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: u8 = 0;
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: usize = 0;
    let mut v___x_5891_: usize = 0;
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: usize = 0;
    let mut v___x_5894_: usize = 0;
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5899_: u8 = 0;
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5904_: u8 = 0;
    let mut v_unused_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5908_: u8 = 0;
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5913_: u8 = 0;
    let mut v_unused_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_c_5849_) {
                0 => {
                    v_decl_5856_ = crate::leanh::lean_ctor_get(v_c_5849_, 0);
                    v_value_5857_ = crate::leanh::lean_ctor_get(v_decl_5856_, 3);
                    if crate::leanh::lean_obj_tag(v_value_5857_) == 11 {
                        crate::leanh::lean_inc_ref(v_value_5857_);
                        v_k_5858_ = crate::leanh::lean_ctor_get(v_c_5849_, 1);
                        crate::leanh::lean_inc_ref(v_k_5858_);
                        crate::leanh::lean_dec_ref_known(v_c_5849_, 2);
                        v_var_5859_ = crate::leanh::lean_ctor_get(v_value_5857_, 1);
                        crate::leanh::lean_inc(v_var_5859_);
                        crate::leanh::lean_dec_ref_known(v_value_5857_, 2);
                        v___x_5860_ = lean_st_ref_take(v_a_5850_);
                        v___x_5861_ = crate::leanh::lean_box(0);
                        v___x_5862_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v___x_5860_, v_var_5859_, v___x_5861_);
                        v___x_5863_ = lean_st_ref_set(v_a_5850_, v___x_5862_);
                        v_c_5849_ = v_k_5858_;
                        state = 0;
                        continue;
                    } else {
                        v_k_5865_ = crate::leanh::lean_ctor_get(v_c_5849_, 1);
                        crate::leanh::lean_inc_ref(v_k_5865_);
                        crate::leanh::lean_dec_ref_known(v_c_5849_, 2);
                        v_c_5849_ = v_k_5865_;
                        state = 0;
                        continue;
                    }
                }
                2 => {
                    v_decl_5867_ = crate::leanh::lean_ctor_get(v_c_5849_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5867_);
                    v_k_5868_ = crate::leanh::lean_ctor_get(v_c_5849_, 1);
                    crate::leanh::lean_inc_ref(v_k_5868_);
                    crate::leanh::lean_dec_ref_known(v_c_5849_, 2);
                    v_value_5869_ = crate::leanh::lean_ctor_get(v_decl_5867_, 4);
                    crate::leanh::lean_inc_ref(v_value_5869_);
                    crate::leanh::lean_dec_ref(v_decl_5867_);
                    v___x_5870_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_value_5869_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_);
                    if crate::leanh::lean_obj_tag(v___x_5870_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5870_, 1);
                        v_c_5849_ = v_k_5868_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5868_);
                        return v___x_5870_;
                    }
                }
                3 => {
                    crate::leanh::lean_dec_ref_known(v_c_5849_, 2);
                    v___x_5872_ = crate::leanh::lean_box(0);
                    v___x_5873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5873_, 0, v___x_5872_);
                    return v___x_5873_;
                }
                4 => {
                    v_cases_5874_ = crate::leanh::lean_ctor_get(v_c_5849_, 0);
                    v_isSharedCheck_5896_ = (!crate::leanh::lean_is_exclusive(v_c_5849_)) as u8;
                    if v_isSharedCheck_5896_ == 0 {
                        v___x_5876_ = v_c_5849_;
                        v_isShared_5877_ = v_isSharedCheck_5896_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cases_5874_);
                        crate::leanh::lean_dec(v_c_5849_);
                        v___x_5876_ = crate::leanh::lean_box(0);
                        v_isShared_5877_ = v_isSharedCheck_5896_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_isSharedCheck_5904_ = (!crate::leanh::lean_is_exclusive(v_c_5849_)) as u8;
                    if v_isSharedCheck_5904_ == 0 {
                        v_unused_5905_ = crate::leanh::lean_ctor_get(v_c_5849_, 0);
                        crate::leanh::lean_dec(v_unused_5905_);
                        v___x_5898_ = v_c_5849_;
                        v_isShared_5899_ = v_isSharedCheck_5904_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_5849_);
                        v___x_5898_ = crate::leanh::lean_box(0);
                        v_isShared_5899_ = v_isSharedCheck_5904_;
                        state = 4;
                        continue;
                    }
                }
                6 => {
                    v_isSharedCheck_5913_ = (!crate::leanh::lean_is_exclusive(v_c_5849_)) as u8;
                    if v_isSharedCheck_5913_ == 0 {
                        v_unused_5914_ = crate::leanh::lean_ctor_get(v_c_5849_, 0);
                        crate::leanh::lean_dec(v_unused_5914_);
                        v___x_5907_ = v_c_5849_;
                        v_isShared_5908_ = v_isSharedCheck_5913_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_c_5849_);
                        v___x_5907_ = crate::leanh::lean_box(0);
                        v_isShared_5908_ = v_isSharedCheck_5913_;
                        state = 6;
                        continue;
                    }
                }
                8 => {
                    v_k_5915_ = crate::leanh::lean_ctor_get(v_c_5849_, 3);
                    crate::leanh::lean_inc_ref(v_k_5915_);
                    crate::leanh::lean_dec_ref_known(v_c_5849_, 4);
                    v_c_5849_ = v_k_5915_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_5917_ = crate::leanh::lean_ctor_get(v_c_5849_, 5);
                    crate::leanh::lean_inc_ref(v_k_5917_);
                    crate::leanh::lean_dec_ref_known(v_c_5849_, 6);
                    v_c_5849_ = v_k_5917_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_c_5849_);
                    v___x_5919_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
                    v___x_5920_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v___x_5919_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_);
                    return v___x_5920_;
                }
            },
            1 => {
                v_alts_5878_ = crate::leanh::lean_ctor_get(v_cases_5874_, 3);
                crate::leanh::lean_inc_ref(v_alts_5878_);
                crate::leanh::lean_dec_ref(v_cases_5874_);
                v___x_5879_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5880_ = lean_array_get_size(v_alts_5878_);
                v___x_5881_ = crate::leanh::lean_box(0);
                v___x_5882_ = lean_nat_dec_lt(v___x_5879_, v___x_5880_);
                if v___x_5882_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_5878_);
                    if v_isShared_5877_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5876_, 0);
                        crate::leanh::lean_ctor_set(v___x_5876_, 0, v___x_5881_);
                        v___x_5884_ = v___x_5876_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5885_, 0, v___x_5881_);
                        v___x_5884_ = v_reuseFailAlloc_5885_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5886_ = lean_nat_dec_le(v___x_5880_, v___x_5880_);
                    if v___x_5886_ == 0 {
                        if v___x_5882_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_5878_);
                            if v_isShared_5877_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_5876_, 0);
                                crate::leanh::lean_ctor_set(v___x_5876_, 0, v___x_5881_);
                                v___x_5888_ = v___x_5876_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5889_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5889_, 0, v___x_5881_);
                                v___x_5888_ = v_reuseFailAlloc_5889_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5876_);
                            v___x_5890_ = 0usize;
                            v___x_5891_ = lean_usize_of_nat(v___x_5880_);
                            v___x_5892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_5878_, v___x_5890_, v___x_5891_, v___x_5881_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_);
                            crate::leanh::lean_dec_ref(v_alts_5878_);
                            return v___x_5892_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5876_);
                        v___x_5893_ = 0usize;
                        v___x_5894_ = lean_usize_of_nat(v___x_5880_);
                        v___x_5895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_5878_, v___x_5893_, v___x_5894_, v___x_5881_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_);
                        crate::leanh::lean_dec_ref(v_alts_5878_);
                        return v___x_5895_;
                    }
                }
            }
            2 => {
                return v___x_5884_;
            }
            3 => {
                return v___x_5888_;
            }
            4 => {
                v___x_5900_ = crate::leanh::lean_box(0);
                if v_isShared_5899_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5898_, 0);
                    crate::leanh::lean_ctor_set(v___x_5898_, 0, v___x_5900_);
                    v___x_5902_ = v___x_5898_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5903_, 0, v___x_5900_);
                    v___x_5902_ = v_reuseFailAlloc_5903_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5902_;
            }
            6 => {
                v___x_5909_ = crate::leanh::lean_box(0);
                if v_isShared_5908_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5907_, 0);
                    crate::leanh::lean_ctor_set(v___x_5907_, 0, v___x_5909_);
                    v___x_5911_ = v___x_5907_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5912_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5912_, 0, v___x_5909_);
                    v___x_5911_ = v_reuseFailAlloc_5912_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(
    mut v_as_5921_: *mut crate::leanh::LeanObject,
    mut v_i_5922_: usize,
    mut v_stop_5923_: usize,
    mut v_b_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
    mut v___y_5928_: *mut crate::leanh::LeanObject,
    mut v___y_5929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: usize = 0;
    let mut v___x_5936_: usize = 0;
    let mut v___x_5938_: u8 = 0;
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5938_ = lean_usize_dec_eq(v_i_5922_, v_stop_5923_);
                if v___x_5938_ == 0 {
                    v___x_5939_ = lean_array_uget_borrowed(v_as_5921_, v_i_5922_);
                    match crate::leanh::lean_obj_tag(v___x_5939_) {
                        0 => {
                            v_code_5940_ = crate::leanh::lean_ctor_get(v___x_5939_, 2);
                            crate::leanh::lean_inc_ref(v_code_5940_);
                            v___y_5932_ = v_code_5940_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_5941_ = crate::leanh::lean_ctor_get(v___x_5939_, 1);
                            crate::leanh::lean_inc_ref(v_code_5941_);
                            v___y_5932_ = v_code_5941_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_5942_ = crate::leanh::lean_ctor_get(v___x_5939_, 0);
                            crate::leanh::lean_inc_ref(v_code_5942_);
                            v___y_5932_ = v_code_5942_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_5943_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5943_, 0, v_b_5924_);
                    return v___x_5943_;
                }
            }
            1 => {
                v___x_5933_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v___y_5932_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_);
                if crate::leanh::lean_obj_tag(v___x_5933_) == 0 {
                    v_a_5934_ = crate::leanh::lean_ctor_get(v___x_5933_, 0);
                    crate::leanh::lean_inc(v_a_5934_);
                    crate::leanh::lean_dec_ref_known(v___x_5933_, 1);
                    v___x_5935_ = 1usize;
                    v___x_5936_ = lean_usize_add(v_i_5922_, v___x_5935_);
                    v_i_5922_ = v___x_5936_;
                    v_b_5924_ = v_a_5934_;
                    state = 0;
                    continue;
                } else {
                    return v___x_5933_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(
    mut v_as_5944_: *mut crate::leanh::LeanObject,
    mut v_i_5945_: *mut crate::leanh::LeanObject,
    mut v_stop_5946_: *mut crate::leanh::LeanObject,
    mut v_b_5947_: *mut crate::leanh::LeanObject,
    mut v___y_5948_: *mut crate::leanh::LeanObject,
    mut v___y_5949_: *mut crate::leanh::LeanObject,
    mut v___y_5950_: *mut crate::leanh::LeanObject,
    mut v___y_5951_: *mut crate::leanh::LeanObject,
    mut v___y_5952_: *mut crate::leanh::LeanObject,
    mut v___y_5953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5954_: usize = 0;
    let mut v_stop_boxed_5955_: usize = 0;
    let mut v_res_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5954_ = crate::leanh::lean_unbox_usize(v_i_5945_);
    crate::leanh::lean_dec(v_i_5945_);
    v_stop_boxed_5955_ = crate::leanh::lean_unbox_usize(v_stop_5946_);
    crate::leanh::lean_dec(v_stop_5946_);
    v_res_5956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_5944_, v_i_boxed_5954_, v_stop_boxed_5955_, v_b_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
    crate::leanh::lean_dec(v___y_5952_);
    crate::leanh::lean_dec_ref(v___y_5951_);
    crate::leanh::lean_dec(v___y_5950_);
    crate::leanh::lean_dec_ref(v___y_5949_);
    crate::leanh::lean_dec(v___y_5948_);
    crate::leanh::lean_dec_ref(v_as_5944_);
    return v_res_5956_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(
    mut v_c_5957_: *mut crate::leanh::LeanObject,
    mut v_a_5958_: *mut crate::leanh::LeanObject,
    mut v_a_5959_: *mut crate::leanh::LeanObject,
    mut v_a_5960_: *mut crate::leanh::LeanObject,
    mut v_a_5961_: *mut crate::leanh::LeanObject,
    mut v_a_5962_: *mut crate::leanh::LeanObject,
    mut v_a_5963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5964_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_5957_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_, v_a_5962_);
    crate::leanh::lean_dec(v_a_5962_);
    crate::leanh::lean_dec_ref(v_a_5961_);
    crate::leanh::lean_dec(v_a_5960_);
    crate::leanh::lean_dec_ref(v_a_5959_);
    crate::leanh::lean_dec(v_a_5958_);
    return v_res_5964_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5965_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5965_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5966_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
    v___x_5967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5967_, 0, v___x_5966_);
    return v___x_5967_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(
    mut v_00_u03b2_5968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5969_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1);
    return v___x_5969_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(
    mut v_f_5970_: *mut crate::leanh::LeanObject,
    mut v_v_5971_: *mut crate::leanh::LeanObject,
    mut v___y_5972_: *mut crate::leanh::LeanObject,
    mut v___y_5973_: *mut crate::leanh::LeanObject,
    mut v___y_5974_: *mut crate::leanh::LeanObject,
    mut v___y_5975_: *mut crate::leanh::LeanObject,
    mut v___y_5976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5981_: u8 = 0;
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5986_: u8 = 0;
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5993_: u8 = 0;
    let mut v_a_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5997_: u8 = 0;
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6001_: u8 = 0;
    let mut v_isSharedCheck_6002_: u8 = 0;
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_5971_) == 0 {
                    v_code_5978_ = crate::leanh::lean_ctor_get(v_v_5971_, 0);
                    v_isSharedCheck_6002_ = (!crate::leanh::lean_is_exclusive(v_v_5971_)) as u8;
                    if v_isSharedCheck_6002_ == 0 {
                        v___x_5980_ = v_v_5971_;
                        v_isShared_5981_ = v_isSharedCheck_6002_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_5978_);
                        crate::leanh::lean_dec(v_v_5971_);
                        v___x_5980_ = crate::leanh::lean_box(0);
                        v_isShared_5981_ = v_isSharedCheck_6002_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5970_);
                    v___x_6003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6003_, 0, v_v_5971_);
                    return v___x_6003_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_5976_);
                crate::leanh::lean_inc_ref(v___y_5975_);
                crate::leanh::lean_inc(v___y_5974_);
                crate::leanh::lean_inc_ref(v___y_5973_);
                crate::leanh::lean_inc_ref(v___y_5972_);
                v___x_5982_ = crate::leanh::lean_apply_7(
                    v_f_5970_,
                    v_code_5978_,
                    v___y_5972_,
                    v___y_5973_,
                    v___y_5974_,
                    v___y_5975_,
                    v___y_5976_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5982_) == 0 {
                    v_a_5983_ = crate::leanh::lean_ctor_get(v___x_5982_, 0);
                    v_isSharedCheck_5993_ = (!crate::leanh::lean_is_exclusive(v___x_5982_)) as u8;
                    if v_isSharedCheck_5993_ == 0 {
                        v___x_5985_ = v___x_5982_;
                        v_isShared_5986_ = v_isSharedCheck_5993_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5983_);
                        crate::leanh::lean_dec(v___x_5982_);
                        v___x_5985_ = crate::leanh::lean_box(0);
                        v_isShared_5986_ = v_isSharedCheck_5993_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5980_);
                    v_a_5994_ = crate::leanh::lean_ctor_get(v___x_5982_, 0);
                    v_isSharedCheck_6001_ = (!crate::leanh::lean_is_exclusive(v___x_5982_)) as u8;
                    if v_isSharedCheck_6001_ == 0 {
                        v___x_5996_ = v___x_5982_;
                        v_isShared_5997_ = v_isSharedCheck_6001_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5994_);
                        crate::leanh::lean_dec(v___x_5982_);
                        v___x_5996_ = crate::leanh::lean_box(0);
                        v_isShared_5997_ = v_isSharedCheck_6001_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5980_, 0, v_a_5983_);
                    v___x_5988_ = v___x_5980_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_a_5983_);
                    v___x_5988_ = v_reuseFailAlloc_5992_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5986_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5985_, 0, v___x_5988_);
                    v___x_5990_ = v___x_5985_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5991_, 0, v___x_5988_);
                    v___x_5990_ = v_reuseFailAlloc_5991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5990_;
            }
            5 => {
                if v_isShared_5997_ == 0 {
                    v___x_5999_ = v___x_5996_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6000_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6000_, 0, v_a_5994_);
                    v___x_5999_ = v_reuseFailAlloc_6000_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(
    mut v_f_6004_: *mut crate::leanh::LeanObject,
    mut v_v_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
    mut v___y_6010_: *mut crate::leanh::LeanObject,
    mut v___y_6011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6012_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_6004_, v_v_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_);
    crate::leanh::lean_dec(v___y_6010_);
    crate::leanh::lean_dec_ref(v___y_6009_);
    crate::leanh::lean_dec(v___y_6008_);
    crate::leanh::lean_dec_ref(v___y_6007_);
    crate::leanh::lean_dec_ref(v___y_6006_);
    return v_res_6012_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(
    mut v_pu_6013_: u8,
    mut v_f_6014_: *mut crate::leanh::LeanObject,
    mut v_v_6015_: *mut crate::leanh::LeanObject,
    mut v___y_6016_: *mut crate::leanh::LeanObject,
    mut v___y_6017_: *mut crate::leanh::LeanObject,
    mut v___y_6018_: *mut crate::leanh::LeanObject,
    mut v___y_6019_: *mut crate::leanh::LeanObject,
    mut v___y_6020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6022_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_6014_, v_v_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_);
    return v___x_6022_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(
    mut v_pu_6023_: *mut crate::leanh::LeanObject,
    mut v_f_6024_: *mut crate::leanh::LeanObject,
    mut v_v_6025_: *mut crate::leanh::LeanObject,
    mut v___y_6026_: *mut crate::leanh::LeanObject,
    mut v___y_6027_: *mut crate::leanh::LeanObject,
    mut v___y_6028_: *mut crate::leanh::LeanObject,
    mut v___y_6029_: *mut crate::leanh::LeanObject,
    mut v___y_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6032_: u8 = 0;
    let mut v_res_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6032_ = (crate::leanh::lean_unbox(v_pu_6023_) as u8);
    v_res_6033_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_boxed_6032_, v_f_6024_, v_v_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_);
    crate::leanh::lean_dec(v___y_6030_);
    crate::leanh::lean_dec_ref(v___y_6029_);
    crate::leanh::lean_dec(v___y_6028_);
    crate::leanh::lean_dec_ref(v___y_6027_);
    crate::leanh::lean_dec_ref(v___y_6026_);
    return v_res_6033_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6034_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(crate::leanh::lean_box(0));
    return v___x_6034_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(
    mut v_code_6035_: *mut crate::leanh::LeanObject,
    mut v___y_6036_: *mut crate::leanh::LeanObject,
    mut v___y_6037_: *mut crate::leanh::LeanObject,
    mut v___y_6038_: *mut crate::leanh::LeanObject,
    mut v___y_6039_: *mut crate::leanh::LeanObject,
    mut v___y_6040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_alreadyFound_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relaxedReuse_6044_: u8 = 0;
    let mut v_ownedness_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relaxedReuse_6052_: u8 = 0;
    let mut v_ownedness_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ownedness_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6063_: u8 = 0;
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_relaxedReuse_6052_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6036_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_relaxedReuse_6052_ == 0 {
                    v_ownedness_6053_ = crate::leanh::lean_ctor_get(v___y_6036_, 1);
                    v___x_6054_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
                    v_alreadyFound_6043_ = v___x_6054_;
                    v_relaxedReuse_6044_ = v_relaxedReuse_6052_;
                    v_ownedness_6045_ = v_ownedness_6053_;
                    v___y_6046_ = v___y_6037_;
                    v___y_6047_ = v___y_6038_;
                    v___y_6048_ = v___y_6039_;
                    v___y_6049_ = v___y_6040_;
                    state = 1;
                    continue;
                } else {
                    v_ownedness_6055_ = crate::leanh::lean_ctor_get(v___y_6036_, 1);
                    v___x_6056_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
                    v___x_6057_ = lean_st_mk_ref(v___x_6056_);
                    crate::leanh::lean_inc_ref(v_code_6035_);
                    v___x_6058_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_code_6035_, v___x_6057_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_);
                    if crate::leanh::lean_obj_tag(v___x_6058_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6058_, 1);
                        v___x_6059_ = lean_st_ref_get(v___x_6057_);
                        crate::leanh::lean_dec(v___x_6057_);
                        v_alreadyFound_6043_ = v___x_6059_;
                        v_relaxedReuse_6044_ = v_relaxedReuse_6052_;
                        v_ownedness_6045_ = v_ownedness_6055_;
                        v___y_6046_ = v___y_6037_;
                        v___y_6047_ = v___y_6038_;
                        v___y_6048_ = v___y_6039_;
                        v___y_6049_ = v___y_6040_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6057_);
                        crate::leanh::lean_dec_ref(v_code_6035_);
                        v_a_6060_ = crate::leanh::lean_ctor_get(v___x_6058_, 0);
                        v_isSharedCheck_6067_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6058_)) as u8;
                        if v_isSharedCheck_6067_ == 0 {
                            v___x_6062_ = v___x_6058_;
                            v_isShared_6063_ = v_isSharedCheck_6067_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6060_);
                            crate::leanh::lean_dec(v___x_6058_);
                            v___x_6062_ = crate::leanh::lean_box(0);
                            v_isShared_6063_ = v_isSharedCheck_6067_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_ownedness_6045_);
                v___x_6050_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6050_, 0, v_alreadyFound_6043_);
                crate::leanh::lean_ctor_set(v___x_6050_, 1, v_ownedness_6045_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6050_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_relaxedReuse_6044_,
                );
                v___x_6051_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_code_6035_, v___x_6050_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_);
                crate::leanh::lean_dec_ref_known(v___x_6050_, 2);
                return v___x_6051_;
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
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(
    mut v_code_6068_: *mut crate::leanh::LeanObject,
    mut v___y_6069_: *mut crate::leanh::LeanObject,
    mut v___y_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6075_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_);
    crate::leanh::lean_dec(v___y_6073_);
    crate::leanh::lean_dec_ref(v___y_6072_);
    crate::leanh::lean_dec(v___y_6071_);
    crate::leanh::lean_dec_ref(v___y_6070_);
    crate::leanh::lean_dec_ref(v___y_6069_);
    return v_res_6075_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(
    mut v_decl_6077_: *mut crate::leanh::LeanObject,
    mut v_a_6078_: *mut crate::leanh::LeanObject,
    mut v_a_6079_: *mut crate::leanh::LeanObject,
    mut v_a_6080_: *mut crate::leanh::LeanObject,
    mut v_a_6081_: *mut crate::leanh::LeanObject,
    mut v_a_6082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_6086_: u8 = 0;
    let mut v_inlineAttr_x3f_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6090_: u8 = 0;
    let mut v___f_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6096_: u8 = 0;
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6103_: u8 = 0;
    let mut v_a_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6107_: u8 = 0;
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6111_: u8 = 0;
    let mut v_isSharedCheck_6112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_6084_ = crate::leanh::lean_ctor_get(v_decl_6077_, 0);
                v_value_6085_ = crate::leanh::lean_ctor_get(v_decl_6077_, 1);
                v_recursive_6086_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_6077_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_6087_ = crate::leanh::lean_ctor_get(v_decl_6077_, 2);
                v_isSharedCheck_6112_ = (!crate::leanh::lean_is_exclusive(v_decl_6077_)) as u8;
                if v_isSharedCheck_6112_ == 0 {
                    v___x_6089_ = v_decl_6077_;
                    v_isShared_6090_ = v_isSharedCheck_6112_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_6087_);
                    crate::leanh::lean_inc(v_value_6085_);
                    crate::leanh::lean_inc(v_toSignature_6084_);
                    crate::leanh::lean_dec(v_decl_6077_);
                    v___x_6089_ = crate::leanh::lean_box(0);
                    v_isShared_6090_ = v_isSharedCheck_6112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_6091_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0;
                v___x_6092_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v___f_6091_, v_value_6085_, v_a_6078_, v_a_6079_, v_a_6080_, v_a_6081_, v_a_6082_);
                if crate::leanh::lean_obj_tag(v___x_6092_) == 0 {
                    v_a_6093_ = crate::leanh::lean_ctor_get(v___x_6092_, 0);
                    v_isSharedCheck_6103_ = (!crate::leanh::lean_is_exclusive(v___x_6092_)) as u8;
                    if v_isSharedCheck_6103_ == 0 {
                        v___x_6095_ = v___x_6092_;
                        v_isShared_6096_ = v_isSharedCheck_6103_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6093_);
                        crate::leanh::lean_dec(v___x_6092_);
                        v___x_6095_ = crate::leanh::lean_box(0);
                        v_isShared_6096_ = v_isSharedCheck_6103_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6089_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_6087_);
                    crate::leanh::lean_dec_ref(v_toSignature_6084_);
                    v_a_6104_ = crate::leanh::lean_ctor_get(v___x_6092_, 0);
                    v_isSharedCheck_6111_ = (!crate::leanh::lean_is_exclusive(v___x_6092_)) as u8;
                    if v_isSharedCheck_6111_ == 0 {
                        v___x_6106_ = v___x_6092_;
                        v_isShared_6107_ = v_isSharedCheck_6111_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6104_);
                        crate::leanh::lean_dec(v___x_6092_);
                        v___x_6106_ = crate::leanh::lean_box(0);
                        v_isShared_6107_ = v_isSharedCheck_6111_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6089_, 1, v_a_6093_);
                    v___x_6098_ = v___x_6089_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6102_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_toSignature_6084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 1, v_a_6093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 2, v_inlineAttr_x3f_6087_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6102_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_6086_,
                    );
                    v___x_6098_ = v_reuseFailAlloc_6102_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6096_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6095_, 0, v___x_6098_);
                    v___x_6100_ = v___x_6095_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6101_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6101_, 0, v___x_6098_);
                    v___x_6100_ = v_reuseFailAlloc_6101_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6100_;
            }
            5 => {
                if v_isShared_6107_ == 0 {
                    v___x_6109_ = v___x_6106_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
                    v___x_6109_ = v_reuseFailAlloc_6110_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(
    mut v_decl_6113_: *mut crate::leanh::LeanObject,
    mut v_a_6114_: *mut crate::leanh::LeanObject,
    mut v_a_6115_: *mut crate::leanh::LeanObject,
    mut v_a_6116_: *mut crate::leanh::LeanObject,
    mut v_a_6117_: *mut crate::leanh::LeanObject,
    mut v_a_6118_: *mut crate::leanh::LeanObject,
    mut v_a_6119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6120_ =
        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(
            v_decl_6113_,
            v_a_6114_,
            v_a_6115_,
            v_a_6116_,
            v_a_6117_,
            v_a_6118_,
        );
    crate::leanh::lean_dec(v_a_6118_);
    crate::leanh::lean_dec_ref(v_a_6117_);
    crate::leanh::lean_dec(v_a_6116_);
    crate::leanh::lean_dec_ref(v_a_6115_);
    crate::leanh::lean_dec_ref(v_a_6114_);
    return v_res_6120_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(
    mut v_decl_6121_: *mut crate::leanh::LeanObject,
    mut v_a_6122_: *mut crate::leanh::LeanObject,
    mut v_a_6123_: *mut crate::leanh::LeanObject,
    mut v_a_6124_: *mut crate::leanh::LeanObject,
    mut v_a_6125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6131_: u8 = 0;
    let mut v_resetReuse_6132_: u8 = 0;
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: u8 = 0;
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6150_: u8 = 0;
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6154_: u8 = 0;
    let mut v_isSharedCheck_6155_: u8 = 0;
    let mut v_a_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6159_: u8 = 0;
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6127_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_6122_);
                if crate::leanh::lean_obj_tag(v___x_6127_) == 0 {
                    v_a_6128_ = crate::leanh::lean_ctor_get(v___x_6127_, 0);
                    v_isSharedCheck_6155_ = (!crate::leanh::lean_is_exclusive(v___x_6127_)) as u8;
                    if v_isSharedCheck_6155_ == 0 {
                        v___x_6130_ = v___x_6127_;
                        v_isShared_6131_ = v_isSharedCheck_6155_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6128_);
                        crate::leanh::lean_dec(v___x_6127_);
                        v___x_6130_ = crate::leanh::lean_box(0);
                        v_isShared_6131_ = v_isSharedCheck_6155_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decl_6121_);
                    v_a_6156_ = crate::leanh::lean_ctor_get(v___x_6127_, 0);
                    v_isSharedCheck_6163_ = (!crate::leanh::lean_is_exclusive(v___x_6127_)) as u8;
                    if v_isSharedCheck_6163_ == 0 {
                        v___x_6158_ = v___x_6127_;
                        v_isShared_6159_ = v_isSharedCheck_6163_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6156_);
                        crate::leanh::lean_dec(v___x_6127_);
                        v___x_6158_ = crate::leanh::lean_box(0);
                        v_isShared_6159_ = v_isSharedCheck_6163_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_resetReuse_6132_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 2) as u32,
                );
                crate::leanh::lean_dec(v_a_6128_);
                if v_resetReuse_6132_ == 0 {
                    if v_isShared_6131_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6130_, 0, v_decl_6121_);
                        v___x_6134_ = v___x_6130_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_decl_6121_);
                        v___x_6134_ = v_reuseFailAlloc_6135_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6130_);
                    crate::leanh::lean_inc_ref(v_decl_6121_);
                    v___x_6136_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(
                        v_decl_6121_,
                        v_a_6122_,
                        v_a_6123_,
                        v_a_6124_,
                        v_a_6125_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6136_) == 0 {
                        v_a_6137_ = crate::leanh::lean_ctor_get(v___x_6136_, 0);
                        crate::leanh::lean_inc_n(v_a_6137_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_6136_, 1);
                        v___x_6138_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(
                            v_decl_6121_,
                            v_a_6137_,
                            v_a_6122_,
                            v_a_6123_,
                            v_a_6124_,
                            v_a_6125_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6138_) == 0 {
                            v_a_6139_ = crate::leanh::lean_ctor_get(v___x_6138_, 0);
                            crate::leanh::lean_inc(v_a_6139_);
                            crate::leanh::lean_dec_ref_known(v___x_6138_, 1);
                            v___x_6140_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
                            v___x_6141_ = 0;
                            crate::leanh::lean_inc(v_a_6137_);
                            v___x_6142_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_6142_, 0, v___x_6140_);
                            crate::leanh::lean_ctor_set(v___x_6142_, 1, v_a_6137_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6142_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_6141_,
                            );
                            v___x_6143_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_6139_, v___x_6142_, v_a_6122_, v_a_6123_, v_a_6124_, v_a_6125_);
                            crate::leanh::lean_dec_ref_known(v___x_6142_, 2);
                            if crate::leanh::lean_obj_tag(v___x_6143_) == 0 {
                                v_a_6144_ = crate::leanh::lean_ctor_get(v___x_6143_, 0);
                                crate::leanh::lean_inc(v_a_6144_);
                                crate::leanh::lean_dec_ref_known(v___x_6143_, 1);
                                v___x_6145_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_6145_, 0, v___x_6140_);
                                crate::leanh::lean_ctor_set(v___x_6145_, 1, v_a_6137_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6145_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                        as u32,
                                    v_resetReuse_6132_,
                                );
                                v___x_6146_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_6144_, v___x_6145_, v_a_6122_, v_a_6123_, v_a_6124_, v_a_6125_);
                                crate::leanh::lean_dec_ref_known(v___x_6145_, 2);
                                return v___x_6146_;
                            } else {
                                crate::leanh::lean_dec(v_a_6137_);
                                return v___x_6143_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6137_);
                            return v___x_6138_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_decl_6121_);
                        v_a_6147_ = crate::leanh::lean_ctor_get(v___x_6136_, 0);
                        v_isSharedCheck_6154_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6136_)) as u8;
                        if v_isSharedCheck_6154_ == 0 {
                            v___x_6149_ = v___x_6136_;
                            v_isShared_6150_ = v_isSharedCheck_6154_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6147_);
                            crate::leanh::lean_dec(v___x_6136_);
                            v___x_6149_ = crate::leanh::lean_box(0);
                            v_isShared_6150_ = v_isSharedCheck_6154_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6134_;
            }
            3 => {
                if v_isShared_6150_ == 0 {
                    v___x_6152_ = v___x_6149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6153_, 0, v_a_6147_);
                    v___x_6152_ = v_reuseFailAlloc_6153_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6152_;
            }
            5 => {
                if v_isShared_6159_ == 0 {
                    v___x_6161_ = v___x_6158_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6162_, 0, v_a_6156_);
                    v___x_6161_ = v_reuseFailAlloc_6162_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(
    mut v_decl_6164_: *mut crate::leanh::LeanObject,
    mut v_a_6165_: *mut crate::leanh::LeanObject,
    mut v_a_6166_: *mut crate::leanh::LeanObject,
    mut v_a_6167_: *mut crate::leanh::LeanObject,
    mut v_a_6168_: *mut crate::leanh::LeanObject,
    mut v_a_6169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6170_ =
        l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(
            v_decl_6164_,
            v_a_6165_,
            v_a_6166_,
            v_a_6167_,
            v_a_6168_,
        );
    crate::leanh::lean_dec(v_a_6168_);
    crate::leanh::lean_dec_ref(v_a_6167_);
    crate::leanh::lean_dec(v_a_6166_);
    crate::leanh::lean_dec_ref(v_a_6165_);
    return v_res_6170_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: u8 = 0;
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6175_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6176_ = l_Lean_Compiler_LCNF_insertResetReuse___closed__2;
    v___x_6177_ = 2;
    v___x_6178_ = l_Lean_Compiler_LCNF_insertResetReuse___closed__1;
    v___x_6179_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_6178_,
        v___x_6177_,
        v___x_6176_,
        v___x_6175_,
    );
    return v___x_6179_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_insertResetReuse() -> *mut crate::leanh::LeanObject {
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6180_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_insertResetReuse___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once),
        _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3,
    );
    return v___x_6180_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6236_ = crate::leanh::lean_unsigned_to_nat(2506150707);
    v___x_6237_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
    v___x_6238_ = l_Lean_Name_num___override(v___x_6237_, v___x_6236_);
    return v___x_6238_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6240_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
    v___x_6241_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
    v___x_6242_ = l_Lean_Name_str___override(v___x_6241_, v___x_6240_);
    return v___x_6242_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6244_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
    v___x_6245_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
    v___x_6246_ = l_Lean_Name_str___override(v___x_6245_, v___x_6244_);
    return v___x_6246_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6247_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_6248_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
    v___x_6249_ = l_Lean_Name_num___override(v___x_6248_, v___x_6247_);
    return v___x_6249_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: u8 = 0;
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6251_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
    v___x_6252_ = 1;
    v___x_6253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
    v___x_6254_ = l_Lean_registerTraceClass(v___x_6251_, v___x_6252_, v___x_6253_);
    return v___x_6254_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(
    mut v_a_6255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6256_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
    return v_res_6256_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ResetReuse(
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
    res = runtime_initialize_Lean_Compiler_LCNF_LiveVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_insertResetReuse = _init_l_Lean_Compiler_LCNF_insertResetReuse();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_insertResetReuse);
    res = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ResetReuse(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ResetReuse(
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
    res = initialize_Lean_Compiler_LCNF_LiveVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
}
