// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.DiscrM
// Imports: Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Simp.Basic
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_LetValue_toExpr;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg, l_Lean_Compiler_LCNF_getPurity___redArg,
    l_Lean_Compiler_LCNF_getType, l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    initialize_Lean_Compiler_LCNF_InferType, l_Lean_Compiler_LCNF_eqvTypes,
    l_Lean_Compiler_LCNF_inferType, runtime_initialize_Lean_Compiler_LCNF_InferType,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::Simp::Basic::{
    initialize_Lean_Compiler_LCNF_Simp_Basic, runtime_initialize_Lean_Compiler_LCNF_Simp_Basic,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Expr_isErased;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hash, l_Lean_Expr_headBeta, l_Lean_Expr_sort___override,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
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
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__1_value:
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
    m_data: [115, 117, 99, 99, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16112798088292836701 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__3_value:
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
    m_data: [122, 101, 114, 111, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__3_value)
            as *mut crate::leanh::LeanObject,
        13428217069302927667 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__1_value:
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
static mut l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__4_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorIdx(
    mut v_x_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1529_) == 0 {
        let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1530_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1530_;
    } else {
        let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1531_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1531_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorIdx___boxed(
    mut v_x_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorIdx(v_x_1532_);
    crate::leanh::lean_dec_ref(v_x_1532_);
    return v_res_1533_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(
    mut v_t_1534_: *mut crate::leanh::LeanObject,
    mut v_k_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1534_) == 0 {
        let mut v_val_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_args_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1536_ = crate::leanh::lean_ctor_get(v_t_1534_, 0);
        crate::leanh::lean_inc_ref(v_val_1536_);
        v_args_1537_ = crate::leanh::lean_ctor_get(v_t_1534_, 1);
        crate::leanh::lean_inc_ref(v_args_1537_);
        crate::leanh::lean_dec_ref_known(v_t_1534_, 2);
        v___x_1538_ = crate::leanh::lean_apply_2(v_k_1535_, v_val_1536_, v_args_1537_);
        return v___x_1538_;
    } else {
        let mut v_n_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_n_1539_ = crate::leanh::lean_ctor_get(v_t_1534_, 0);
        crate::leanh::lean_inc(v_n_1539_);
        crate::leanh::lean_dec_ref_known(v_t_1534_, 1);
        v___x_1540_ = crate::leanh::lean_apply_1(v_k_1535_, v_n_1539_);
        return v___x_1540_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim(
    mut v_motive_1541_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1542_: *mut crate::leanh::LeanObject,
    mut v_t_1543_: *mut crate::leanh::LeanObject,
    mut v_h_1544_: *mut crate::leanh::LeanObject,
    mut v_k_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1543_, v_k_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___boxed(
    mut v_motive_1547_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1548_: *mut crate::leanh::LeanObject,
    mut v_t_1549_: *mut crate::leanh::LeanObject,
    mut v_h_1550_: *mut crate::leanh::LeanObject,
    mut v_k_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim(
        v_motive_1547_,
        v_ctorIdx_1548_,
        v_t_1549_,
        v_h_1550_,
        v_k_1551_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1548_);
    return v_res_1552_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctor_elim___redArg(
    mut v_t_1553_: *mut crate::leanh::LeanObject,
    mut v_ctor_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1553_, v_ctor_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctor_elim(
    mut v_motive_1556_: *mut crate::leanh::LeanObject,
    mut v_t_1557_: *mut crate::leanh::LeanObject,
    mut v_h_1558_: *mut crate::leanh::LeanObject,
    mut v_ctor_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1557_, v_ctor_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_natVal_elim___redArg(
    mut v_t_1561_: *mut crate::leanh::LeanObject,
    mut v_natVal_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1563_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1561_, v_natVal_1562_);
    return v___x_1563_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_natVal_elim(
    mut v_motive_1564_: *mut crate::leanh::LeanObject,
    mut v_t_1565_: *mut crate::leanh::LeanObject,
    mut v_h_1566_: *mut crate::leanh::LeanObject,
    mut v_natVal_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1565_, v_natVal_1567_);
    return v___x_1568_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(
    mut v_x_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1578_) == 0 {
        let mut v_val_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toConstantVal_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1579_ = crate::leanh::lean_ctor_get(v_x_1578_, 0);
        v_toConstantVal_1580_ = crate::leanh::lean_ctor_get(v_val_1579_, 0);
        v_name_1581_ = crate::leanh::lean_ctor_get(v_toConstantVal_1580_, 0);
        crate::leanh::lean_inc(v_name_1581_);
        return v_name_1581_;
    } else {
        let mut v_n_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: u8 = 0;
        v_n_1582_ = crate::leanh::lean_ctor_get(v_x_1578_, 0);
        v___x_1583_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1584_ = lean_nat_dec_eq(v_n_1582_, v___x_1583_);
        if v___x_1584_ == 0 {
            let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1585_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2;
            return v___x_1585_;
        } else {
            let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1586_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4;
            return v___x_1586_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___boxed(
    mut v_x_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_x_1587_);
    crate::leanh::lean_dec_ref(v_x_1587_);
    return v_res_1588_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumParams(
    mut v_x_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1589_) == 0 {
        let mut v_val_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_numParams_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1590_ = crate::leanh::lean_ctor_get(v_x_1589_, 0);
        v_numParams_1591_ = crate::leanh::lean_ctor_get(v_val_1590_, 3);
        crate::leanh::lean_inc(v_numParams_1591_);
        return v_numParams_1591_;
    } else {
        let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1592_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1592_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumParams___boxed(
    mut v_x_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumParams(v_x_1593_);
    crate::leanh::lean_dec_ref(v_x_1593_);
    return v_res_1594_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumFields(
    mut v_x_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1595_) == 0 {
        let mut v_val_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_numFields_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1596_ = crate::leanh::lean_ctor_get(v_x_1595_, 0);
        v_numFields_1597_ = crate::leanh::lean_ctor_get(v_val_1596_, 4);
        crate::leanh::lean_inc(v_numFields_1597_);
        return v_numFields_1597_;
    } else {
        let mut v_n_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: u8 = 0;
        v_n_1598_ = crate::leanh::lean_ctor_get(v_x_1595_, 0);
        v___x_1599_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1600_ = lean_nat_dec_eq(v_n_1598_, v___x_1599_);
        if v___x_1600_ == 0 {
            let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1601_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1601_;
        } else {
            return v___x_1599_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumFields___boxed(
    mut v_x_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumFields(v_x_1602_);
    crate::leanh::lean_dec_ref(v_x_1602_);
    return v_res_1603_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(
    mut v_t_1604_: *mut crate::leanh::LeanObject,
    mut v_k_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1604_) == 0 {
                    v_k_1606_ = crate::leanh::lean_ctor_get(v_t_1604_, 1);
                    v_v_1607_ = crate::leanh::lean_ctor_get(v_t_1604_, 2);
                    v_l_1608_ = crate::leanh::lean_ctor_get(v_t_1604_, 3);
                    v_r_1609_ = crate::leanh::lean_ctor_get(v_t_1604_, 4);
                    v___x_1610_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1605_, v_k_1606_);
                    match v___x_1610_ {
                        0 => {
                            v_t_1604_ = v_l_1608_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_1607_);
                            v___x_1612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1612_, 0, v_v_1607_);
                            return v___x_1612_;
                        }
                        _ => {
                            v_t_1604_ = v_r_1609_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1614_ = crate::leanh::lean_box(0);
                    return v___x_1614_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg___boxed(
    mut v_t_1615_: *mut crate::leanh::LeanObject,
    mut v_k_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_t_1615_, v_k_1616_);
    crate::leanh::lean_dec(v_k_1616_);
    crate::leanh::lean_dec(v_t_1615_);
    return v_res_1617_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
    mut v_fvarId_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
    mut v_a_1620_: *mut crate::leanh::LeanObject,
    mut v_a_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___y_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrCtorMap_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v_value_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v_val_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut v_declName_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v_val_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_isSharedCheck_1685_: u8 = 0;
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_a_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1626_ = 0;
                v___x_1627_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                    v___x_1626_,
                    v_fvarId_1618_,
                    v_a_1620_,
                );
                if crate::leanh::lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1687_ = (!crate::leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1630_ = v___x_1627_;
                        v_isShared_1631_ = v_isSharedCheck_1687_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1628_);
                        crate::leanh::lean_dec(v___x_1627_);
                        v___x_1630_ = crate::leanh::lean_box(0);
                        v_isShared_1631_ = v_isSharedCheck_1687_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1688_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1695_ = (!crate::leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1695_ == 0 {
                        v___x_1690_ = v___x_1627_;
                        v_isShared_1691_ = v_isSharedCheck_1695_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1688_);
                        crate::leanh::lean_dec(v___x_1627_);
                        v___x_1690_ = crate::leanh::lean_box(0);
                        v_isShared_1691_ = v_isSharedCheck_1695_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1624_ = crate::leanh::lean_box(0);
                v___x_1625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1625_, 0, v___x_1624_);
                return v___x_1625_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1628_) == 1 {
                    v_val_1639_ = crate::leanh::lean_ctor_get(v_a_1628_, 0);
                    v_isSharedCheck_1686_ = (!crate::leanh::lean_is_exclusive(v_a_1628_)) as u8;
                    if v_isSharedCheck_1686_ == 0 {
                        v___x_1641_ = v_a_1628_;
                        v_isShared_1642_ = v_isSharedCheck_1686_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1639_);
                        crate::leanh::lean_dec(v_a_1628_);
                        v___x_1641_ = crate::leanh::lean_box(0);
                        v_isShared_1642_ = v_isSharedCheck_1686_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1628_);
                    v___y_1633_ = v_a_1619_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_discrCtorMap_1634_ = crate::leanh::lean_ctor_get(v___y_1633_, 0);
                v___x_1635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_discrCtorMap_1634_, v_fvarId_1618_);
                if v_isShared_1631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1630_, 0, v___x_1635_);
                    v___x_1637_ = v___x_1630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
                    v___x_1637_ = v_reuseFailAlloc_1638_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1637_;
            }
            5 => {
                v_value_1643_ = crate::leanh::lean_ctor_get(v_val_1639_, 3);
                crate::leanh::lean_inc(v_value_1643_);
                crate::leanh::lean_dec(v_val_1639_);
                match crate::leanh::lean_obj_tag(v_value_1643_) {
                    0 => {
                        v_value_1644_ = crate::leanh::lean_ctor_get(v_value_1643_, 0);
                        v_isSharedCheck_1662_ =
                            (!crate::leanh::lean_is_exclusive(v_value_1643_)) as u8;
                        if v_isSharedCheck_1662_ == 0 {
                            v___x_1646_ = v_value_1643_;
                            v_isShared_1647_ = v_isSharedCheck_1662_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_value_1644_);
                            crate::leanh::lean_dec(v_value_1643_);
                            v___x_1646_ = crate::leanh::lean_box(0);
                            v_isShared_1647_ = v_isSharedCheck_1662_;
                            state = 6;
                            continue;
                        }
                    }
                    3 => {
                        crate::leanh::lean_del_object(v___x_1641_);
                        crate::leanh::lean_del_object(v___x_1630_);
                        v_declName_1663_ = crate::leanh::lean_ctor_get(v_value_1643_, 0);
                        crate::leanh::lean_inc(v_declName_1663_);
                        v_args_1664_ = crate::leanh::lean_ctor_get(v_value_1643_, 2);
                        crate::leanh::lean_inc_ref(v_args_1664_);
                        crate::leanh::lean_dec_ref_known(v_value_1643_, 3);
                        v___x_1665_ = lean_st_ref_get(v_a_1621_);
                        v_env_1666_ = crate::leanh::lean_ctor_get(v___x_1665_, 0);
                        crate::leanh::lean_inc_ref(v_env_1666_);
                        crate::leanh::lean_dec(v___x_1665_);
                        v___x_1667_ = 0;
                        v___x_1668_ =
                            l_Lean_Environment_find_x3f(v_env_1666_, v_declName_1663_, v___x_1667_);
                        if crate::leanh::lean_obj_tag(v___x_1668_) == 1 {
                            v_val_1669_ = crate::leanh::lean_ctor_get(v___x_1668_, 0);
                            v_isSharedCheck_1685_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1668_)) as u8;
                            if v_isSharedCheck_1685_ == 0 {
                                v___x_1671_ = v___x_1668_;
                                v_isShared_1672_ = v_isSharedCheck_1685_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_1669_);
                                crate::leanh::lean_dec(v___x_1668_);
                                v___x_1671_ = crate::leanh::lean_box(0);
                                v_isShared_1672_ = v_isSharedCheck_1685_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1668_);
                            crate::leanh::lean_dec_ref(v_args_1664_);
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_value_1643_);
                        crate::leanh::lean_del_object(v___x_1641_);
                        v___y_1633_ = v_a_1619_;
                        state = 3;
                        continue;
                    }
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_value_1644_) == 0 {
                    crate::leanh::lean_del_object(v___x_1630_);
                    v_val_1648_ = crate::leanh::lean_ctor_get(v_value_1644_, 0);
                    v_isSharedCheck_1661_ = (!crate::leanh::lean_is_exclusive(v_value_1644_)) as u8;
                    if v_isSharedCheck_1661_ == 0 {
                        v___x_1650_ = v_value_1644_;
                        v_isShared_1651_ = v_isSharedCheck_1661_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1648_);
                        crate::leanh::lean_dec(v_value_1644_);
                        v___x_1650_ = crate::leanh::lean_box(0);
                        v_isShared_1651_ = v_isSharedCheck_1661_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1646_);
                    crate::leanh::lean_dec_ref(v_value_1644_);
                    crate::leanh::lean_del_object(v___x_1641_);
                    v___y_1633_ = v_a_1619_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v_isShared_1651_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1650_, 1);
                    v___x_1653_ = v___x_1650_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_val_1648_);
                    v___x_1653_ = v_reuseFailAlloc_1660_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1642_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1641_, 0, v___x_1653_);
                    v___x_1655_ = v___x_1641_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1653_);
                    v___x_1655_ = v_reuseFailAlloc_1659_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1655_);
                    v___x_1657_ = v___x_1646_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
                    v___x_1657_ = v_reuseFailAlloc_1658_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1657_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_val_1669_) == 6 {
                    v_val_1673_ = crate::leanh::lean_ctor_get(v_val_1669_, 0);
                    v_isSharedCheck_1684_ = (!crate::leanh::lean_is_exclusive(v_val_1669_)) as u8;
                    if v_isSharedCheck_1684_ == 0 {
                        v___x_1675_ = v_val_1669_;
                        v_isShared_1676_ = v_isSharedCheck_1684_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1673_);
                        crate::leanh::lean_dec(v_val_1669_);
                        v___x_1675_ = crate::leanh::lean_box(0);
                        v_isShared_1676_ = v_isSharedCheck_1684_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1671_);
                    crate::leanh::lean_dec(v_val_1669_);
                    crate::leanh::lean_dec_ref(v_args_1664_);
                    state = 1;
                    continue;
                }
            }
            12 => {
                v___x_1677_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1677_, 0, v_val_1673_);
                crate::leanh::lean_ctor_set(v___x_1677_, 1, v_args_1664_);
                if v_isShared_1672_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1671_, 0, v___x_1677_);
                    v___x_1679_ = v___x_1671_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1677_);
                    v___x_1679_ = v_reuseFailAlloc_1683_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_1676_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1675_, 0);
                    crate::leanh::lean_ctor_set(v___x_1675_, 0, v___x_1679_);
                    v___x_1681_ = v___x_1675_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
                    v___x_1681_ = v_reuseFailAlloc_1682_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1681_;
            }
            15 => {
                if v_isShared_1691_ == 0 {
                    v___x_1693_ = v___x_1690_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
                    v___x_1693_ = v_reuseFailAlloc_1694_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg___boxed(
    mut v_fvarId_1696_: *mut crate::leanh::LeanObject,
    mut v_a_1697_: *mut crate::leanh::LeanObject,
    mut v_a_1698_: *mut crate::leanh::LeanObject,
    mut v_a_1699_: *mut crate::leanh::LeanObject,
    mut v_a_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
        v_fvarId_1696_,
        v_a_1697_,
        v_a_1698_,
        v_a_1699_,
    );
    crate::leanh::lean_dec(v_a_1699_);
    crate::leanh::lean_dec(v_a_1698_);
    crate::leanh::lean_dec_ref(v_a_1697_);
    crate::leanh::lean_dec(v_fvarId_1696_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtor_x3f(
    mut v_fvarId_1702_: *mut crate::leanh::LeanObject,
    mut v_a_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1709_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
        v_fvarId_1702_,
        v_a_1703_,
        v_a_1705_,
        v_a_1707_,
    );
    return v___x_1709_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtor_x3f___boxed(
    mut v_fvarId_1710_: *mut crate::leanh::LeanObject,
    mut v_a_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
    mut v_a_1714_: *mut crate::leanh::LeanObject,
    mut v_a_1715_: *mut crate::leanh::LeanObject,
    mut v_a_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f(
        v_fvarId_1710_,
        v_a_1711_,
        v_a_1712_,
        v_a_1713_,
        v_a_1714_,
        v_a_1715_,
    );
    crate::leanh::lean_dec(v_a_1715_);
    crate::leanh::lean_dec_ref(v_a_1714_);
    crate::leanh::lean_dec(v_a_1713_);
    crate::leanh::lean_dec_ref(v_a_1712_);
    crate::leanh::lean_dec_ref(v_a_1711_);
    crate::leanh::lean_dec(v_fvarId_1710_);
    return v_res_1717_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0(
    mut v_00_u03b4_1718_: *mut crate::leanh::LeanObject,
    mut v_t_1719_: *mut crate::leanh::LeanObject,
    mut v_k_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_t_1719_, v_k_1720_);
    return v___x_1721_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___boxed(
    mut v_00_u03b4_1722_: *mut crate::leanh::LeanObject,
    mut v_t_1723_: *mut crate::leanh::LeanObject,
    mut v_k_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0(v_00_u03b4_1722_, v_t_1723_, v_k_1724_);
    crate::leanh::lean_dec(v_k_1724_);
    crate::leanh::lean_dec(v_t_1723_);
    return v_res_1725_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(
    mut v_fvarId_1726_: *mut crate::leanh::LeanObject,
    mut v_a_1727_: *mut crate::leanh::LeanObject,
    mut v_a_1728_: *mut crate::leanh::LeanObject,
    mut v_a_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1735_: u8 = 0;
    let mut v_val_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v_a_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1731_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
                    v_fvarId_1726_,
                    v_a_1727_,
                    v_a_1728_,
                    v_a_1729_,
                );
                if crate::leanh::lean_obj_tag(v___x_1731_) == 0 {
                    v_a_1732_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1752_ = (!crate::leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1752_ == 0 {
                        v___x_1734_ = v___x_1731_;
                        v_isShared_1735_ = v_isSharedCheck_1752_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1732_);
                        crate::leanh::lean_dec(v___x_1731_);
                        v___x_1734_ = crate::leanh::lean_box(0);
                        v_isShared_1735_ = v_isSharedCheck_1752_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1753_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1760_ = (!crate::leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1760_ == 0 {
                        v___x_1755_ = v___x_1731_;
                        v_isShared_1756_ = v_isSharedCheck_1760_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1753_);
                        crate::leanh::lean_dec(v___x_1731_);
                        v___x_1755_ = crate::leanh::lean_box(0);
                        v_isShared_1756_ = v_isSharedCheck_1760_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1732_) == 1 {
                    v_val_1736_ = crate::leanh::lean_ctor_get(v_a_1732_, 0);
                    v_isSharedCheck_1747_ = (!crate::leanh::lean_is_exclusive(v_a_1732_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1738_ = v_a_1732_;
                        v_isShared_1739_ = v_isSharedCheck_1747_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1736_);
                        crate::leanh::lean_dec(v_a_1732_);
                        v___x_1738_ = crate::leanh::lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1747_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1732_);
                    v___x_1748_ = crate::leanh::lean_box(0);
                    if v_isShared_1735_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1734_, 0, v___x_1748_);
                        v___x_1750_ = v___x_1734_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1751_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
                        v___x_1750_ = v_reuseFailAlloc_1751_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1740_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_1736_);
                crate::leanh::lean_dec(v_val_1736_);
                if v_isShared_1739_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1738_, 0, v___x_1740_);
                    v___x_1742_ = v___x_1738_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1740_);
                    v___x_1742_ = v_reuseFailAlloc_1746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1734_, 0, v___x_1742_);
                    v___x_1744_ = v___x_1734_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
                    v___x_1744_ = v_reuseFailAlloc_1745_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1744_;
            }
            5 => {
                return v___x_1750_;
            }
            6 => {
                if v_isShared_1756_ == 0 {
                    v___x_1758_ = v___x_1755_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
                    v___x_1758_ = v_reuseFailAlloc_1759_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg___boxed(
    mut v_fvarId_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
    mut v_a_1765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(
        v_fvarId_1761_,
        v_a_1762_,
        v_a_1763_,
        v_a_1764_,
    );
    crate::leanh::lean_dec(v_a_1764_);
    crate::leanh::lean_dec(v_a_1763_);
    crate::leanh::lean_dec_ref(v_a_1762_);
    crate::leanh::lean_dec(v_fvarId_1761_);
    return v_res_1766_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtorName_x3f(
    mut v_fvarId_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(
        v_fvarId_1767_,
        v_a_1768_,
        v_a_1770_,
        v_a_1772_,
    );
    return v___x_1774_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___boxed(
    mut v_fvarId_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_a_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f(
        v_fvarId_1775_,
        v_a_1776_,
        v_a_1777_,
        v_a_1778_,
        v_a_1779_,
        v_a_1780_,
    );
    crate::leanh::lean_dec(v_a_1780_);
    crate::leanh::lean_dec_ref(v_a_1779_);
    crate::leanh::lean_dec(v_a_1778_);
    crate::leanh::lean_dec_ref(v_a_1777_);
    crate::leanh::lean_dec_ref(v_a_1776_);
    crate::leanh::lean_dec(v_fvarId_1775_);
    return v_res_1782_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1783_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0);
    v___x_1785_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1785_, 0, v___x_1784_);
    return v___x_1785_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1);
    v___x_1787_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1788_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1788_, 0, v___x_1787_);
    crate::leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
    crate::leanh::lean_ctor_set(v___x_1788_, 2, v___x_1787_);
    crate::leanh::lean_ctor_set(v___x_1788_, 3, v___x_1787_);
    crate::leanh::lean_ctor_set(v___x_1788_, 4, v___x_1786_);
    crate::leanh::lean_ctor_set(v___x_1788_, 5, v___x_1786_);
    crate::leanh::lean_ctor_set(v___x_1788_, 6, v___x_1786_);
    crate::leanh::lean_ctor_set(v___x_1788_, 7, v___x_1786_);
    crate::leanh::lean_ctor_set(v___x_1788_, 8, v___x_1786_);
    crate::leanh::lean_ctor_set(v___x_1788_, 9, v___x_1786_);
    return v___x_1788_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1789_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1790_ = lean_mk_empty_array_with_capacity(v___x_1789_);
    v___x_1791_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1790_);
    return v___x_1791_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: usize = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = 5usize;
    v___x_1793_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1794_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1795_ = lean_mk_empty_array_with_capacity(v___x_1794_);
    v___x_1796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3);
    v___x_1797_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1797_, 0, v___x_1796_);
    crate::leanh::lean_ctor_set(v___x_1797_, 1, v___x_1795_);
    crate::leanh::lean_ctor_set(v___x_1797_, 2, v___x_1793_);
    crate::leanh::lean_ctor_set(v___x_1797_, 3, v___x_1793_);
    crate::leanh::lean_ctor_set_usize(v___x_1797_, 4, v___x_1792_);
    return v___x_1797_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = crate::leanh::lean_box(1);
    v___x_1799_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4);
    v___x_1800_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1);
    v___x_1801_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    crate::leanh::lean_ctor_set(v___x_1801_, 1, v___x_1799_);
    crate::leanh::lean_ctor_set(v___x_1801_, 2, v___x_1798_);
    return v___x_1801_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(
    mut v_msgData_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = lean_st_ref_get(v___y_1804_);
    v_env_1807_ = crate::leanh::lean_ctor_get(v___x_1806_, 0);
    crate::leanh::lean_inc_ref(v_env_1807_);
    crate::leanh::lean_dec(v___x_1806_);
    v_options_1808_ = crate::leanh::lean_ctor_get(v___y_1803_, 2);
    v___x_1809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2);
    v___x_1810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5);
    crate::leanh::lean_inc_ref(v_options_1808_);
    v___x_1811_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1811_, 0, v_env_1807_);
    crate::leanh::lean_ctor_set(v___x_1811_, 1, v___x_1809_);
    crate::leanh::lean_ctor_set(v___x_1811_, 2, v___x_1810_);
    crate::leanh::lean_ctor_set(v___x_1811_, 3, v_options_1808_);
    v___x_1812_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    crate::leanh::lean_ctor_set(v___x_1812_, 1, v_msgData_1802_);
    v___x_1813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    return v___x_1813_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___boxed(
    mut v_msgData_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(v_msgData_1814_, v___y_1815_, v___y_1816_);
    crate::leanh::lean_dec(v___y_1816_);
    crate::leanh::lean_dec_ref(v___y_1815_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(
    mut v_msg_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1823_ = crate::leanh::lean_ctor_get(v___y_1820_, 5);
                v___x_1824_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(v_msg_1819_, v___y_1820_, v___y_1821_);
                v_a_1825_ = crate::leanh::lean_ctor_get(v___x_1824_, 0);
                v_isSharedCheck_1833_ = (!crate::leanh::lean_is_exclusive(v___x_1824_)) as u8;
                if v_isSharedCheck_1833_ == 0 {
                    v___x_1827_ = v___x_1824_;
                    v_isShared_1828_ = v_isSharedCheck_1833_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1825_);
                    crate::leanh::lean_dec(v___x_1824_);
                    v___x_1827_ = crate::leanh::lean_box(0);
                    v_isShared_1828_ = v_isSharedCheck_1833_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1823_);
                v___x_1829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1829_, 0, v_ref_1823_);
                crate::leanh::lean_ctor_set(v___x_1829_, 1, v_a_1825_);
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1827_, 1);
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1829_);
                    v___x_1831_ = v___x_1827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
                    v___x_1831_ = v_reuseFailAlloc_1832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_msg_1834_: *mut crate::leanh::LeanObject,
    mut v___y_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1834_, v___y_1835_, v___y_1836_);
    crate::leanh::lean_dec(v___y_1836_);
    crate::leanh::lean_dec_ref(v___y_1835_);
    return v_res_1838_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_1839_: *mut crate::leanh::LeanObject,
    mut v_msg_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1856_: u8 = 0;
    let mut v_cancelTk_x3f_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1858_: u8 = 0;
    let mut v_inheritedTraceOptions_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1844_ = crate::leanh::lean_ctor_get(v___y_1841_, 0);
    v_fileMap_1845_ = crate::leanh::lean_ctor_get(v___y_1841_, 1);
    v_options_1846_ = crate::leanh::lean_ctor_get(v___y_1841_, 2);
    v_currRecDepth_1847_ = crate::leanh::lean_ctor_get(v___y_1841_, 3);
    v_maxRecDepth_1848_ = crate::leanh::lean_ctor_get(v___y_1841_, 4);
    v_ref_1849_ = crate::leanh::lean_ctor_get(v___y_1841_, 5);
    v_currNamespace_1850_ = crate::leanh::lean_ctor_get(v___y_1841_, 6);
    v_openDecls_1851_ = crate::leanh::lean_ctor_get(v___y_1841_, 7);
    v_initHeartbeats_1852_ = crate::leanh::lean_ctor_get(v___y_1841_, 8);
    v_maxHeartbeats_1853_ = crate::leanh::lean_ctor_get(v___y_1841_, 9);
    v_quotContext_1854_ = crate::leanh::lean_ctor_get(v___y_1841_, 10);
    v_currMacroScope_1855_ = crate::leanh::lean_ctor_get(v___y_1841_, 11);
    v_diag_1856_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1841_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1857_ = crate::leanh::lean_ctor_get(v___y_1841_, 12);
    v_suppressElabErrors_1858_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1841_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1859_ = crate::leanh::lean_ctor_get(v___y_1841_, 13);
    v_ref_1860_ = l_Lean_replaceRef(v_ref_1839_, v_ref_1849_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1859_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1857_);
    crate::leanh::lean_inc(v_currMacroScope_1855_);
    crate::leanh::lean_inc(v_quotContext_1854_);
    crate::leanh::lean_inc(v_maxHeartbeats_1853_);
    crate::leanh::lean_inc(v_initHeartbeats_1852_);
    crate::leanh::lean_inc(v_openDecls_1851_);
    crate::leanh::lean_inc(v_currNamespace_1850_);
    crate::leanh::lean_inc(v_maxRecDepth_1848_);
    crate::leanh::lean_inc(v_currRecDepth_1847_);
    crate::leanh::lean_inc_ref(v_options_1846_);
    crate::leanh::lean_inc_ref(v_fileMap_1845_);
    crate::leanh::lean_inc_ref(v_fileName_1844_);
    v___x_1861_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1861_, 0, v_fileName_1844_);
    crate::leanh::lean_ctor_set(v___x_1861_, 1, v_fileMap_1845_);
    crate::leanh::lean_ctor_set(v___x_1861_, 2, v_options_1846_);
    crate::leanh::lean_ctor_set(v___x_1861_, 3, v_currRecDepth_1847_);
    crate::leanh::lean_ctor_set(v___x_1861_, 4, v_maxRecDepth_1848_);
    crate::leanh::lean_ctor_set(v___x_1861_, 5, v_ref_1860_);
    crate::leanh::lean_ctor_set(v___x_1861_, 6, v_currNamespace_1850_);
    crate::leanh::lean_ctor_set(v___x_1861_, 7, v_openDecls_1851_);
    crate::leanh::lean_ctor_set(v___x_1861_, 8, v_initHeartbeats_1852_);
    crate::leanh::lean_ctor_set(v___x_1861_, 9, v_maxHeartbeats_1853_);
    crate::leanh::lean_ctor_set(v___x_1861_, 10, v_quotContext_1854_);
    crate::leanh::lean_ctor_set(v___x_1861_, 11, v_currMacroScope_1855_);
    crate::leanh::lean_ctor_set(v___x_1861_, 12, v_cancelTk_x3f_1857_);
    crate::leanh::lean_ctor_set(v___x_1861_, 13, v_inheritedTraceOptions_1859_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1861_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1856_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1861_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1858_,
    );
    v___x_1862_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1840_, v___x_1861_, v___y_1842_);
    crate::leanh::lean_dec_ref_known(v___x_1861_, 14);
    return v___x_1862_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_1863_: *mut crate::leanh::LeanObject,
    mut v_msg_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1868_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1863_, v_msg_1864_, v___y_1865_, v___y_1866_);
    crate::leanh::lean_dec(v___y_1866_);
    crate::leanh::lean_dec_ref(v___y_1865_);
    crate::leanh::lean_dec(v_ref_1863_);
    return v_res_1868_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
    v___x_1871_ = l_Lean_stringToMessageData(v___x_1870_);
    return v___x_1871_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
    v___x_1874_ = l_Lean_stringToMessageData(v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1876_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
    v___x_1877_ = l_Lean_stringToMessageData(v___x_1876_);
    return v___x_1877_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1880_ = l_Lean_stringToMessageData(v___x_1879_);
    return v___x_1880_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1883_ = l_Lean_stringToMessageData(v___x_1882_);
    return v___x_1883_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1886_ = l_Lean_stringToMessageData(v___x_1885_);
    return v___x_1886_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1888_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
    return v___x_1889_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1890_: *mut crate::leanh::LeanObject,
    mut v_declHint_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: u8 = 0;
    let mut v_isExporting_1897_: u8 = 0;
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: u8 = 0;
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1894_ = lean_st_ref_get(v___y_1892_);
                v_env_1895_ = crate::leanh::lean_ctor_get(v___x_1894_, 0);
                crate::leanh::lean_inc_ref(v_env_1895_);
                crate::leanh::lean_dec(v___x_1894_);
                v___x_1896_ = l_Lean_Name_isAnonymous(v_declHint_1891_);
                if v___x_1896_ == 0 {
                    v_isExporting_1897_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1895_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1897_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1895_);
                        crate::leanh::lean_dec(v_declHint_1891_);
                        v___x_1898_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1898_, 0, v_msg_1890_);
                        return v___x_1898_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1895_);
                        v___x_1899_ = l_Lean_Environment_setExporting(v_env_1895_, v___x_1896_);
                        crate::leanh::lean_inc(v_declHint_1891_);
                        crate::leanh::lean_inc_ref(v___x_1899_);
                        v___x_1900_ = l_Lean_Environment_contains(
                            v___x_1899_,
                            v_declHint_1891_,
                            v_isExporting_1897_,
                        );
                        if v___x_1900_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1899_);
                            crate::leanh::lean_dec_ref(v_env_1895_);
                            crate::leanh::lean_dec(v_declHint_1891_);
                            v___x_1901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1901_, 0, v_msg_1890_);
                            return v___x_1901_;
                        } else {
                            v___x_1902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2);
                            v___x_1903_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5);
                            v___x_1904_ = l_Lean_Options_empty;
                            v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1899_);
                            crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1902_);
                            crate::leanh::lean_ctor_set(v___x_1905_, 2, v___x_1903_);
                            crate::leanh::lean_ctor_set(v___x_1905_, 3, v___x_1904_);
                            crate::leanh::lean_inc(v_declHint_1891_);
                            v___x_1906_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1891_, v___x_1896_);
                            v_c_1907_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1907_, 0, v___x_1905_);
                            crate::leanh::lean_ctor_set(v_c_1907_, 1, v___x_1906_);
                            v___x_1908_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1895_,
                                v_declHint_1891_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1908_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1895_);
                                crate::leanh::lean_dec(v_declHint_1891_);
                                v___x_1909_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                                v___x_1910_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1910_, 0, v___x_1909_);
                                crate::leanh::lean_ctor_set(v___x_1910_, 1, v_c_1907_);
                                v___x_1911_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
                                v___x_1912_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1912_, 0, v___x_1910_);
                                crate::leanh::lean_ctor_set(v___x_1912_, 1, v___x_1911_);
                                v___x_1913_ = l_Lean_MessageData_note(v___x_1912_);
                                v___x_1914_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1914_, 0, v_msg_1890_);
                                crate::leanh::lean_ctor_set(v___x_1914_, 1, v___x_1913_);
                                v___x_1915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1915_, 0, v___x_1914_);
                                return v___x_1915_;
                            } else {
                                v_val_1916_ = crate::leanh::lean_ctor_get(v___x_1908_, 0);
                                v_isSharedCheck_1951_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1908_)) as u8;
                                if v_isSharedCheck_1951_ == 0 {
                                    v___x_1918_ = v___x_1908_;
                                    v_isShared_1919_ = v_isSharedCheck_1951_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1916_);
                                    crate::leanh::lean_dec(v___x_1908_);
                                    v___x_1918_ = crate::leanh::lean_box(0);
                                    v_isShared_1919_ = v_isSharedCheck_1951_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1895_);
                    crate::leanh::lean_dec(v_declHint_1891_);
                    v___x_1952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1952_, 0, v_msg_1890_);
                    return v___x_1952_;
                }
            }
            1 => {
                v___x_1920_ = crate::leanh::lean_box(0);
                v___x_1921_ = l_Lean_Environment_header(v_env_1895_);
                crate::leanh::lean_dec_ref(v_env_1895_);
                v___x_1922_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1921_);
                v_mod_1923_ = lean_array_get(v___x_1920_, v___x_1922_, v_val_1916_);
                crate::leanh::lean_dec(v_val_1916_);
                crate::leanh::lean_dec_ref(v___x_1922_);
                v___x_1924_ = l_Lean_isPrivateName(v_declHint_1891_);
                crate::leanh::lean_dec(v_declHint_1891_);
                if v___x_1924_ == 0 {
                    v___x_1925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                    v___x_1926_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_1925_);
                    crate::leanh::lean_ctor_set(v___x_1926_, 1, v_c_1907_);
                    v___x_1927_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_1928_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1928_, 0, v___x_1926_);
                    crate::leanh::lean_ctor_set(v___x_1928_, 1, v___x_1927_);
                    v___x_1929_ = l_Lean_MessageData_ofName(v_mod_1923_);
                    v___x_1930_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1930_, 0, v___x_1928_);
                    crate::leanh::lean_ctor_set(v___x_1930_, 1, v___x_1929_);
                    v___x_1931_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                    v___x_1932_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1932_, 0, v___x_1930_);
                    crate::leanh::lean_ctor_set(v___x_1932_, 1, v___x_1931_);
                    v___x_1933_ = l_Lean_MessageData_note(v___x_1932_);
                    v___x_1934_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1934_, 0, v_msg_1890_);
                    crate::leanh::lean_ctor_set(v___x_1934_, 1, v___x_1933_);
                    if v_isShared_1919_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1918_, 0);
                        crate::leanh::lean_ctor_set(v___x_1918_, 0, v___x_1934_);
                        v___x_1936_ = v___x_1918_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
                        v___x_1936_ = v_reuseFailAlloc_1937_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1938_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                    v___x_1939_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1939_, 0, v___x_1938_);
                    crate::leanh::lean_ctor_set(v___x_1939_, 1, v_c_1907_);
                    v___x_1940_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_1941_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1941_, 0, v___x_1939_);
                    crate::leanh::lean_ctor_set(v___x_1941_, 1, v___x_1940_);
                    v___x_1942_ = l_Lean_MessageData_ofName(v_mod_1923_);
                    v___x_1943_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1941_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 1, v___x_1942_);
                    v___x_1944_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_1945_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1945_, 0, v___x_1943_);
                    crate::leanh::lean_ctor_set(v___x_1945_, 1, v___x_1944_);
                    v___x_1946_ = l_Lean_MessageData_note(v___x_1945_);
                    v___x_1947_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1947_, 0, v_msg_1890_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 1, v___x_1946_);
                    if v_isShared_1919_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1918_, 0);
                        crate::leanh::lean_ctor_set(v___x_1918_, 0, v___x_1947_);
                        v___x_1949_ = v___x_1918_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
                        v___x_1949_ = v_reuseFailAlloc_1950_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1936_;
            }
            3 => {
                return v___x_1949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_1953_: *mut crate::leanh::LeanObject,
    mut v_declHint_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1953_, v_declHint_1954_, v___y_1955_);
    crate::leanh::lean_dec(v___y_1955_);
    return v_res_1957_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_1958_: *mut crate::leanh::LeanObject,
    mut v_declHint_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1963_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1958_, v_declHint_1959_, v___y_1961_);
                v_a_1964_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                v_isSharedCheck_1973_ = (!crate::leanh::lean_is_exclusive(v___x_1963_)) as u8;
                if v_isSharedCheck_1973_ == 0 {
                    v___x_1966_ = v___x_1963_;
                    v_isShared_1967_ = v_isSharedCheck_1973_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1964_);
                    crate::leanh::lean_dec(v___x_1963_);
                    v___x_1966_ = crate::leanh::lean_box(0);
                    v_isShared_1967_ = v_isSharedCheck_1973_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1968_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1969_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1969_, 0, v___x_1968_);
                crate::leanh::lean_ctor_set(v___x_1969_, 1, v_a_1964_);
                if v_isShared_1967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1966_, 0, v___x_1969_);
                    v___x_1971_ = v___x_1966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v_msg_1974_: *mut crate::leanh::LeanObject,
    mut v_declHint_1975_: *mut crate::leanh::LeanObject,
    mut v___y_1976_: *mut crate::leanh::LeanObject,
    mut v___y_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1979_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1974_, v_declHint_1975_, v___y_1976_, v___y_1977_);
    crate::leanh::lean_dec(v___y_1977_);
    crate::leanh::lean_dec_ref(v___y_1976_);
    return v_res_1979_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_1980_: *mut crate::leanh::LeanObject,
    mut v_msg_1981_: *mut crate::leanh::LeanObject,
    mut v_declHint_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1986_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1981_, v_declHint_1982_, v___y_1983_, v___y_1984_);
    v_a_1987_ = crate::leanh::lean_ctor_get(v___x_1986_, 0);
    crate::leanh::lean_inc(v_a_1987_);
    crate::leanh::lean_dec_ref(v___x_1986_);
    v___x_1988_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1980_, v_a_1987_, v___y_1983_, v___y_1984_);
    return v___x_1988_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_1989_: *mut crate::leanh::LeanObject,
    mut v_msg_1990_: *mut crate::leanh::LeanObject,
    mut v_declHint_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1995_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1989_, v_msg_1990_, v_declHint_1991_, v___y_1992_, v___y_1993_);
    crate::leanh::lean_dec(v___y_1993_);
    crate::leanh::lean_dec_ref(v___y_1992_);
    crate::leanh::lean_dec(v_ref_1989_);
    return v_res_1995_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
    return v___x_1998_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2000_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
    return v___x_2001_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2002_: *mut crate::leanh::LeanObject,
    mut v_constName_2003_: *mut crate::leanh::LeanObject,
    mut v___y_2004_: *mut crate::leanh::LeanObject,
    mut v___y_2005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2008_ = 0;
    crate::leanh::lean_inc(v_constName_2003_);
    v___x_2009_ = l_Lean_MessageData_ofConstName(v_constName_2003_, v___x_2008_);
    v___x_2010_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2010_, 0, v___x_2007_);
    crate::leanh::lean_ctor_set(v___x_2010_, 1, v___x_2009_);
    v___x_2011_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2012_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2012_, 0, v___x_2010_);
    crate::leanh::lean_ctor_set(v___x_2012_, 1, v___x_2011_);
    v___x_2013_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2002_, v___x_2012_, v_constName_2003_, v___y_2004_, v___y_2005_);
    return v___x_2013_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2014_: *mut crate::leanh::LeanObject,
    mut v_constName_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
    mut v___y_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2019_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2014_, v_constName_2015_, v___y_2016_, v___y_2017_);
    crate::leanh::lean_dec(v___y_2017_);
    crate::leanh::lean_dec_ref(v___y_2016_);
    crate::leanh::lean_dec(v_ref_2014_);
    return v_res_2019_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg(
    mut v_constName_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
    mut v___y_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2024_ = crate::leanh::lean_ctor_get(v___y_2021_, 5);
    v___x_2025_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2024_, v_constName_2020_, v___y_2021_, v___y_2022_);
    return v___x_2025_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
    mut v___y_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg(v_constName_2026_, v___y_2027_, v___y_2028_);
    crate::leanh::lean_dec(v___y_2028_);
    crate::leanh::lean_dec_ref(v___y_2027_);
    return v_res_2030_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0(
    mut v_constName_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2035_ = lean_st_ref_get(v___y_2033_);
                v_env_2036_ = crate::leanh::lean_ctor_get(v___x_2035_, 0);
                crate::leanh::lean_inc_ref(v_env_2036_);
                crate::leanh::lean_dec(v___x_2035_);
                v___x_2037_ = 0;
                crate::leanh::lean_inc(v_constName_2031_);
                v___x_2038_ =
                    l_Lean_Environment_find_x3f(v_env_2036_, v_constName_2031_, v___x_2037_);
                if crate::leanh::lean_obj_tag(v___x_2038_) == 0 {
                    v___x_2039_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg(v_constName_2031_, v___y_2032_, v___y_2033_);
                    return v___x_2039_;
                } else {
                    crate::leanh::lean_dec(v_constName_2031_);
                    v_val_2040_ = crate::leanh::lean_ctor_get(v___x_2038_, 0);
                    v_isSharedCheck_2047_ = (!crate::leanh::lean_is_exclusive(v___x_2038_)) as u8;
                    if v_isSharedCheck_2047_ == 0 {
                        v___x_2042_ = v___x_2038_;
                        v_isShared_2043_ = v_isSharedCheck_2047_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2040_);
                        crate::leanh::lean_dec(v___x_2038_);
                        v___x_2042_ = crate::leanh::lean_box(0);
                        v_isShared_2043_ = v_isSharedCheck_2047_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2043_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2042_, 0);
                    v___x_2045_ = v___x_2042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2046_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_val_2040_);
                    v___x_2045_ = v_reuseFailAlloc_2046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0___boxed(
    mut v_constName_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2052_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0(
        v_constName_2048_,
        v___y_2049_,
        v___y_2050_,
    );
    crate::leanh::lean_dec(v___y_2050_);
    crate::leanh::lean_dec_ref(v___y_2049_);
    return v_res_2052_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__2(
    mut v_sz_2053_: usize,
    mut v_i_2054_: usize,
    mut v_bs_2055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: u8 = 0;
    let mut v_v_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: usize = 0;
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2056_ = lean_usize_dec_lt(v_i_2054_, v_sz_2053_);
                if v___x_2056_ == 0 {
                    return v_bs_2055_;
                } else {
                    v_v_2057_ = lean_array_uget(v_bs_2055_, v_i_2054_);
                    v___x_2058_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2059_ = lean_array_uset(v_bs_2055_, v_i_2054_, v___x_2058_);
                    if crate::leanh::lean_obj_tag(v_v_2057_) == 1 {
                        v_fvarId_2066_ = crate::leanh::lean_ctor_get(v_v_2057_, 0);
                        crate::leanh::lean_inc(v_fvarId_2066_);
                        crate::leanh::lean_dec_ref_known(v_v_2057_, 1);
                        v___x_2067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2067_, 0, v_fvarId_2066_);
                        v___y_2061_ = v___x_2067_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2068_ = l_Lean_Expr_isErased(v_v_2057_);
                        if v___x_2068_ == 0 {
                            v___x_2069_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2069_, 0, v_v_2057_);
                            v___y_2061_ = v___x_2069_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_v_2057_);
                            v___x_2070_ = crate::leanh::lean_box(0);
                            v___y_2061_ = v___x_2070_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2062_ = 1usize;
                v___x_2063_ = lean_usize_add(v_i_2054_, v___x_2062_);
                v___x_2064_ = lean_array_uset(v_bs_x27_2059_, v_i_2054_, v___y_2061_);
                v_i_2054_ = v___x_2063_;
                v_bs_2055_ = v___x_2064_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__2___boxed(
    mut v_sz_2071_: *mut crate::leanh::LeanObject,
    mut v_i_2072_: *mut crate::leanh::LeanObject,
    mut v_bs_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2074_: usize = 0;
    let mut v_i_boxed_2075_: usize = 0;
    let mut v_res_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2074_ = crate::leanh::lean_unbox_usize(v_sz_2071_);
    crate::leanh::lean_dec(v_sz_2071_);
    v_i_boxed_2075_ = crate::leanh::lean_unbox_usize(v_i_2072_);
    crate::leanh::lean_dec(v_i_2072_);
    v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__2(v_sz_boxed_2074_, v_i_boxed_2075_, v_bs_2073_);
    return v_res_2076_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1___redArg(
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v_b_2078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v___x_2085_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2079_ = crate::leanh::lean_ctor_get(v_a_2077_, 0);
                v_start_2080_ = crate::leanh::lean_ctor_get(v_a_2077_, 1);
                v_stop_2081_ = crate::leanh::lean_ctor_get(v_a_2077_, 2);
                v_isSharedCheck_2094_ = (!crate::leanh::lean_is_exclusive(v_a_2077_)) as u8;
                if v_isSharedCheck_2094_ == 0 {
                    v___x_2083_ = v_a_2077_;
                    v_isShared_2084_ = v_isSharedCheck_2094_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_2081_);
                    crate::leanh::lean_inc(v_start_2080_);
                    crate::leanh::lean_inc(v_array_2079_);
                    crate::leanh::lean_dec(v_a_2077_);
                    v___x_2083_ = crate::leanh::lean_box(0);
                    v_isShared_2084_ = v_isSharedCheck_2094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2085_ = lean_nat_dec_lt(v_start_2080_, v_stop_2081_);
                if v___x_2085_ == 0 {
                    crate::leanh::lean_del_object(v___x_2083_);
                    crate::leanh::lean_dec(v_stop_2081_);
                    crate::leanh::lean_dec(v_start_2080_);
                    crate::leanh::lean_dec_ref(v_array_2079_);
                    return v_b_2078_;
                } else {
                    v___x_2086_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2087_ = lean_nat_add(v_start_2080_, v___x_2086_);
                    crate::leanh::lean_inc_ref(v_array_2079_);
                    if v_isShared_2084_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2083_, 1, v___x_2087_);
                        v___x_2089_ = v___x_2083_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2093_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_array_2079_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2087_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_stop_2081_);
                        v___x_2089_ = v_reuseFailAlloc_2093_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2090_ = lean_array_fget(v_array_2079_, v_start_2080_);
                crate::leanh::lean_dec(v_start_2080_);
                crate::leanh::lean_dec_ref(v_array_2079_);
                v___x_2091_ = lean_array_push(v_b_2078_, v___x_2090_);
                v_a_2077_ = v___x_2089_;
                v_b_2078_ = v___x_2091_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2095_ = crate::leanh::lean_box(0);
    v_dummy_2096_ = l_Lean_Expr_sort___override(v___x_2095_);
    return v_dummy_2096_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(
    mut v_type_2099_: *mut crate::leanh::LeanObject,
    mut v_ind_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: u8 = 0;
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v_val_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v_numParams_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2136_: usize = 0;
    let mut v___x_2137_: usize = 0;
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2151_: u8 = 0;
    let mut v_a_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_2104_ = l_Lean_Expr_headBeta(v_type_2099_);
                v___x_2105_ = l_Lean_Expr_getAppFn(v_type_2104_);
                if crate::leanh::lean_obj_tag(v___x_2105_) == 4 {
                    v_declName_2106_ = crate::leanh::lean_ctor_get(v___x_2105_, 0);
                    crate::leanh::lean_inc(v_declName_2106_);
                    v_us_2107_ = crate::leanh::lean_ctor_get(v___x_2105_, 1);
                    crate::leanh::lean_inc(v_us_2107_);
                    crate::leanh::lean_dec_ref_known(v___x_2105_, 2);
                    v___x_2108_ = lean_name_eq(v_declName_2106_, v_ind_2100_);
                    if v___x_2108_ == 0 {
                        crate::leanh::lean_dec(v_us_2107_);
                        crate::leanh::lean_dec(v_declName_2106_);
                        crate::leanh::lean_dec_ref(v_type_2104_);
                        v___x_2109_ = crate::leanh::lean_box(0);
                        v___x_2110_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2110_, 0, v___x_2109_);
                        return v___x_2110_;
                    } else {
                        v___x_2111_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0(v_declName_2106_, v_a_2101_, v_a_2102_);
                        if crate::leanh::lean_obj_tag(v___x_2111_) == 0 {
                            v_a_2112_ = crate::leanh::lean_ctor_get(v___x_2111_, 0);
                            v_isSharedCheck_2151_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2111_)) as u8;
                            if v_isSharedCheck_2151_ == 0 {
                                v___x_2114_ = v___x_2111_;
                                v_isShared_2115_ = v_isSharedCheck_2151_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2112_);
                                crate::leanh::lean_dec(v___x_2111_);
                                v___x_2114_ = crate::leanh::lean_box(0);
                                v_isShared_2115_ = v_isSharedCheck_2151_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_us_2107_);
                            crate::leanh::lean_dec_ref(v_type_2104_);
                            v_a_2152_ = crate::leanh::lean_ctor_get(v___x_2111_, 0);
                            v_isSharedCheck_2159_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2111_)) as u8;
                            if v_isSharedCheck_2159_ == 0 {
                                v___x_2154_ = v___x_2111_;
                                v_isShared_2155_ = v_isSharedCheck_2159_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2152_);
                                crate::leanh::lean_dec(v___x_2111_);
                                v___x_2154_ = crate::leanh::lean_box(0);
                                v_isShared_2155_ = v_isSharedCheck_2159_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2105_);
                    crate::leanh::lean_dec_ref(v_type_2104_);
                    v___x_2160_ = crate::leanh::lean_box(0);
                    v___x_2161_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2161_, 0, v___x_2160_);
                    return v___x_2161_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2112_) == 5 {
                    v_val_2116_ = crate::leanh::lean_ctor_get(v_a_2112_, 0);
                    v_isSharedCheck_2146_ = (!crate::leanh::lean_is_exclusive(v_a_2112_)) as u8;
                    if v_isSharedCheck_2146_ == 0 {
                        v___x_2118_ = v_a_2112_;
                        v_isShared_2119_ = v_isSharedCheck_2146_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2116_);
                        crate::leanh::lean_dec(v_a_2112_);
                        v___x_2118_ = crate::leanh::lean_box(0);
                        v_isShared_2119_ = v_isSharedCheck_2146_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2112_);
                    crate::leanh::lean_dec(v_us_2107_);
                    crate::leanh::lean_dec_ref(v_type_2104_);
                    v___x_2147_ = crate::leanh::lean_box(0);
                    if v_isShared_2115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2114_, 0, v___x_2147_);
                        v___x_2149_ = v___x_2114_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2150_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
                        v___x_2149_ = v_reuseFailAlloc_2150_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_numParams_2120_ = crate::leanh::lean_ctor_get(v_val_2116_, 1);
                crate::leanh::lean_inc(v_numParams_2120_);
                crate::leanh::lean_dec_ref(v_val_2116_);
                v___x_2121_ = l_Lean_Expr_getAppNumArgs(v_type_2104_);
                v___x_2122_ = lean_nat_dec_le(v_numParams_2120_, v___x_2121_);
                if v___x_2122_ == 0 {
                    crate::leanh::lean_dec(v___x_2121_);
                    crate::leanh::lean_dec(v_numParams_2120_);
                    crate::leanh::lean_del_object(v___x_2118_);
                    crate::leanh::lean_dec(v_us_2107_);
                    crate::leanh::lean_dec_ref(v_type_2104_);
                    v___x_2123_ = crate::leanh::lean_box(0);
                    if v_isShared_2115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2114_, 0, v___x_2123_);
                        v___x_2125_ = v___x_2114_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
                        v___x_2125_ = v_reuseFailAlloc_2126_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_dummy_2127_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0,
                    );
                    crate::leanh::lean_inc(v___x_2121_);
                    v___x_2128_ = lean_mk_array(v___x_2121_, v_dummy_2127_);
                    v___x_2129_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2130_ = lean_nat_sub(v___x_2121_, v___x_2129_);
                    crate::leanh::lean_dec(v___x_2121_);
                    v___x_2131_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_type_2104_,
                        v___x_2128_,
                        v___x_2130_,
                    );
                    v___x_2132_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2133_ =
                        l_Array_toSubarray___redArg(v___x_2131_, v___x_2132_, v_numParams_2120_);
                    v___x_2134_ = l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__1;
                    v___x_2135_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1___redArg(v___x_2133_, v___x_2134_);
                    v_sz_2136_ = lean_array_size(v___x_2135_);
                    v___x_2137_ = 0usize;
                    v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__2(v_sz_2136_, v___x_2137_, v___x_2135_);
                    v___x_2139_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2139_, 0, v_us_2107_);
                    crate::leanh::lean_ctor_set(v___x_2139_, 1, v___x_2138_);
                    if v_isShared_2119_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2118_, 1);
                        crate::leanh::lean_ctor_set(v___x_2118_, 0, v___x_2139_);
                        v___x_2141_ = v___x_2118_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2139_);
                        v___x_2141_ = v_reuseFailAlloc_2145_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2125_;
            }
            4 => {
                if v_isShared_2115_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2114_, 0, v___x_2141_);
                    v___x_2143_ = v___x_2114_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
                    v___x_2143_ = v_reuseFailAlloc_2144_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2143_;
            }
            6 => {
                return v___x_2149_;
            }
            7 => {
                if v_isShared_2155_ == 0 {
                    v___x_2157_ = v___x_2154_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
                    v___x_2157_ = v_reuseFailAlloc_2158_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___boxed(
    mut v_type_2162_: *mut crate::leanh::LeanObject,
    mut v_ind_2163_: *mut crate::leanh::LeanObject,
    mut v_a_2164_: *mut crate::leanh::LeanObject,
    mut v_a_2165_: *mut crate::leanh::LeanObject,
    mut v_a_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ =
        l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(v_type_2162_, v_ind_2163_, v_a_2164_, v_a_2165_);
    crate::leanh::lean_dec(v_a_2165_);
    crate::leanh::lean_dec_ref(v_a_2164_);
    crate::leanh::lean_dec(v_ind_2163_);
    return v_res_2167_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1(
    mut v_inst_2168_: *mut crate::leanh::LeanObject,
    mut v_R_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
    mut v_b_2171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1___redArg(v_a_2170_, v_b_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0(
    mut v_00_u03b1_2173_: *mut crate::leanh::LeanObject,
    mut v_constName_2174_: *mut crate::leanh::LeanObject,
    mut v___y_2175_: *mut crate::leanh::LeanObject,
    mut v___y_2176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg(v_constName_2174_, v___y_2175_, v___y_2176_);
    return v___x_2178_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_2179_: *mut crate::leanh::LeanObject,
    mut v_constName_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0(v_00_u03b1_2179_, v_constName_2180_, v___y_2181_, v___y_2182_);
    crate::leanh::lean_dec(v___y_2182_);
    crate::leanh::lean_dec_ref(v___y_2181_);
    return v_res_2184_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2185_: *mut crate::leanh::LeanObject,
    mut v_ref_2186_: *mut crate::leanh::LeanObject,
    mut v_constName_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
    mut v___y_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2186_, v_constName_2187_, v___y_2188_, v___y_2189_);
    return v___x_2191_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2192_: *mut crate::leanh::LeanObject,
    mut v_ref_2193_: *mut crate::leanh::LeanObject,
    mut v_constName_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2192_, v_ref_2193_, v_constName_2194_, v___y_2195_, v___y_2196_);
    crate::leanh::lean_dec(v___y_2196_);
    crate::leanh::lean_dec_ref(v___y_2195_);
    crate::leanh::lean_dec(v_ref_2193_);
    return v_res_2198_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_2199_: *mut crate::leanh::LeanObject,
    mut v_ref_2200_: *mut crate::leanh::LeanObject,
    mut v_msg_2201_: *mut crate::leanh::LeanObject,
    mut v_declHint_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2206_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2200_, v_msg_2201_, v_declHint_2202_, v___y_2203_, v___y_2204_);
    return v___x_2206_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_2207_: *mut crate::leanh::LeanObject,
    mut v_ref_2208_: *mut crate::leanh::LeanObject,
    mut v_msg_2209_: *mut crate::leanh::LeanObject,
    mut v_declHint_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2214_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2207_, v_ref_2208_, v_msg_2209_, v_declHint_2210_, v___y_2211_, v___y_2212_);
    crate::leanh::lean_dec(v___y_2212_);
    crate::leanh::lean_dec_ref(v___y_2211_);
    crate::leanh::lean_dec(v_ref_2208_);
    return v_res_2214_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_2215_: *mut crate::leanh::LeanObject,
    mut v_declHint_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2215_, v_declHint_2216_, v___y_2218_);
    return v___x_2220_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_2221_: *mut crate::leanh::LeanObject,
    mut v_declHint_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2226_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2221_, v_declHint_2222_, v___y_2223_, v___y_2224_);
    crate::leanh::lean_dec(v___y_2224_);
    crate::leanh::lean_dec_ref(v___y_2223_);
    return v_res_2226_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_2227_: *mut crate::leanh::LeanObject,
    mut v_ref_2228_: *mut crate::leanh::LeanObject,
    mut v_msg_2229_: *mut crate::leanh::LeanObject,
    mut v___y_2230_: *mut crate::leanh::LeanObject,
    mut v___y_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2233_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2228_, v_msg_2229_, v___y_2230_, v___y_2231_);
    return v___x_2233_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_2234_: *mut crate::leanh::LeanObject,
    mut v_ref_2235_: *mut crate::leanh::LeanObject,
    mut v_msg_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
    mut v___y_2239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2234_, v_ref_2235_, v_msg_2236_, v___y_2237_, v___y_2238_);
    crate::leanh::lean_dec(v___y_2238_);
    crate::leanh::lean_dec_ref(v___y_2237_);
    crate::leanh::lean_dec(v_ref_2235_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(
    mut v_00_u03b1_2241_: *mut crate::leanh::LeanObject,
    mut v_msg_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2246_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2242_, v___y_2243_, v___y_2244_);
    return v___x_2246_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_2247_: *mut crate::leanh::LeanObject,
    mut v_msg_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2247_, v_msg_2248_, v___y_2249_, v___y_2250_);
    crate::leanh::lean_dec(v___y_2250_);
    crate::leanh::lean_dec_ref(v___y_2249_);
    return v_res_2252_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_x_2253_: *mut crate::leanh::LeanObject,
    mut v_x_2254_: *mut crate::leanh::LeanObject,
    mut v_x_2255_: *mut crate::leanh::LeanObject,
    mut v_x_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2261_: u8 = 0;
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2257_ = crate::leanh::lean_ctor_get(v_x_2253_, 0);
                v_vs_2258_ = crate::leanh::lean_ctor_get(v_x_2253_, 1);
                v_isSharedCheck_2282_ = (!crate::leanh::lean_is_exclusive(v_x_2253_)) as u8;
                if v_isSharedCheck_2282_ == 0 {
                    v___x_2260_ = v_x_2253_;
                    v_isShared_2261_ = v_isSharedCheck_2282_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2258_);
                    crate::leanh::lean_inc(v_ks_2257_);
                    crate::leanh::lean_dec(v_x_2253_);
                    v___x_2260_ = crate::leanh::lean_box(0);
                    v_isShared_2261_ = v_isSharedCheck_2282_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2262_ = lean_array_get_size(v_ks_2257_);
                v___x_2263_ = lean_nat_dec_lt(v_x_2254_, v___x_2262_);
                if v___x_2263_ == 0 {
                    crate::leanh::lean_dec(v_x_2254_);
                    v___x_2264_ = lean_array_push(v_ks_2257_, v_x_2255_);
                    v___x_2265_ = lean_array_push(v_vs_2258_, v_x_2256_);
                    if v_isShared_2261_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2260_, 1, v___x_2265_);
                        crate::leanh::lean_ctor_set(v___x_2260_, 0, v___x_2264_);
                        v___x_2267_ = v___x_2260_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2268_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2264_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2265_);
                        v___x_2267_ = v_reuseFailAlloc_2268_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2269_ = lean_array_fget_borrowed(v_ks_2257_, v_x_2254_);
                    v___x_2270_ = lean_expr_eqv(v_x_2255_, v_k_x27_2269_);
                    if v___x_2270_ == 0 {
                        if v_isShared_2261_ == 0 {
                            v___x_2272_ = v___x_2260_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2276_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_ks_2257_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_vs_2258_);
                            v___x_2272_ = v_reuseFailAlloc_2276_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2277_ = lean_array_fset(v_ks_2257_, v_x_2254_, v_x_2255_);
                        v___x_2278_ = lean_array_fset(v_vs_2258_, v_x_2254_, v_x_2256_);
                        crate::leanh::lean_dec(v_x_2254_);
                        if v_isShared_2261_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2260_, 1, v___x_2278_);
                            crate::leanh::lean_ctor_set(v___x_2260_, 0, v___x_2277_);
                            v___x_2280_ = v___x_2260_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2281_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2277_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2278_);
                            v___x_2280_ = v_reuseFailAlloc_2281_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2267_;
            }
            3 => {
                v___x_2273_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2274_ = lean_nat_add(v_x_2254_, v___x_2273_);
                crate::leanh::lean_dec(v_x_2254_);
                v_x_2253_ = v___x_2272_;
                v_x_2254_ = v___x_2274_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5___redArg(
    mut v_n_2283_: *mut crate::leanh::LeanObject,
    mut v_k_2284_: *mut crate::leanh::LeanObject,
    mut v_v_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2287_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5_spec__6___redArg(v_n_2283_, v___x_2286_, v_k_2284_, v_v_2285_);
    return v___x_2287_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_2288_: usize = 0;
    let mut v___x_2289_: usize = 0;
    let mut v___x_2290_: usize = 0;
    v___x_2288_ = 5usize;
    v___x_2289_ = 1usize;
    v___x_2290_ = lean_usize_shift_left(v___x_2289_, v___x_2288_);
    return v___x_2290_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: usize = 0;
    v___x_2291_ = 1usize;
    v___x_2292_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0);
    v___x_2293_ = lean_usize_sub(v___x_2292_, v___x_2291_);
    return v___x_2293_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2294_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(
    mut v_x_2295_: *mut crate::leanh::LeanObject,
    mut v_x_2296_: usize,
    mut v_x_2297_: usize,
    mut v_x_2298_: *mut crate::leanh::LeanObject,
    mut v_x_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: usize = 0;
    let mut v___x_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: usize = 0;
    let mut v_j_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2310_: u8 = 0;
    let mut v_v_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_node_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2342_: u8 = 0;
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut v_unused_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2350_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2355_: u8 = 0;
    let mut v_ks_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v_reuseFailAlloc_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2295_) == 0 {
                    v_es_2300_ = crate::leanh::lean_ctor_get(v_x_2295_, 0);
                    v___x_2301_ = 5usize;
                    v___x_2302_ = 1usize;
                    v___x_2303_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1);
                    v___x_2304_ = lean_usize_land(v_x_2296_, v___x_2303_);
                    v_j_2305_ = lean_usize_to_nat(v___x_2304_);
                    v___x_2306_ = lean_array_get_size(v_es_2300_);
                    v___x_2307_ = lean_nat_dec_lt(v_j_2305_, v___x_2306_);
                    if v___x_2307_ == 0 {
                        crate::leanh::lean_dec(v_j_2305_);
                        crate::leanh::lean_dec(v_x_2299_);
                        crate::leanh::lean_dec_ref(v_x_2298_);
                        return v_x_2295_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2300_);
                        v_isSharedCheck_2344_ = (!crate::leanh::lean_is_exclusive(v_x_2295_)) as u8;
                        if v_isSharedCheck_2344_ == 0 {
                            v_unused_2345_ = crate::leanh::lean_ctor_get(v_x_2295_, 0);
                            crate::leanh::lean_dec(v_unused_2345_);
                            v___x_2309_ = v_x_2295_;
                            v_isShared_2310_ = v_isSharedCheck_2344_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2295_);
                            v___x_2309_ = crate::leanh::lean_box(0);
                            v_isShared_2310_ = v_isSharedCheck_2344_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2346_ = crate::leanh::lean_ctor_get(v_x_2295_, 0);
                    v_vs_2347_ = crate::leanh::lean_ctor_get(v_x_2295_, 1);
                    v_isSharedCheck_2367_ = (!crate::leanh::lean_is_exclusive(v_x_2295_)) as u8;
                    if v_isSharedCheck_2367_ == 0 {
                        v___x_2349_ = v_x_2295_;
                        v_isShared_2350_ = v_isSharedCheck_2367_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2347_);
                        crate::leanh::lean_inc(v_ks_2346_);
                        crate::leanh::lean_dec(v_x_2295_);
                        v___x_2349_ = crate::leanh::lean_box(0);
                        v_isShared_2350_ = v_isSharedCheck_2367_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2311_ = lean_array_fget(v_es_2300_, v_j_2305_);
                v___x_2312_ = crate::leanh::lean_box(0);
                v_xs_x27_2313_ = lean_array_fset(v_es_2300_, v_j_2305_, v___x_2312_);
                match crate::leanh::lean_obj_tag(v_v_2311_) {
                    0 => {
                        v_key_2320_ = crate::leanh::lean_ctor_get(v_v_2311_, 0);
                        v_val_2321_ = crate::leanh::lean_ctor_get(v_v_2311_, 1);
                        v_isSharedCheck_2331_ = (!crate::leanh::lean_is_exclusive(v_v_2311_)) as u8;
                        if v_isSharedCheck_2331_ == 0 {
                            v___x_2323_ = v_v_2311_;
                            v_isShared_2324_ = v_isSharedCheck_2331_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2321_);
                            crate::leanh::lean_inc(v_key_2320_);
                            crate::leanh::lean_dec(v_v_2311_);
                            v___x_2323_ = crate::leanh::lean_box(0);
                            v_isShared_2324_ = v_isSharedCheck_2331_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2332_ = crate::leanh::lean_ctor_get(v_v_2311_, 0);
                        v_isSharedCheck_2342_ = (!crate::leanh::lean_is_exclusive(v_v_2311_)) as u8;
                        if v_isSharedCheck_2342_ == 0 {
                            v___x_2334_ = v_v_2311_;
                            v_isShared_2335_ = v_isSharedCheck_2342_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2332_);
                            crate::leanh::lean_dec(v_v_2311_);
                            v___x_2334_ = crate::leanh::lean_box(0);
                            v_isShared_2335_ = v_isSharedCheck_2342_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2343_, 0, v_x_2298_);
                        crate::leanh::lean_ctor_set(v___x_2343_, 1, v_x_2299_);
                        v___y_2315_ = v___x_2343_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2316_ = lean_array_fset(v_xs_x27_2313_, v_j_2305_, v___y_2315_);
                crate::leanh::lean_dec(v_j_2305_);
                if v_isShared_2310_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2309_, 0, v___x_2316_);
                    v___x_2318_ = v___x_2309_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2318_;
            }
            4 => {
                v___x_2325_ = lean_expr_eqv(v_x_2298_, v_key_2320_);
                if v___x_2325_ == 0 {
                    crate::leanh::lean_del_object(v___x_2323_);
                    v___x_2326_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2320_,
                        v_val_2321_,
                        v_x_2298_,
                        v_x_2299_,
                    );
                    v___x_2327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2327_, 0, v___x_2326_);
                    v___y_2315_ = v___x_2327_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2321_);
                    crate::leanh::lean_dec(v_key_2320_);
                    if v_isShared_2324_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2323_, 1, v_x_2299_);
                        crate::leanh::lean_ctor_set(v___x_2323_, 0, v_x_2298_);
                        v___x_2329_ = v___x_2323_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2330_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_x_2298_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_x_2299_);
                        v___x_2329_ = v_reuseFailAlloc_2330_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2315_ = v___x_2329_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2336_ = lean_usize_shift_right(v_x_2296_, v___x_2301_);
                v___x_2337_ = lean_usize_add(v_x_2297_, v___x_2302_);
                v___x_2338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(v_node_2332_, v___x_2336_, v___x_2337_, v_x_2298_, v_x_2299_);
                if v_isShared_2335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2334_, 0, v___x_2338_);
                    v___x_2340_ = v___x_2334_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2341_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
                    v___x_2340_ = v_reuseFailAlloc_2341_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2315_ = v___x_2340_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2350_ == 0 {
                    v___x_2352_ = v___x_2349_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2366_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_ks_2346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_vs_2347_);
                    v___x_2352_ = v_reuseFailAlloc_2366_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2353_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5___redArg(v___x_2352_, v_x_2298_, v_x_2299_);
                v___x_2361_ = 7usize;
                v___x_2362_ = lean_usize_dec_le(v___x_2361_, v_x_2297_);
                if v___x_2362_ == 0 {
                    v___x_2363_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2353_);
                    v___x_2364_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2365_ = lean_nat_dec_lt(v___x_2363_, v___x_2364_);
                    crate::leanh::lean_dec(v___x_2363_);
                    v___y_2355_ = v___x_2365_;
                    state = 10;
                    continue;
                } else {
                    v___y_2355_ = v___x_2362_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2355_ == 0 {
                    v_ks_2356_ = crate::leanh::lean_ctor_get(v_newNode_2353_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2356_);
                    v_vs_2357_ = crate::leanh::lean_ctor_get(v_newNode_2353_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2357_);
                    crate::leanh::lean_dec_ref(v_newNode_2353_);
                    v___x_2358_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2359_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2);
                    v___x_2360_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___redArg(v_x_2297_, v_ks_2356_, v_vs_2357_, v___x_2358_, v___x_2359_);
                    crate::leanh::lean_dec_ref(v_vs_2357_);
                    crate::leanh::lean_dec_ref(v_ks_2356_);
                    return v___x_2360_;
                } else {
                    return v_newNode_2353_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___redArg(
    mut v_depth_2368_: usize,
    mut v_keys_2369_: *mut crate::leanh::LeanObject,
    mut v_vals_2370_: *mut crate::leanh::LeanObject,
    mut v_i_2371_: *mut crate::leanh::LeanObject,
    mut v_entries_2372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    let mut v_k_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u64 = 0;
    let mut v_h_2378_: usize = 0;
    let mut v___x_2379_: usize = 0;
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: usize = 0;
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: usize = 0;
    let mut v_h_2384_: usize = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2373_ = lean_array_get_size(v_keys_2369_);
                v___x_2374_ = lean_nat_dec_lt(v_i_2371_, v___x_2373_);
                if v___x_2374_ == 0 {
                    crate::leanh::lean_dec(v_i_2371_);
                    return v_entries_2372_;
                } else {
                    v_k_2375_ = lean_array_fget_borrowed(v_keys_2369_, v_i_2371_);
                    v_v_2376_ = lean_array_fget_borrowed(v_vals_2370_, v_i_2371_);
                    v___x_2377_ = l_Lean_Expr_hash(v_k_2375_);
                    v_h_2378_ = lean_uint64_to_usize(v___x_2377_);
                    v___x_2379_ = 5usize;
                    v___x_2380_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2381_ = 1usize;
                    v___x_2382_ = lean_usize_sub(v_depth_2368_, v___x_2381_);
                    v___x_2383_ = lean_usize_mul(v___x_2379_, v___x_2382_);
                    v_h_2384_ = lean_usize_shift_right(v_h_2378_, v___x_2383_);
                    v___x_2385_ = lean_nat_add(v_i_2371_, v___x_2380_);
                    crate::leanh::lean_dec(v_i_2371_);
                    crate::leanh::lean_inc(v_v_2376_);
                    crate::leanh::lean_inc(v_k_2375_);
                    v___x_2386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(v_entries_2372_, v_h_2384_, v_depth_2368_, v_k_2375_, v_v_2376_);
                    v_i_2371_ = v___x_2385_;
                    v_entries_2372_ = v___x_2386_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_depth_2388_: *mut crate::leanh::LeanObject,
    mut v_keys_2389_: *mut crate::leanh::LeanObject,
    mut v_vals_2390_: *mut crate::leanh::LeanObject,
    mut v_i_2391_: *mut crate::leanh::LeanObject,
    mut v_entries_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2393_: usize = 0;
    let mut v_res_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2393_ = crate::leanh::lean_unbox_usize(v_depth_2388_);
    crate::leanh::lean_dec(v_depth_2388_);
    v_res_2394_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___redArg(v_depth_boxed_2393_, v_keys_2389_, v_vals_2390_, v_i_2391_, v_entries_2392_);
    crate::leanh::lean_dec_ref(v_vals_2390_);
    crate::leanh::lean_dec_ref(v_keys_2389_);
    return v_res_2394_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___boxed(
    mut v_x_2395_: *mut crate::leanh::LeanObject,
    mut v_x_2396_: *mut crate::leanh::LeanObject,
    mut v_x_2397_: *mut crate::leanh::LeanObject,
    mut v_x_2398_: *mut crate::leanh::LeanObject,
    mut v_x_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4558__boxed_2400_: usize = 0;
    let mut v_x_4559__boxed_2401_: usize = 0;
    let mut v_res_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4558__boxed_2400_ = crate::leanh::lean_unbox_usize(v_x_2396_);
    crate::leanh::lean_dec(v_x_2396_);
    v_x_4559__boxed_2401_ = crate::leanh::lean_unbox_usize(v_x_2397_);
    crate::leanh::lean_dec(v_x_2397_);
    v_res_2402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(v_x_2395_, v_x_4558__boxed_2400_, v_x_4559__boxed_2401_, v_x_2398_, v_x_2399_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2___redArg(
    mut v_x_2403_: *mut crate::leanh::LeanObject,
    mut v_x_2404_: *mut crate::leanh::LeanObject,
    mut v_x_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2406_: u64 = 0;
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: usize = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_Expr_hash(v_x_2404_);
    v___x_2407_ = lean_uint64_to_usize(v___x_2406_);
    v___x_2408_ = 1usize;
    v___x_2409_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(v_x_2403_, v___x_2407_, v___x_2408_, v_x_2404_, v_x_2405_);
    return v___x_2409_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg(
    mut v_msg_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2424_: u8 = 0;
    let mut v_env_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2429_: u8 = 0;
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut v_unused_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2443_: u8 = 0;
    let mut v_a_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2447_: u8 = 0;
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2416_ = crate::leanh::lean_ctor_get(v___y_2413_, 2);
                v_ref_2417_ = crate::leanh::lean_ctor_get(v___y_2413_, 5);
                v___x_2418_ = lean_st_ref_get(v___y_2414_);
                v___x_2419_ = lean_st_ref_get(v___y_2412_);
                v___x_2420_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2411_);
                if crate::leanh::lean_obj_tag(v___x_2420_) == 0 {
                    v_a_2421_ = crate::leanh::lean_ctor_get(v___x_2420_, 0);
                    v_isSharedCheck_2443_ = (!crate::leanh::lean_is_exclusive(v___x_2420_)) as u8;
                    if v_isSharedCheck_2443_ == 0 {
                        v___x_2423_ = v___x_2420_;
                        v_isShared_2424_ = v_isSharedCheck_2443_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2421_);
                        crate::leanh::lean_dec(v___x_2420_);
                        v___x_2423_ = crate::leanh::lean_box(0);
                        v_isShared_2424_ = v_isSharedCheck_2443_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2419_);
                    crate::leanh::lean_dec(v___x_2418_);
                    crate::leanh::lean_dec_ref(v_msg_2410_);
                    v_a_2444_ = crate::leanh::lean_ctor_get(v___x_2420_, 0);
                    v_isSharedCheck_2451_ = (!crate::leanh::lean_is_exclusive(v___x_2420_)) as u8;
                    if v_isSharedCheck_2451_ == 0 {
                        v___x_2446_ = v___x_2420_;
                        v_isShared_2447_ = v_isSharedCheck_2451_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2444_);
                        crate::leanh::lean_dec(v___x_2420_);
                        v___x_2446_ = crate::leanh::lean_box(0);
                        v_isShared_2447_ = v_isSharedCheck_2451_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_2425_ = crate::leanh::lean_ctor_get(v___x_2418_, 0);
                crate::leanh::lean_inc_ref(v_env_2425_);
                crate::leanh::lean_dec(v___x_2418_);
                v_lctx_2426_ = crate::leanh::lean_ctor_get(v___x_2419_, 0);
                v_isSharedCheck_2441_ = (!crate::leanh::lean_is_exclusive(v___x_2419_)) as u8;
                if v_isSharedCheck_2441_ == 0 {
                    v_unused_2442_ = crate::leanh::lean_ctor_get(v___x_2419_, 1);
                    crate::leanh::lean_dec(v_unused_2442_);
                    v___x_2428_ = v___x_2419_;
                    v_isShared_2429_ = v_isSharedCheck_2441_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_2426_);
                    crate::leanh::lean_dec(v___x_2419_);
                    v___x_2428_ = crate::leanh::lean_box(0);
                    v_isShared_2429_ = v_isSharedCheck_2441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2430_ = (crate::leanh::lean_unbox(v_a_2421_) as u8);
                crate::leanh::lean_dec(v_a_2421_);
                v___x_2431_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2426_, v___x_2430_);
                crate::leanh::lean_dec_ref(v_lctx_2426_);
                v___x_2432_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2);
                crate::leanh::lean_inc_ref(v_options_2416_);
                v___x_2433_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2433_, 0, v_env_2425_);
                crate::leanh::lean_ctor_set(v___x_2433_, 1, v___x_2432_);
                crate::leanh::lean_ctor_set(v___x_2433_, 2, v___x_2431_);
                crate::leanh::lean_ctor_set(v___x_2433_, 3, v_options_2416_);
                if v_isShared_2429_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2428_, 3);
                    crate::leanh::lean_ctor_set(v___x_2428_, 1, v_msg_2410_);
                    crate::leanh::lean_ctor_set(v___x_2428_, 0, v___x_2433_);
                    v___x_2435_ = v___x_2428_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2440_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_msg_2410_);
                    v___x_2435_ = v_reuseFailAlloc_2440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_ref_2417_);
                v___x_2436_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2436_, 0, v_ref_2417_);
                crate::leanh::lean_ctor_set(v___x_2436_, 1, v___x_2435_);
                if v_isShared_2424_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2423_, 1);
                    crate::leanh::lean_ctor_set(v___x_2423_, 0, v___x_2436_);
                    v___x_2438_ = v___x_2423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
                    v___x_2438_ = v_reuseFailAlloc_2439_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2438_;
            }
            5 => {
                if v_isShared_2447_ == 0 {
                    v___x_2449_ = v___x_2446_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
                    v___x_2449_ = v_reuseFailAlloc_2450_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg___boxed(
    mut v_msg_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
    mut v___y_2456_: *mut crate::leanh::LeanObject,
    mut v___y_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2458_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg(v_msg_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
    crate::leanh::lean_dec(v___y_2456_);
    crate::leanh::lean_dec_ref(v___y_2455_);
    crate::leanh::lean_dec(v___y_2454_);
    crate::leanh::lean_dec_ref(v___y_2453_);
    return v_res_2458_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2459_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2459_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1(
    mut v_msg_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
    mut v___y_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v_toFunctor_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___f_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v_toFunctor_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___f_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189__overap_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2527_: u8 = 0;
    let mut v_unused_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_unused_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_unused_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v_unused_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2471_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0);
                v___x_2472_ = l_StateRefT_x27_instMonad___redArg(v___x_2471_);
                v_toApplicative_2473_ = crate::leanh::lean_ctor_get(v___x_2472_, 0);
                v_isSharedCheck_2535_ = (!crate::leanh::lean_is_exclusive(v___x_2472_)) as u8;
                if v_isSharedCheck_2535_ == 0 {
                    v_unused_2536_ = crate::leanh::lean_ctor_get(v___x_2472_, 1);
                    crate::leanh::lean_dec(v_unused_2536_);
                    v___x_2475_ = v___x_2472_;
                    v_isShared_2476_ = v_isSharedCheck_2535_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2473_);
                    crate::leanh::lean_dec(v___x_2472_);
                    v___x_2475_ = crate::leanh::lean_box(0);
                    v_isShared_2476_ = v_isSharedCheck_2535_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2477_ = crate::leanh::lean_ctor_get(v_toApplicative_2473_, 0);
                v_toSeq_2478_ = crate::leanh::lean_ctor_get(v_toApplicative_2473_, 2);
                v_toSeqLeft_2479_ = crate::leanh::lean_ctor_get(v_toApplicative_2473_, 3);
                v_toSeqRight_2480_ = crate::leanh::lean_ctor_get(v_toApplicative_2473_, 4);
                v_isSharedCheck_2533_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2473_)) as u8;
                if v_isSharedCheck_2533_ == 0 {
                    v_unused_2534_ = crate::leanh::lean_ctor_get(v_toApplicative_2473_, 1);
                    crate::leanh::lean_dec(v_unused_2534_);
                    v___x_2482_ = v_toApplicative_2473_;
                    v_isShared_2483_ = v_isSharedCheck_2533_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2480_);
                    crate::leanh::lean_inc(v_toSeqLeft_2479_);
                    crate::leanh::lean_inc(v_toSeq_2478_);
                    crate::leanh::lean_inc(v_toFunctor_2477_);
                    crate::leanh::lean_dec(v_toApplicative_2473_);
                    v___x_2482_ = crate::leanh::lean_box(0);
                    v_isShared_2483_ = v_isSharedCheck_2533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2484_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__1;
                v___f_2485_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2477_);
                v___f_2486_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2486_, 0, v_toFunctor_2477_);
                v___f_2487_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2487_, 0, v_toFunctor_2477_);
                v___x_2488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2488_, 0, v___f_2486_);
                crate::leanh::lean_ctor_set(v___x_2488_, 1, v___f_2487_);
                v___f_2489_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2489_, 0, v_toSeqRight_2480_);
                v___f_2490_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2490_, 0, v_toSeqLeft_2479_);
                v___f_2491_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2491_, 0, v_toSeq_2478_);
                if v_isShared_2483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2482_, 4, v___f_2489_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 3, v___f_2490_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 2, v___f_2491_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 1, v___f_2484_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 0, v___x_2488_);
                    v___x_2493_ = v___x_2482_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___f_2484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 2, v___f_2491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 3, v___f_2490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 4, v___f_2489_);
                    v___x_2493_ = v_reuseFailAlloc_2532_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2476_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2475_, 1, v___f_2485_);
                    crate::leanh::lean_ctor_set(v___x_2475_, 0, v___x_2493_);
                    v___x_2495_ = v___x_2475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___f_2485_);
                    v___x_2495_ = v_reuseFailAlloc_2531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2496_ = l_StateRefT_x27_instMonad___redArg(v___x_2495_);
                v_toApplicative_2497_ = crate::leanh::lean_ctor_get(v___x_2496_, 0);
                v_isSharedCheck_2529_ = (!crate::leanh::lean_is_exclusive(v___x_2496_)) as u8;
                if v_isSharedCheck_2529_ == 0 {
                    v_unused_2530_ = crate::leanh::lean_ctor_get(v___x_2496_, 1);
                    crate::leanh::lean_dec(v_unused_2530_);
                    v___x_2499_ = v___x_2496_;
                    v_isShared_2500_ = v_isSharedCheck_2529_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2497_);
                    crate::leanh::lean_dec(v___x_2496_);
                    v___x_2499_ = crate::leanh::lean_box(0);
                    v_isShared_2500_ = v_isSharedCheck_2529_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2501_ = crate::leanh::lean_ctor_get(v_toApplicative_2497_, 0);
                v_toSeq_2502_ = crate::leanh::lean_ctor_get(v_toApplicative_2497_, 2);
                v_toSeqLeft_2503_ = crate::leanh::lean_ctor_get(v_toApplicative_2497_, 3);
                v_toSeqRight_2504_ = crate::leanh::lean_ctor_get(v_toApplicative_2497_, 4);
                v_isSharedCheck_2527_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2497_)) as u8;
                if v_isSharedCheck_2527_ == 0 {
                    v_unused_2528_ = crate::leanh::lean_ctor_get(v_toApplicative_2497_, 1);
                    crate::leanh::lean_dec(v_unused_2528_);
                    v___x_2506_ = v_toApplicative_2497_;
                    v_isShared_2507_ = v_isSharedCheck_2527_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2504_);
                    crate::leanh::lean_inc(v_toSeqLeft_2503_);
                    crate::leanh::lean_inc(v_toSeq_2502_);
                    crate::leanh::lean_inc(v_toFunctor_2501_);
                    crate::leanh::lean_dec(v_toApplicative_2497_);
                    v___x_2506_ = crate::leanh::lean_box(0);
                    v_isShared_2507_ = v_isSharedCheck_2527_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2508_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__3;
                v___f_2509_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_2501_);
                v___f_2510_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2510_, 0, v_toFunctor_2501_);
                v___f_2511_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2511_, 0, v_toFunctor_2501_);
                v___x_2512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2512_, 0, v___f_2510_);
                crate::leanh::lean_ctor_set(v___x_2512_, 1, v___f_2511_);
                v___f_2513_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2513_, 0, v_toSeqRight_2504_);
                v___f_2514_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2514_, 0, v_toSeqLeft_2503_);
                v___f_2515_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2515_, 0, v_toSeq_2502_);
                if v_isShared_2507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2506_, 4, v___f_2513_);
                    crate::leanh::lean_ctor_set(v___x_2506_, 3, v___f_2514_);
                    crate::leanh::lean_ctor_set(v___x_2506_, 2, v___f_2515_);
                    crate::leanh::lean_ctor_set(v___x_2506_, 1, v___f_2508_);
                    crate::leanh::lean_ctor_set(v___x_2506_, 0, v___x_2512_);
                    v___x_2517_ = v___x_2506_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2526_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 1, v___f_2508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 2, v___f_2515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 3, v___f_2514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 4, v___f_2513_);
                    v___x_2517_ = v_reuseFailAlloc_2526_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2499_, 1, v___f_2509_);
                    crate::leanh::lean_ctor_set(v___x_2499_, 0, v___x_2517_);
                    v___x_2519_ = v___x_2499_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___f_2509_);
                    v___x_2519_ = v_reuseFailAlloc_2525_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2520_ = l_ReaderT_instMonad___redArg(v___x_2519_);
                v___x_2521_ = crate::leanh::lean_box(0);
                v___x_2522_ = l_instInhabitedOfMonad___redArg(v___x_2520_, v___x_2521_);
                v___x_4189__overap_2523_ = lean_panic_fn_borrowed(v___x_2522_, v_msg_2464_);
                crate::leanh::lean_dec(v___x_2522_);
                crate::leanh::lean_inc(v___y_2469_);
                crate::leanh::lean_inc_ref(v___y_2468_);
                crate::leanh::lean_inc(v___y_2467_);
                crate::leanh::lean_inc_ref(v___y_2466_);
                crate::leanh::lean_inc_ref(v___y_2465_);
                v___x_2524_ = crate::leanh::lean_apply_6(
                    v___x_4189__overap_2523_,
                    v___y_2465_,
                    v___y_2466_,
                    v___y_2467_,
                    v___y_2468_,
                    v___y_2469_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___boxed(
    mut v_msg_2537_: *mut crate::leanh::LeanObject,
    mut v___y_2538_: *mut crate::leanh::LeanObject,
    mut v___y_2539_: *mut crate::leanh::LeanObject,
    mut v___y_2540_: *mut crate::leanh::LeanObject,
    mut v___y_2541_: *mut crate::leanh::LeanObject,
    mut v___y_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1(v_msg_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
    crate::leanh::lean_dec(v___y_2542_);
    crate::leanh::lean_dec_ref(v___y_2541_);
    crate::leanh::lean_dec(v___y_2540_);
    crate::leanh::lean_dec_ref(v___y_2539_);
    crate::leanh::lean_dec_ref(v___y_2538_);
    return v_res_2544_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__0;
    v___x_2547_ = l_Lean_stringToMessageData(v___x_2546_);
    return v___x_2547_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2551_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__4;
    v___x_2552_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2553_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_2554_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__3;
    v___x_2555_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__2;
    v___x_2556_ = l_mkPanicMessageWithDecl(
        v___x_2555_,
        v___x_2554_,
        v___x_2553_,
        v___x_2552_,
        v___x_2551_,
    );
    return v___x_2556_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(
    mut v_constName_2557_: *mut crate::leanh::LeanObject,
    mut v___y_2558_: *mut crate::leanh::LeanObject,
    mut v___y_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: u8 = 0;
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2577_: u8 = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2582_: u8 = 0;
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2592_: u8 = 0;
    let mut v_val_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2597_: u8 = 0;
    let mut v_a_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2572_ = lean_st_ref_get(v___y_2562_);
                v_env_2573_ = crate::leanh::lean_ctor_get(v___x_2572_, 0);
                crate::leanh::lean_inc_ref(v_env_2573_);
                crate::leanh::lean_dec(v___x_2572_);
                v___x_2574_ = 0;
                crate::leanh::lean_inc(v_constName_2557_);
                v___x_2575_ =
                    l_Lean_Environment_findAsync_x3f(v_env_2573_, v_constName_2557_, v___x_2574_);
                if crate::leanh::lean_obj_tag(v___x_2575_) == 1 {
                    v_val_2576_ = crate::leanh::lean_ctor_get(v___x_2575_, 0);
                    crate::leanh::lean_inc(v_val_2576_);
                    crate::leanh::lean_dec_ref_known(v___x_2575_, 1);
                    v_kind_2577_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2576_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_2577_ == 6 {
                        v___x_2578_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2576_);
                        if crate::leanh::lean_obj_tag(v___x_2578_) == 6 {
                            crate::leanh::lean_dec(v_constName_2557_);
                            v_val_2579_ = crate::leanh::lean_ctor_get(v___x_2578_, 0);
                            v_isSharedCheck_2586_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2578_)) as u8;
                            if v_isSharedCheck_2586_ == 0 {
                                v___x_2581_ = v___x_2578_;
                                v_isShared_2582_ = v_isSharedCheck_2586_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2579_);
                                crate::leanh::lean_dec(v___x_2578_);
                                v___x_2581_ = crate::leanh::lean_box(0);
                                v_isShared_2582_ = v_isSharedCheck_2586_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2578_);
                            v___x_2587_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5);
                            v___x_2588_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1(v___x_2587_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
                            if crate::leanh::lean_obj_tag(v___x_2588_) == 0 {
                                v_a_2589_ = crate::leanh::lean_ctor_get(v___x_2588_, 0);
                                v_isSharedCheck_2597_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2588_)) as u8;
                                if v_isSharedCheck_2597_ == 0 {
                                    v___x_2591_ = v___x_2588_;
                                    v_isShared_2592_ = v_isSharedCheck_2597_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2589_);
                                    crate::leanh::lean_dec(v___x_2588_);
                                    v___x_2591_ = crate::leanh::lean_box(0);
                                    v_isShared_2592_ = v_isSharedCheck_2597_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_2557_);
                                v_a_2598_ = crate::leanh::lean_ctor_get(v___x_2588_, 0);
                                v_isSharedCheck_2605_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2588_)) as u8;
                                if v_isSharedCheck_2605_ == 0 {
                                    v___x_2600_ = v___x_2588_;
                                    v_isShared_2601_ = v_isSharedCheck_2605_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2598_);
                                    crate::leanh::lean_dec(v___x_2588_);
                                    v___x_2600_ = crate::leanh::lean_box(0);
                                    v_isShared_2601_ = v_isSharedCheck_2605_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2576_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2575_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2565_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
                v___x_2566_ = 0;
                v___x_2567_ = l_Lean_MessageData_ofConstName(v_constName_2557_, v___x_2566_);
                v___x_2568_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2565_);
                crate::leanh::lean_ctor_set(v___x_2568_, 1, v___x_2567_);
                v___x_2569_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1);
                v___x_2570_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2570_, 0, v___x_2568_);
                crate::leanh::lean_ctor_set(v___x_2570_, 1, v___x_2569_);
                v___x_2571_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg(v___x_2570_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
                return v___x_2571_;
            }
            2 => {
                if v_isShared_2582_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2581_, 0);
                    v___x_2584_ = v___x_2581_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_val_2579_);
                    v___x_2584_ = v_reuseFailAlloc_2585_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2584_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2589_) == 0 {
                    crate::leanh::lean_del_object(v___x_2591_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_2557_);
                    v_val_2593_ = crate::leanh::lean_ctor_get(v_a_2589_, 0);
                    crate::leanh::lean_inc(v_val_2593_);
                    crate::leanh::lean_dec_ref_known(v_a_2589_, 1);
                    if v_isShared_2592_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2591_, 0, v_val_2593_);
                        v___x_2595_ = v___x_2591_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_val_2593_);
                        v___x_2595_ = v_reuseFailAlloc_2596_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2595_;
            }
            6 => {
                if v_isShared_2601_ == 0 {
                    v___x_2603_ = v___x_2600_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___boxed(
    mut v_constName_2606_: *mut crate::leanh::LeanObject,
    mut v___y_2607_: *mut crate::leanh::LeanObject,
    mut v___y_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
    mut v___y_2611_: *mut crate::leanh::LeanObject,
    mut v___y_2612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2613_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(v_constName_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
    crate::leanh::lean_dec(v___y_2611_);
    crate::leanh::lean_dec_ref(v___y_2610_);
    crate::leanh::lean_dec(v___y_2609_);
    crate::leanh::lean_dec_ref(v___y_2608_);
    crate::leanh::lean_dec_ref(v___y_2607_);
    return v_res_2613_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1(
    mut v_sz_2614_: usize,
    mut v_i_2615_: usize,
    mut v_bs_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2617_: u8 = 0;
    let mut v_v_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: usize = 0;
    let mut v___x_2624_: usize = 0;
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2617_ = lean_usize_dec_lt(v_i_2615_, v_sz_2614_);
                if v___x_2617_ == 0 {
                    return v_bs_2616_;
                } else {
                    v_v_2618_ = lean_array_uget_borrowed(v_bs_2616_, v_i_2615_);
                    v_fvarId_2619_ = crate::leanh::lean_ctor_get(v_v_2618_, 0);
                    crate::leanh::lean_inc(v_fvarId_2619_);
                    v___x_2620_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2621_ = lean_array_uset(v_bs_2616_, v_i_2615_, v___x_2620_);
                    v___x_2622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2622_, 0, v_fvarId_2619_);
                    v___x_2623_ = 1usize;
                    v___x_2624_ = lean_usize_add(v_i_2615_, v___x_2623_);
                    v___x_2625_ = lean_array_uset(v_bs_x27_2621_, v_i_2615_, v___x_2622_);
                    v_i_2615_ = v___x_2624_;
                    v_bs_2616_ = v___x_2625_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1___boxed(
    mut v_sz_2627_: *mut crate::leanh::LeanObject,
    mut v_i_2628_: *mut crate::leanh::LeanObject,
    mut v_bs_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2630_: usize = 0;
    let mut v_i_boxed_2631_: usize = 0;
    let mut v_res_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2630_ = crate::leanh::lean_unbox_usize(v_sz_2627_);
    crate::leanh::lean_dec(v_sz_2627_);
    v_i_boxed_2631_ = crate::leanh::lean_unbox_usize(v_i_2628_);
    crate::leanh::lean_dec(v_i_2628_);
    v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1(v_sz_boxed_2630_, v_i_boxed_2631_, v_bs_2629_);
    return v_res_2632_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(
    mut v_discr_2633_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2634_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v_a_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v_sz_2654_: usize = 0;
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v_name_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v_discrCtorMap_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorDiscrMap_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_unused_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2687_: u8 = 0;
    let mut v_discrCtorMap_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorDiscrMap_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2699_: u8 = 0;
    let mut v_a_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2703_: u8 = 0;
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_a_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v_a_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2642_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(v_ctorName_2634_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
                if crate::leanh::lean_obj_tag(v___x_2642_) == 0 {
                    v_a_2643_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                    crate::leanh::lean_inc(v_a_2643_);
                    crate::leanh::lean_dec_ref_known(v___x_2642_, 1);
                    crate::leanh::lean_inc(v_discr_2633_);
                    v___x_2644_ = l_Lean_Compiler_LCNF_getType(
                        v_discr_2633_,
                        v_a_2637_,
                        v_a_2638_,
                        v_a_2639_,
                        v_a_2640_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2644_) == 0 {
                        v_a_2645_ = crate::leanh::lean_ctor_get(v___x_2644_, 0);
                        crate::leanh::lean_inc(v_a_2645_);
                        crate::leanh::lean_dec_ref_known(v___x_2644_, 1);
                        v_toConstantVal_2646_ = crate::leanh::lean_ctor_get(v_a_2643_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_2646_);
                        v_induct_2647_ = crate::leanh::lean_ctor_get(v_a_2643_, 1);
                        v_numParams_2648_ = crate::leanh::lean_ctor_get(v_a_2643_, 3);
                        v___x_2649_ = l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(
                            v_a_2645_,
                            v_induct_2647_,
                            v_a_2639_,
                            v_a_2640_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2649_) == 0 {
                            v_a_2650_ = crate::leanh::lean_ctor_get(v___x_2649_, 0);
                            v_isSharedCheck_2699_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2649_)) as u8;
                            if v_isSharedCheck_2699_ == 0 {
                                v___x_2652_ = v___x_2649_;
                                v_isShared_2653_ = v_isSharedCheck_2699_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2650_);
                                crate::leanh::lean_dec(v___x_2649_);
                                v___x_2652_ = crate::leanh::lean_box(0);
                                v_isShared_2653_ = v_isSharedCheck_2699_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_toConstantVal_2646_);
                            crate::leanh::lean_dec(v_a_2643_);
                            crate::leanh::lean_dec_ref(v_ctorFields_2635_);
                            crate::leanh::lean_dec(v_discr_2633_);
                            v_a_2700_ = crate::leanh::lean_ctor_get(v___x_2649_, 0);
                            v_isSharedCheck_2707_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2649_)) as u8;
                            if v_isSharedCheck_2707_ == 0 {
                                v___x_2702_ = v___x_2649_;
                                v_isShared_2703_ = v_isSharedCheck_2707_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2700_);
                                crate::leanh::lean_dec(v___x_2649_);
                                v___x_2702_ = crate::leanh::lean_box(0);
                                v_isShared_2703_ = v_isSharedCheck_2707_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2643_);
                        crate::leanh::lean_dec_ref(v_ctorFields_2635_);
                        crate::leanh::lean_dec(v_discr_2633_);
                        v_a_2708_ = crate::leanh::lean_ctor_get(v___x_2644_, 0);
                        v_isSharedCheck_2715_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2644_)) as u8;
                        if v_isSharedCheck_2715_ == 0 {
                            v___x_2710_ = v___x_2644_;
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2708_);
                            crate::leanh::lean_dec(v___x_2644_);
                            v___x_2710_ = crate::leanh::lean_box(0);
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctorFields_2635_);
                    crate::leanh::lean_dec(v_discr_2633_);
                    v_a_2716_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                    v_isSharedCheck_2723_ = (!crate::leanh::lean_is_exclusive(v___x_2642_)) as u8;
                    if v_isSharedCheck_2723_ == 0 {
                        v___x_2718_ = v___x_2642_;
                        v_isShared_2719_ = v_isSharedCheck_2723_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2716_);
                        crate::leanh::lean_dec(v___x_2642_);
                        v___x_2718_ = crate::leanh::lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2723_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_2654_ = lean_array_size(v_ctorFields_2635_);
                v___x_2655_ = 0usize;
                v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1(v_sz_2654_, v___x_2655_, v_ctorFields_2635_);
                if crate::leanh::lean_obj_tag(v_a_2650_) == 1 {
                    v_val_2657_ = crate::leanh::lean_ctor_get(v_a_2650_, 0);
                    crate::leanh::lean_inc(v_val_2657_);
                    crate::leanh::lean_dec_ref_known(v_a_2650_, 1);
                    v_fst_2658_ = crate::leanh::lean_ctor_get(v_val_2657_, 0);
                    v_snd_2659_ = crate::leanh::lean_ctor_get(v_val_2657_, 1);
                    v_isSharedCheck_2687_ = (!crate::leanh::lean_is_exclusive(v_val_2657_)) as u8;
                    if v_isSharedCheck_2687_ == 0 {
                        v___x_2661_ = v_val_2657_;
                        v_isShared_2662_ = v_isSharedCheck_2687_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2659_);
                        crate::leanh::lean_inc(v_fst_2658_);
                        crate::leanh::lean_dec(v_val_2657_);
                        v___x_2661_ = crate::leanh::lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2687_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2650_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_2646_);
                    v_discrCtorMap_2688_ = crate::leanh::lean_ctor_get(v_a_2636_, 0);
                    v_ctorDiscrMap_2689_ = crate::leanh::lean_ctor_get(v_a_2636_, 1);
                    v___x_2690_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_numParams_2648_);
                    v___x_2691_ = lean_mk_array(v_numParams_2648_, v___x_2690_);
                    v___x_2692_ = l_Array_append___redArg(v___x_2691_, v___x_2656_);
                    crate::leanh::lean_dec_ref(v___x_2656_);
                    v___x_2693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2693_, 0, v_a_2643_);
                    crate::leanh::lean_ctor_set(v___x_2693_, 1, v___x_2692_);
                    crate::leanh::lean_inc(v_discrCtorMap_2688_);
                    v___x_2694_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_2633_, v___x_2693_, v_discrCtorMap_2688_);
                    crate::leanh::lean_inc_ref(v_ctorDiscrMap_2689_);
                    v___x_2695_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2695_, 0, v___x_2694_);
                    crate::leanh::lean_ctor_set(v___x_2695_, 1, v_ctorDiscrMap_2689_);
                    if v_isShared_2653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2652_, 0, v___x_2695_);
                        v___x_2697_ = v___x_2652_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2698_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
                        v___x_2697_ = v_reuseFailAlloc_2698_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_name_2663_ = crate::leanh::lean_ctor_get(v_toConstantVal_2646_, 0);
                v_isSharedCheck_2684_ =
                    (!crate::leanh::lean_is_exclusive(v_toConstantVal_2646_)) as u8;
                if v_isSharedCheck_2684_ == 0 {
                    v_unused_2685_ = crate::leanh::lean_ctor_get(v_toConstantVal_2646_, 2);
                    crate::leanh::lean_dec(v_unused_2685_);
                    v_unused_2686_ = crate::leanh::lean_ctor_get(v_toConstantVal_2646_, 1);
                    crate::leanh::lean_dec(v_unused_2686_);
                    v___x_2665_ = v_toConstantVal_2646_;
                    v_isShared_2666_ = v_isSharedCheck_2684_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2663_);
                    crate::leanh::lean_dec(v_toConstantVal_2646_);
                    v___x_2665_ = crate::leanh::lean_box(0);
                    v_isShared_2666_ = v_isSharedCheck_2684_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_discrCtorMap_2667_ = crate::leanh::lean_ctor_get(v_a_2636_, 0);
                v_ctorDiscrMap_2668_ = crate::leanh::lean_ctor_get(v_a_2636_, 1);
                v___x_2669_ = l_Array_append___redArg(v_snd_2659_, v___x_2656_);
                crate::leanh::lean_dec_ref(v___x_2656_);
                crate::leanh::lean_inc_ref(v___x_2669_);
                if v_isShared_2662_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2661_, 1, v___x_2669_);
                    crate::leanh::lean_ctor_set(v___x_2661_, 0, v_a_2643_);
                    v___x_2671_ = v___x_2661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2683_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2669_);
                    v___x_2671_ = v_reuseFailAlloc_2683_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2672_ = 0;
                if v_isShared_2666_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2665_, 3);
                    crate::leanh::lean_ctor_set(v___x_2665_, 2, v___x_2669_);
                    crate::leanh::lean_ctor_set(v___x_2665_, 1, v_fst_2658_);
                    v___x_2674_ = v___x_2665_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_name_2663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_fst_2658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 2, v___x_2669_);
                    v___x_2674_ = v_reuseFailAlloc_2682_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_discrCtorMap_2667_);
                crate::leanh::lean_inc(v_discr_2633_);
                v___x_2675_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_2633_, v___x_2671_, v_discrCtorMap_2667_);
                v___x_2676_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_2672_, v___x_2674_);
                crate::leanh::lean_inc_ref(v_ctorDiscrMap_2668_);
                v___x_2677_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2___redArg(v_ctorDiscrMap_2668_, v___x_2676_, v_discr_2633_);
                v___x_2678_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2678_, 0, v___x_2675_);
                crate::leanh::lean_ctor_set(v___x_2678_, 1, v___x_2677_);
                if v_isShared_2653_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2652_, 0, v___x_2678_);
                    v___x_2680_ = v___x_2652_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2681_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
                    v___x_2680_ = v_reuseFailAlloc_2681_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2680_;
            }
            7 => {
                return v___x_2697_;
            }
            8 => {
                if v_isShared_2703_ == 0 {
                    v___x_2705_ = v___x_2702_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
                    v___x_2705_ = v_reuseFailAlloc_2706_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2705_;
            }
            10 => {
                if v_isShared_2711_ == 0 {
                    v___x_2713_ = v___x_2710_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
                    v___x_2713_ = v_reuseFailAlloc_2714_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2713_;
            }
            12 => {
                if v_isShared_2719_ == 0 {
                    v___x_2721_ = v___x_2718_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
                    v___x_2721_ = v_reuseFailAlloc_2722_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___boxed(
    mut v_discr_2724_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2725_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v_a_2732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2733_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2724_, v_ctorName_2725_, v_ctorFields_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
    crate::leanh::lean_dec(v_a_2731_);
    crate::leanh::lean_dec_ref(v_a_2730_);
    crate::leanh::lean_dec(v_a_2729_);
    crate::leanh::lean_dec_ref(v_a_2728_);
    crate::leanh::lean_dec_ref(v_a_2727_);
    return v_res_2733_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0(
    mut v_00_u03b1_2734_: *mut crate::leanh::LeanObject,
    mut v_msg_2735_: *mut crate::leanh::LeanObject,
    mut v___y_2736_: *mut crate::leanh::LeanObject,
    mut v___y_2737_: *mut crate::leanh::LeanObject,
    mut v___y_2738_: *mut crate::leanh::LeanObject,
    mut v___y_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg(v_msg_2735_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
    return v___x_2742_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___boxed(
    mut v_00_u03b1_2743_: *mut crate::leanh::LeanObject,
    mut v_msg_2744_: *mut crate::leanh::LeanObject,
    mut v___y_2745_: *mut crate::leanh::LeanObject,
    mut v___y_2746_: *mut crate::leanh::LeanObject,
    mut v___y_2747_: *mut crate::leanh::LeanObject,
    mut v___y_2748_: *mut crate::leanh::LeanObject,
    mut v___y_2749_: *mut crate::leanh::LeanObject,
    mut v___y_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2751_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0(v_00_u03b1_2743_, v_msg_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
    crate::leanh::lean_dec(v___y_2749_);
    crate::leanh::lean_dec_ref(v___y_2748_);
    crate::leanh::lean_dec(v___y_2747_);
    crate::leanh::lean_dec_ref(v___y_2746_);
    crate::leanh::lean_dec_ref(v___y_2745_);
    return v_res_2751_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2(
    mut v_00_u03b2_2752_: *mut crate::leanh::LeanObject,
    mut v_x_2753_: *mut crate::leanh::LeanObject,
    mut v_x_2754_: *mut crate::leanh::LeanObject,
    mut v_x_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2___redArg(v_x_2753_, v_x_2754_, v_x_2755_);
    return v___x_2756_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4(
    mut v_00_u03b2_2757_: *mut crate::leanh::LeanObject,
    mut v_x_2758_: *mut crate::leanh::LeanObject,
    mut v_x_2759_: usize,
    mut v_x_2760_: usize,
    mut v_x_2761_: *mut crate::leanh::LeanObject,
    mut v_x_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(v_x_2758_, v_x_2759_, v_x_2760_, v_x_2761_, v_x_2762_);
    return v___x_2763_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___boxed(
    mut v_00_u03b2_2764_: *mut crate::leanh::LeanObject,
    mut v_x_2765_: *mut crate::leanh::LeanObject,
    mut v_x_2766_: *mut crate::leanh::LeanObject,
    mut v_x_2767_: *mut crate::leanh::LeanObject,
    mut v_x_2768_: *mut crate::leanh::LeanObject,
    mut v_x_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5303__boxed_2770_: usize = 0;
    let mut v_x_5304__boxed_2771_: usize = 0;
    let mut v_res_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5303__boxed_2770_ = crate::leanh::lean_unbox_usize(v_x_2766_);
    crate::leanh::lean_dec(v_x_2766_);
    v_x_5304__boxed_2771_ = crate::leanh::lean_unbox_usize(v_x_2767_);
    crate::leanh::lean_dec(v_x_2767_);
    v_res_2772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4(v_00_u03b2_2764_, v_x_2765_, v_x_5303__boxed_2770_, v_x_5304__boxed_2771_, v_x_2768_, v_x_2769_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2773_: *mut crate::leanh::LeanObject,
    mut v_n_2774_: *mut crate::leanh::LeanObject,
    mut v_k_2775_: *mut crate::leanh::LeanObject,
    mut v_v_2776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2777_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5___redArg(v_n_2774_, v_k_2775_, v_v_2776_);
    return v___x_2777_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6(
    mut v_00_u03b2_2778_: *mut crate::leanh::LeanObject,
    mut v_depth_2779_: usize,
    mut v_keys_2780_: *mut crate::leanh::LeanObject,
    mut v_vals_2781_: *mut crate::leanh::LeanObject,
    mut v_heq_2782_: *mut crate::leanh::LeanObject,
    mut v_i_2783_: *mut crate::leanh::LeanObject,
    mut v_entries_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2785_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___redArg(v_depth_2779_, v_keys_2780_, v_vals_2781_, v_i_2783_, v_entries_2784_);
    return v___x_2785_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b2_2786_: *mut crate::leanh::LeanObject,
    mut v_depth_2787_: *mut crate::leanh::LeanObject,
    mut v_keys_2788_: *mut crate::leanh::LeanObject,
    mut v_vals_2789_: *mut crate::leanh::LeanObject,
    mut v_heq_2790_: *mut crate::leanh::LeanObject,
    mut v_i_2791_: *mut crate::leanh::LeanObject,
    mut v_entries_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2793_: usize = 0;
    let mut v_res_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2793_ = crate::leanh::lean_unbox_usize(v_depth_2787_);
    crate::leanh::lean_dec(v_depth_2787_);
    v_res_2794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6(v_00_u03b2_2786_, v_depth_boxed_2793_, v_keys_2788_, v_vals_2789_, v_heq_2790_, v_i_2791_, v_entries_2792_);
    crate::leanh::lean_dec_ref(v_vals_2789_);
    crate::leanh::lean_dec_ref(v_keys_2788_);
    return v_res_2794_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_2795_: *mut crate::leanh::LeanObject,
    mut v_x_2796_: *mut crate::leanh::LeanObject,
    mut v_x_2797_: *mut crate::leanh::LeanObject,
    mut v_x_2798_: *mut crate::leanh::LeanObject,
    mut v_x_2799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5_spec__6___redArg(v_x_2796_, v_x_2797_, v_x_2798_, v_x_2799_);
    return v___x_2800_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg(
    mut v_discr_2801_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2802_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2803_: *mut crate::leanh::LeanObject,
    mut v_x_2804_: *mut crate::leanh::LeanObject,
    mut v_a_2805_: *mut crate::leanh::LeanObject,
    mut v_a_2806_: *mut crate::leanh::LeanObject,
    mut v_a_2807_: *mut crate::leanh::LeanObject,
    mut v_a_2808_: *mut crate::leanh::LeanObject,
    mut v_a_2809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2817_: u8 = 0;
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2811_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2801_, v_ctorName_2802_, v_ctorFields_2803_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
                if crate::leanh::lean_obj_tag(v___x_2811_) == 0 {
                    v_a_2812_ = crate::leanh::lean_ctor_get(v___x_2811_, 0);
                    crate::leanh::lean_inc(v_a_2812_);
                    crate::leanh::lean_dec_ref_known(v___x_2811_, 1);
                    crate::leanh::lean_inc(v_a_2809_);
                    crate::leanh::lean_inc_ref(v_a_2808_);
                    crate::leanh::lean_inc(v_a_2807_);
                    crate::leanh::lean_inc_ref(v_a_2806_);
                    v___x_2813_ = crate::leanh::lean_apply_6(
                        v_x_2804_,
                        v_a_2812_,
                        v_a_2806_,
                        v_a_2807_,
                        v_a_2808_,
                        v_a_2809_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2813_;
                } else {
                    crate::leanh::lean_dec_ref(v_x_2804_);
                    v_a_2814_ = crate::leanh::lean_ctor_get(v___x_2811_, 0);
                    v_isSharedCheck_2821_ = (!crate::leanh::lean_is_exclusive(v___x_2811_)) as u8;
                    if v_isSharedCheck_2821_ == 0 {
                        v___x_2816_ = v___x_2811_;
                        v_isShared_2817_ = v_isSharedCheck_2821_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2814_);
                        crate::leanh::lean_dec(v___x_2811_);
                        v___x_2816_ = crate::leanh::lean_box(0);
                        v_isShared_2817_ = v_isSharedCheck_2821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2817_ == 0 {
                    v___x_2819_ = v___x_2816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2820_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
                    v___x_2819_ = v_reuseFailAlloc_2820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg___boxed(
    mut v_discr_2822_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2823_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2824_: *mut crate::leanh::LeanObject,
    mut v_x_2825_: *mut crate::leanh::LeanObject,
    mut v_a_2826_: *mut crate::leanh::LeanObject,
    mut v_a_2827_: *mut crate::leanh::LeanObject,
    mut v_a_2828_: *mut crate::leanh::LeanObject,
    mut v_a_2829_: *mut crate::leanh::LeanObject,
    mut v_a_2830_: *mut crate::leanh::LeanObject,
    mut v_a_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2832_ = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg(
        v_discr_2822_,
        v_ctorName_2823_,
        v_ctorFields_2824_,
        v_x_2825_,
        v_a_2826_,
        v_a_2827_,
        v_a_2828_,
        v_a_2829_,
        v_a_2830_,
    );
    crate::leanh::lean_dec(v_a_2830_);
    crate::leanh::lean_dec_ref(v_a_2829_);
    crate::leanh::lean_dec(v_a_2828_);
    crate::leanh::lean_dec_ref(v_a_2827_);
    crate::leanh::lean_dec_ref(v_a_2826_);
    return v_res_2832_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp(
    mut v_00_u03b1_2833_: *mut crate::leanh::LeanObject,
    mut v_discr_2834_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2835_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2836_: *mut crate::leanh::LeanObject,
    mut v_x_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
    mut v_a_2839_: *mut crate::leanh::LeanObject,
    mut v_a_2840_: *mut crate::leanh::LeanObject,
    mut v_a_2841_: *mut crate::leanh::LeanObject,
    mut v_a_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2850_: u8 = 0;
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2854_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2844_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2834_, v_ctorName_2835_, v_ctorFields_2836_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
                if crate::leanh::lean_obj_tag(v___x_2844_) == 0 {
                    v_a_2845_ = crate::leanh::lean_ctor_get(v___x_2844_, 0);
                    crate::leanh::lean_inc(v_a_2845_);
                    crate::leanh::lean_dec_ref_known(v___x_2844_, 1);
                    crate::leanh::lean_inc(v_a_2842_);
                    crate::leanh::lean_inc_ref(v_a_2841_);
                    crate::leanh::lean_inc(v_a_2840_);
                    crate::leanh::lean_inc_ref(v_a_2839_);
                    v___x_2846_ = crate::leanh::lean_apply_6(
                        v_x_2837_,
                        v_a_2845_,
                        v_a_2839_,
                        v_a_2840_,
                        v_a_2841_,
                        v_a_2842_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2846_;
                } else {
                    crate::leanh::lean_dec_ref(v_x_2837_);
                    v_a_2847_ = crate::leanh::lean_ctor_get(v___x_2844_, 0);
                    v_isSharedCheck_2854_ = (!crate::leanh::lean_is_exclusive(v___x_2844_)) as u8;
                    if v_isSharedCheck_2854_ == 0 {
                        v___x_2849_ = v___x_2844_;
                        v_isShared_2850_ = v_isSharedCheck_2854_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2847_);
                        crate::leanh::lean_dec(v___x_2844_);
                        v___x_2849_ = crate::leanh::lean_box(0);
                        v_isShared_2850_ = v_isSharedCheck_2854_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2850_ == 0 {
                    v___x_2852_ = v___x_2849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
                    v___x_2852_ = v_reuseFailAlloc_2853_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___boxed(
    mut v_00_u03b1_2855_: *mut crate::leanh::LeanObject,
    mut v_discr_2856_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2857_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2858_: *mut crate::leanh::LeanObject,
    mut v_x_2859_: *mut crate::leanh::LeanObject,
    mut v_a_2860_: *mut crate::leanh::LeanObject,
    mut v_a_2861_: *mut crate::leanh::LeanObject,
    mut v_a_2862_: *mut crate::leanh::LeanObject,
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2866_ = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp(
        v_00_u03b1_2855_,
        v_discr_2856_,
        v_ctorName_2857_,
        v_ctorFields_2858_,
        v_x_2859_,
        v_a_2860_,
        v_a_2861_,
        v_a_2862_,
        v_a_2863_,
        v_a_2864_,
    );
    crate::leanh::lean_dec(v_a_2864_);
    crate::leanh::lean_dec_ref(v_a_2863_);
    crate::leanh::lean_dec(v_a_2862_);
    crate::leanh::lean_dec_ref(v_a_2861_);
    crate::leanh::lean_dec_ref(v_a_2860_);
    return v_res_2866_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0(
    mut v_discr_2867_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2868_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2869_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2870_: *mut crate::leanh::LeanObject,
    mut v___y_2871_: *mut crate::leanh::LeanObject,
    mut v___y_2872_: *mut crate::leanh::LeanObject,
    mut v___y_2873_: *mut crate::leanh::LeanObject,
    mut v___y_2874_: *mut crate::leanh::LeanObject,
    mut v___y_2875_: *mut crate::leanh::LeanObject,
    mut v___y_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2878_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2867_, v_ctorName_2868_, v_ctorFields_2869_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
                if crate::leanh::lean_obj_tag(v___x_2878_) == 0 {
                    v_a_2879_ = crate::leanh::lean_ctor_get(v___x_2878_, 0);
                    crate::leanh::lean_inc(v_a_2879_);
                    crate::leanh::lean_dec_ref_known(v___x_2878_, 1);
                    crate::leanh::lean_inc(v___y_2876_);
                    crate::leanh::lean_inc_ref(v___y_2875_);
                    crate::leanh::lean_inc(v___y_2874_);
                    crate::leanh::lean_inc_ref(v___y_2873_);
                    v___x_2880_ = crate::leanh::lean_apply_6(
                        v___y_2871_,
                        v_a_2879_,
                        v___y_2873_,
                        v___y_2874_,
                        v___y_2875_,
                        v___y_2876_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2880_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2871_);
                    v_a_2881_ = crate::leanh::lean_ctor_get(v___x_2878_, 0);
                    v_isSharedCheck_2888_ = (!crate::leanh::lean_is_exclusive(v___x_2878_)) as u8;
                    if v_isSharedCheck_2888_ == 0 {
                        v___x_2883_ = v___x_2878_;
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2881_);
                        crate::leanh::lean_dec(v___x_2878_);
                        v___x_2883_ = crate::leanh::lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2884_ == 0 {
                    v___x_2886_ = v___x_2883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
                    v___x_2886_ = v_reuseFailAlloc_2887_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed(
    mut v_discr_2889_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2890_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2891_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2900_ = l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0(
        v_discr_2889_,
        v_ctorName_2890_,
        v_ctorFields_2891_,
        v_00_u03b2_2892_,
        v___y_2893_,
        v___y_2894_,
        v___y_2895_,
        v___y_2896_,
        v___y_2897_,
        v___y_2898_,
    );
    crate::leanh::lean_dec(v___y_2898_);
    crate::leanh::lean_dec_ref(v___y_2897_);
    crate::leanh::lean_dec(v___y_2896_);
    crate::leanh::lean_dec_ref(v___y_2895_);
    crate::leanh::lean_dec_ref(v___y_2894_);
    return v_res_2900_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg(
    mut v_inst_2901_: *mut crate::leanh::LeanObject,
    mut v_discr_2902_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2903_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2904_: *mut crate::leanh::LeanObject,
    mut v_a_2905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2906_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2906_, 0, v_discr_2902_);
    crate::leanh::lean_closure_set(v___f_2906_, 1, v_ctorName_2903_);
    crate::leanh::lean_closure_set(v___f_2906_, 2, v_ctorFields_2904_);
    v___x_2907_ = crate::leanh::lean_apply_3(
        v_inst_2901_,
        crate::leanh::lean_box(0),
        v___f_2906_,
        v_a_2905_,
    );
    return v___x_2907_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtor(
    mut v_m_2908_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2909_: *mut crate::leanh::LeanObject,
    mut v_inst_2910_: *mut crate::leanh::LeanObject,
    mut v_discr_2911_: *mut crate::leanh::LeanObject,
    mut v_ctorName_2912_: *mut crate::leanh::LeanObject,
    mut v_ctorFields_2913_: *mut crate::leanh::LeanObject,
    mut v_a_2914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2915_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2915_, 0, v_discr_2911_);
    crate::leanh::lean_closure_set(v___f_2915_, 1, v_ctorName_2912_);
    crate::leanh::lean_closure_set(v___f_2915_, 2, v_ctorFields_2913_);
    v___x_2916_ = crate::leanh::lean_apply_3(
        v_inst_2910_,
        crate::leanh::lean_box(0),
        v___f_2915_,
        v_a_2914_,
    );
    return v___x_2916_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2917_: *mut crate::leanh::LeanObject,
    mut v_vals_2918_: *mut crate::leanh::LeanObject,
    mut v_i_2919_: *mut crate::leanh::LeanObject,
    mut v_k_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2921_ = lean_array_get_size(v_keys_2917_);
                v___x_2922_ = lean_nat_dec_lt(v_i_2919_, v___x_2921_);
                if v___x_2922_ == 0 {
                    crate::leanh::lean_dec(v_i_2919_);
                    v___x_2923_ = crate::leanh::lean_box(0);
                    return v___x_2923_;
                } else {
                    v_k_x27_2924_ = lean_array_fget_borrowed(v_keys_2917_, v_i_2919_);
                    v___x_2925_ = lean_expr_eqv(v_k_2920_, v_k_x27_2924_);
                    if v___x_2925_ == 0 {
                        v___x_2926_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2927_ = lean_nat_add(v_i_2919_, v___x_2926_);
                        crate::leanh::lean_dec(v_i_2919_);
                        v_i_2919_ = v___x_2927_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2929_ = lean_array_fget_borrowed(v_vals_2918_, v_i_2919_);
                        crate::leanh::lean_dec(v_i_2919_);
                        crate::leanh::lean_inc(v___x_2929_);
                        v___x_2930_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2930_, 0, v___x_2929_);
                        return v___x_2930_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2931_: *mut crate::leanh::LeanObject,
    mut v_vals_2932_: *mut crate::leanh::LeanObject,
    mut v_i_2933_: *mut crate::leanh::LeanObject,
    mut v_k_2934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2935_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2931_, v_vals_2932_, v_i_2933_, v_k_2934_);
    crate::leanh::lean_dec_ref(v_k_2934_);
    crate::leanh::lean_dec_ref(v_vals_2932_);
    crate::leanh::lean_dec_ref(v_keys_2931_);
    return v_res_2935_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(
    mut v_x_2936_: *mut crate::leanh::LeanObject,
    mut v_x_2937_: usize,
    mut v_x_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: usize = 0;
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: usize = 0;
    let mut v_j_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: usize = 0;
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2936_) == 0 {
                    v_es_2939_ = crate::leanh::lean_ctor_get(v_x_2936_, 0);
                    v___x_2940_ = crate::leanh::lean_box(2);
                    v___x_2941_ = 5usize;
                    v___x_2942_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1);
                    v___x_2943_ = lean_usize_land(v_x_2937_, v___x_2942_);
                    v_j_2944_ = lean_usize_to_nat(v___x_2943_);
                    v___x_2945_ = lean_array_get_borrowed(v___x_2940_, v_es_2939_, v_j_2944_);
                    crate::leanh::lean_dec(v_j_2944_);
                    match crate::leanh::lean_obj_tag(v___x_2945_) {
                        0 => {
                            v_key_2946_ = crate::leanh::lean_ctor_get(v___x_2945_, 0);
                            v_val_2947_ = crate::leanh::lean_ctor_get(v___x_2945_, 1);
                            v___x_2948_ = lean_expr_eqv(v_x_2938_, v_key_2946_);
                            if v___x_2948_ == 0 {
                                v___x_2949_ = crate::leanh::lean_box(0);
                                return v___x_2949_;
                            } else {
                                crate::leanh::lean_inc(v_val_2947_);
                                v___x_2950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2950_, 0, v_val_2947_);
                                return v___x_2950_;
                            }
                        }
                        1 => {
                            v_node_2951_ = crate::leanh::lean_ctor_get(v___x_2945_, 0);
                            v___x_2952_ = lean_usize_shift_right(v_x_2937_, v___x_2941_);
                            v_x_2936_ = v_node_2951_;
                            v_x_2937_ = v___x_2952_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2954_ = crate::leanh::lean_box(0);
                            return v___x_2954_;
                        }
                    }
                } else {
                    v_ks_2955_ = crate::leanh::lean_ctor_get(v_x_2936_, 0);
                    v_vs_2956_ = crate::leanh::lean_ctor_get(v_x_2936_, 1);
                    v___x_2957_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2958_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2955_, v_vs_2956_, v___x_2957_, v_x_2938_);
                    return v___x_2958_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2959_: *mut crate::leanh::LeanObject,
    mut v_x_2960_: *mut crate::leanh::LeanObject,
    mut v_x_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1257__boxed_2962_: usize = 0;
    let mut v_res_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1257__boxed_2962_ = crate::leanh::lean_unbox_usize(v_x_2960_);
    crate::leanh::lean_dec(v_x_2960_);
    v_res_2963_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_2959_, v_x_1257__boxed_2962_, v_x_2961_);
    crate::leanh::lean_dec_ref(v_x_2961_);
    crate::leanh::lean_dec_ref(v_x_2959_);
    return v_res_2963_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(
    mut v_x_2964_: *mut crate::leanh::LeanObject,
    mut v_x_2965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2966_: u64 = 0;
    let mut v___x_2967_: usize = 0;
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2966_ = l_Lean_Expr_hash(v_x_2965_);
    v___x_2967_ = lean_uint64_to_usize(v___x_2966_);
    v___x_2968_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_2964_, v___x_2967_, v_x_2965_);
    return v___x_2968_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg___boxed(
    mut v_x_2969_: *mut crate::leanh::LeanObject,
    mut v_x_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_x_2969_, v_x_2970_);
    crate::leanh::lean_dec_ref(v_x_2970_);
    crate::leanh::lean_dec_ref(v_x_2969_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(
    mut v_e_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
    mut v_a_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctorDiscrMap_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v___x_2989_: u8 = 0;
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut v_a_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_a_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ctorDiscrMap_2979_ = crate::leanh::lean_ctor_get(v_a_2973_, 1);
                v___x_2980_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_ctorDiscrMap_2979_, v_e_2972_);
                if crate::leanh::lean_obj_tag(v___x_2980_) == 1 {
                    v_val_2981_ = crate::leanh::lean_ctor_get(v___x_2980_, 0);
                    crate::leanh::lean_inc(v_val_2981_);
                    v___x_2982_ = l_Lean_Compiler_LCNF_getType(
                        v_val_2981_,
                        v_a_2974_,
                        v_a_2975_,
                        v_a_2976_,
                        v_a_2977_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2982_) == 0 {
                        v_a_2983_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                        crate::leanh::lean_inc(v_a_2983_);
                        crate::leanh::lean_dec_ref_known(v___x_2982_, 1);
                        v___x_2984_ = l_Lean_Compiler_LCNF_inferType(
                            v_e_2972_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2984_) == 0 {
                            v_a_2985_ = crate::leanh::lean_ctor_get(v___x_2984_, 0);
                            v_isSharedCheck_2997_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2984_)) as u8;
                            if v_isSharedCheck_2997_ == 0 {
                                v___x_2987_ = v___x_2984_;
                                v_isShared_2988_ = v_isSharedCheck_2997_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2985_);
                                crate::leanh::lean_dec(v___x_2984_);
                                v___x_2987_ = crate::leanh::lean_box(0);
                                v_isShared_2988_ = v_isSharedCheck_2997_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2983_);
                            crate::leanh::lean_dec_ref_known(v___x_2980_, 1);
                            v_a_2998_ = crate::leanh::lean_ctor_get(v___x_2984_, 0);
                            v_isSharedCheck_3005_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2984_)) as u8;
                            if v_isSharedCheck_3005_ == 0 {
                                v___x_3000_ = v___x_2984_;
                                v_isShared_3001_ = v_isSharedCheck_3005_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2998_);
                                crate::leanh::lean_dec(v___x_2984_);
                                v___x_3000_ = crate::leanh::lean_box(0);
                                v_isShared_3001_ = v_isSharedCheck_3005_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2980_, 1);
                        crate::leanh::lean_dec_ref(v_e_2972_);
                        v_a_3006_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                        v_isSharedCheck_3013_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2982_)) as u8;
                        if v_isSharedCheck_3013_ == 0 {
                            v___x_3008_ = v___x_2982_;
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3006_);
                            crate::leanh::lean_dec(v___x_2982_);
                            v___x_3008_ = crate::leanh::lean_box(0);
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2980_);
                    crate::leanh::lean_dec_ref(v_e_2972_);
                    v___x_3014_ = crate::leanh::lean_box(0);
                    v___x_3015_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3015_, 0, v___x_3014_);
                    return v___x_3015_;
                }
            }
            1 => {
                v___x_2989_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2983_, v_a_2985_);
                if v___x_2989_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2980_, 1);
                    v___x_2990_ = crate::leanh::lean_box(0);
                    if v_isShared_2988_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2987_, 0, v___x_2990_);
                        v___x_2992_ = v___x_2987_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
                        v___x_2992_ = v_reuseFailAlloc_2993_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2988_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2987_, 0, v___x_2980_);
                        v___x_2995_ = v___x_2987_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2980_);
                        v___x_2995_ = v_reuseFailAlloc_2996_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2992_;
            }
            3 => {
                return v___x_2995_;
            }
            4 => {
                if v_isShared_3001_ == 0 {
                    v___x_3003_ = v___x_3000_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3004_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3003_;
            }
            6 => {
                if v_isShared_3009_ == 0 {
                    v___x_3011_ = v___x_3008_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f___boxed(
    mut v_e_3016_: *mut crate::leanh::LeanObject,
    mut v_a_3017_: *mut crate::leanh::LeanObject,
    mut v_a_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_a_3022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3023_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(
        v_e_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_,
    );
    crate::leanh::lean_dec(v_a_3021_);
    crate::leanh::lean_dec_ref(v_a_3020_);
    crate::leanh::lean_dec(v_a_3019_);
    crate::leanh::lean_dec_ref(v_a_3018_);
    crate::leanh::lean_dec_ref(v_a_3017_);
    return v_res_3023_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0(
    mut v_00_u03b2_3024_: *mut crate::leanh::LeanObject,
    mut v_x_3025_: *mut crate::leanh::LeanObject,
    mut v_x_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_x_3025_, v_x_3026_);
    return v___x_3027_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___boxed(
    mut v_00_u03b2_3028_: *mut crate::leanh::LeanObject,
    mut v_x_3029_: *mut crate::leanh::LeanObject,
    mut v_x_3030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3031_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0(v_00_u03b2_3028_, v_x_3029_, v_x_3030_);
    crate::leanh::lean_dec_ref(v_x_3030_);
    crate::leanh::lean_dec_ref(v_x_3029_);
    return v_res_3031_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0(
    mut v_00_u03b2_3032_: *mut crate::leanh::LeanObject,
    mut v_x_3033_: *mut crate::leanh::LeanObject,
    mut v_x_3034_: usize,
    mut v_x_3035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3036_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_3033_, v_x_3034_, v_x_3035_);
    return v___x_3036_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_3037_: *mut crate::leanh::LeanObject,
    mut v_x_3038_: *mut crate::leanh::LeanObject,
    mut v_x_3039_: *mut crate::leanh::LeanObject,
    mut v_x_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1401__boxed_3041_: usize = 0;
    let mut v_res_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1401__boxed_3041_ = crate::leanh::lean_unbox_usize(v_x_3039_);
    crate::leanh::lean_dec(v_x_3039_);
    v_res_3042_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0(v_00_u03b2_3037_, v_x_3038_, v_x_1401__boxed_3041_, v_x_3040_);
    crate::leanh::lean_dec_ref(v_x_3040_);
    crate::leanh::lean_dec_ref(v_x_3038_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3043_: *mut crate::leanh::LeanObject,
    mut v_keys_3044_: *mut crate::leanh::LeanObject,
    mut v_vals_3045_: *mut crate::leanh::LeanObject,
    mut v_heq_3046_: *mut crate::leanh::LeanObject,
    mut v_i_3047_: *mut crate::leanh::LeanObject,
    mut v_k_3048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3049_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3044_, v_vals_3045_, v_i_3047_, v_k_3048_);
    return v___x_3049_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3050_: *mut crate::leanh::LeanObject,
    mut v_keys_3051_: *mut crate::leanh::LeanObject,
    mut v_vals_3052_: *mut crate::leanh::LeanObject,
    mut v_heq_3053_: *mut crate::leanh::LeanObject,
    mut v_i_3054_: *mut crate::leanh::LeanObject,
    mut v_k_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3050_, v_keys_3051_, v_vals_3052_, v_heq_3053_, v_i_3054_, v_k_3055_);
    crate::leanh::lean_dec_ref(v_k_3055_);
    crate::leanh::lean_dec_ref(v_vals_3052_);
    crate::leanh::lean_dec_ref(v_keys_3051_);
    return v_res_3056_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_DiscrM(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_DiscrM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
}
