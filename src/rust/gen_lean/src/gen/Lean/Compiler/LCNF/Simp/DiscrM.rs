// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.DiscrM
// Imports: Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Simp.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
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
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__1_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__1_value)
            as *mut leanh::LeanObject,
        16112798088292836701 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__3_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__3_value)
            as *mut leanh::LeanObject,
        13428217069302927667 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__1_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__0_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__4_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorIdx(
    mut v_x_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1529_) == 0 {
        let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1530_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1530_;
    } else {
        let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1531_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1531_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorIdx___boxed(
    mut v_x_1532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorIdx(v_x_1532_);
    leanh::lean_dec_ref(v_x_1532_);
    return v_res_1533_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(
    mut v_t_1534_: *mut leanh::LeanObject,
    mut v_k_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1534_) == 0 {
        let mut v_val_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_args_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1536_ = leanh::lean_ctor_get(v_t_1534_, 0);
        leanh::lean_inc_ref(v_val_1536_);
        v_args_1537_ = leanh::lean_ctor_get(v_t_1534_, 1);
        leanh::lean_inc_ref(v_args_1537_);
        leanh::lean_dec_ref_known(v_t_1534_, 2);
        v___x_1538_ = leanh::lean_apply_2(v_k_1535_, v_val_1536_, v_args_1537_);
        return v___x_1538_;
    } else {
        let mut v_n_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_n_1539_ = leanh::lean_ctor_get(v_t_1534_, 0);
        leanh::lean_inc(v_n_1539_);
        leanh::lean_dec_ref_known(v_t_1534_, 1);
        v___x_1540_ = leanh::lean_apply_1(v_k_1535_, v_n_1539_);
        return v___x_1540_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim(
    mut v_motive_1541_: *mut leanh::LeanObject,
    mut v_ctorIdx_1542_: *mut leanh::LeanObject,
    mut v_t_1543_: *mut leanh::LeanObject,
    mut v_h_1544_: *mut leanh::LeanObject,
    mut v_k_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1543_, v_k_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___boxed(
    mut v_motive_1547_: *mut leanh::LeanObject,
    mut v_ctorIdx_1548_: *mut leanh::LeanObject,
    mut v_t_1549_: *mut leanh::LeanObject,
    mut v_h_1550_: *mut leanh::LeanObject,
    mut v_k_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim(
        v_motive_1547_,
        v_ctorIdx_1548_,
        v_t_1549_,
        v_h_1550_,
        v_k_1551_,
    );
    leanh::lean_dec(v_ctorIdx_1548_);
    return v_res_1552_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctor_elim___redArg(
    mut v_t_1553_: *mut leanh::LeanObject,
    mut v_ctor_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1553_, v_ctor_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_ctor_elim(
    mut v_motive_1556_: *mut leanh::LeanObject,
    mut v_t_1557_: *mut leanh::LeanObject,
    mut v_h_1558_: *mut leanh::LeanObject,
    mut v_ctor_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1557_, v_ctor_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_natVal_elim___redArg(
    mut v_t_1561_: *mut leanh::LeanObject,
    mut v_natVal_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1563_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1561_, v_natVal_1562_);
    return v___x_1563_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_natVal_elim(
    mut v_motive_1564_: *mut leanh::LeanObject,
    mut v_t_1565_: *mut leanh::LeanObject,
    mut v_h_1566_: *mut leanh::LeanObject,
    mut v_natVal_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_ctorElim___redArg(v_t_1565_, v_natVal_1567_);
    return v___x_1568_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(
    mut v_x_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1578_) == 0 {
        let mut v_val_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toConstantVal_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1579_ = leanh::lean_ctor_get(v_x_1578_, 0);
        v_toConstantVal_1580_ = leanh::lean_ctor_get(v_val_1579_, 0);
        v_name_1581_ = leanh::lean_ctor_get(v_toConstantVal_1580_, 0);
        leanh::lean_inc(v_name_1581_);
        return v_name_1581_;
    } else {
        let mut v_n_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: u8 = 0;
        v_n_1582_ = leanh::lean_ctor_get(v_x_1578_, 0);
        v___x_1583_ = leanh::lean_unsigned_to_nat(0);
        v___x_1584_ = lean_nat_dec_eq(v_n_1582_, v___x_1583_);
        if v___x_1584_ == 0 {
            let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1585_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__2;
            return v___x_1585_;
        } else {
            let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1586_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___closed__4;
            return v___x_1586_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getName___boxed(
    mut v_x_1587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_x_1587_);
    leanh::lean_dec_ref(v_x_1587_);
    return v_res_1588_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumParams(
    mut v_x_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1589_) == 0 {
        let mut v_val_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_numParams_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1590_ = leanh::lean_ctor_get(v_x_1589_, 0);
        v_numParams_1591_ = leanh::lean_ctor_get(v_val_1590_, 3);
        leanh::lean_inc(v_numParams_1591_);
        return v_numParams_1591_;
    } else {
        let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1592_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1592_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumParams___boxed(
    mut v_x_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumParams(v_x_1593_);
    leanh::lean_dec_ref(v_x_1593_);
    return v_res_1594_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumFields(
    mut v_x_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1595_) == 0 {
        let mut v_val_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_numFields_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1596_ = leanh::lean_ctor_get(v_x_1595_, 0);
        v_numFields_1597_ = leanh::lean_ctor_get(v_val_1596_, 4);
        leanh::lean_inc(v_numFields_1597_);
        return v_numFields_1597_;
    } else {
        let mut v_n_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: u8 = 0;
        v_n_1598_ = leanh::lean_ctor_get(v_x_1595_, 0);
        v___x_1599_ = leanh::lean_unsigned_to_nat(0);
        v___x_1600_ = lean_nat_dec_eq(v_n_1598_, v___x_1599_);
        if v___x_1600_ == 0 {
            let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1601_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1601_;
        } else {
            return v___x_1599_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumFields___boxed(
    mut v_x_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getNumFields(v_x_1602_);
    leanh::lean_dec_ref(v_x_1602_);
    return v_res_1603_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(
    mut v_t_1604_: *mut leanh::LeanObject,
    mut v_k_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1604_) == 0 {
                    v_k_1606_ = leanh::lean_ctor_get(v_t_1604_, 1);
                    v_v_1607_ = leanh::lean_ctor_get(v_t_1604_, 2);
                    v_l_1608_ = leanh::lean_ctor_get(v_t_1604_, 3);
                    v_r_1609_ = leanh::lean_ctor_get(v_t_1604_, 4);
                    v___x_1610_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1605_, v_k_1606_);
                    match v___x_1610_ {
                        0 => {
                            v_t_1604_ = v_l_1608_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_1607_);
                            v___x_1612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1612_, 0, v_v_1607_);
                            return v___x_1612_;
                        }
                        _ => {
                            v_t_1604_ = v_r_1609_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1614_ = leanh::lean_box(0);
                    return v___x_1614_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg___boxed(
    mut v_t_1615_: *mut leanh::LeanObject,
    mut v_k_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_t_1615_, v_k_1616_);
    leanh::lean_dec(v_k_1616_);
    leanh::lean_dec(v_t_1615_);
    return v_res_1617_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
    mut v_fvarId_1618_: *mut leanh::LeanObject,
    mut v_a_1619_: *mut leanh::LeanObject,
    mut v_a_1620_: *mut leanh::LeanObject,
    mut v_a_1621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___y_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrCtorMap_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v_value_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v_val_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut v_declName_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v_val_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_isSharedCheck_1685_: u8 = 0;
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_a_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = leanh::lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1687_ = (!leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1630_ = v___x_1627_;
                        v_isShared_1631_ = v_isSharedCheck_1687_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1628_);
                        leanh::lean_dec(v___x_1627_);
                        v___x_1630_ = leanh::lean_box(0);
                        v_isShared_1631_ = v_isSharedCheck_1687_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1688_ = leanh::lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1695_ = (!leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1695_ == 0 {
                        v___x_1690_ = v___x_1627_;
                        v_isShared_1691_ = v_isSharedCheck_1695_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1688_);
                        leanh::lean_dec(v___x_1627_);
                        v___x_1690_ = leanh::lean_box(0);
                        v_isShared_1691_ = v_isSharedCheck_1695_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1624_ = leanh::lean_box(0);
                v___x_1625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1625_, 0, v___x_1624_);
                return v___x_1625_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_1628_) == 1 {
                    v_val_1639_ = leanh::lean_ctor_get(v_a_1628_, 0);
                    v_isSharedCheck_1686_ = (!leanh::lean_is_exclusive(v_a_1628_)) as u8;
                    if v_isSharedCheck_1686_ == 0 {
                        v___x_1641_ = v_a_1628_;
                        v_isShared_1642_ = v_isSharedCheck_1686_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1639_);
                        leanh::lean_dec(v_a_1628_);
                        v___x_1641_ = leanh::lean_box(0);
                        v_isShared_1642_ = v_isSharedCheck_1686_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1628_);
                    v___y_1633_ = v_a_1619_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_discrCtorMap_1634_ = leanh::lean_ctor_get(v___y_1633_, 0);
                v___x_1635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_discrCtorMap_1634_, v_fvarId_1618_);
                if v_isShared_1631_ == 0 {
                    leanh::lean_ctor_set(v___x_1630_, 0, v___x_1635_);
                    v___x_1637_ = v___x_1630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
                    v___x_1637_ = v_reuseFailAlloc_1638_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1637_;
            }
            5 => {
                v_value_1643_ = leanh::lean_ctor_get(v_val_1639_, 3);
                leanh::lean_inc(v_value_1643_);
                leanh::lean_dec(v_val_1639_);
                match leanh::lean_obj_tag(v_value_1643_) {
                    0 => {
                        v_value_1644_ = leanh::lean_ctor_get(v_value_1643_, 0);
                        v_isSharedCheck_1662_ =
                            (!leanh::lean_is_exclusive(v_value_1643_)) as u8;
                        if v_isSharedCheck_1662_ == 0 {
                            v___x_1646_ = v_value_1643_;
                            v_isShared_1647_ = v_isSharedCheck_1662_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_value_1644_);
                            leanh::lean_dec(v_value_1643_);
                            v___x_1646_ = leanh::lean_box(0);
                            v_isShared_1647_ = v_isSharedCheck_1662_;
                            state = 6;
                            continue;
                        }
                    }
                    3 => {
                        leanh::lean_del_object(v___x_1641_);
                        leanh::lean_del_object(v___x_1630_);
                        v_declName_1663_ = leanh::lean_ctor_get(v_value_1643_, 0);
                        leanh::lean_inc(v_declName_1663_);
                        v_args_1664_ = leanh::lean_ctor_get(v_value_1643_, 2);
                        leanh::lean_inc_ref(v_args_1664_);
                        leanh::lean_dec_ref_known(v_value_1643_, 3);
                        v___x_1665_ = lean_st_ref_get(v_a_1621_);
                        v_env_1666_ = leanh::lean_ctor_get(v___x_1665_, 0);
                        leanh::lean_inc_ref(v_env_1666_);
                        leanh::lean_dec(v___x_1665_);
                        v___x_1667_ = 0;
                        v___x_1668_ =
                            l_Lean_Environment_find_x3f(v_env_1666_, v_declName_1663_, v___x_1667_);
                        if leanh::lean_obj_tag(v___x_1668_) == 1 {
                            v_val_1669_ = leanh::lean_ctor_get(v___x_1668_, 0);
                            v_isSharedCheck_1685_ =
                                (!leanh::lean_is_exclusive(v___x_1668_)) as u8;
                            if v_isSharedCheck_1685_ == 0 {
                                v___x_1671_ = v___x_1668_;
                                v_isShared_1672_ = v_isSharedCheck_1685_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_1669_);
                                leanh::lean_dec(v___x_1668_);
                                v___x_1671_ = leanh::lean_box(0);
                                v_isShared_1672_ = v_isSharedCheck_1685_;
                                state = 11;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_1668_);
                            leanh::lean_dec_ref(v_args_1664_);
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_value_1643_);
                        leanh::lean_del_object(v___x_1641_);
                        v___y_1633_ = v_a_1619_;
                        state = 3;
                        continue;
                    }
                }
            }
            6 => {
                if leanh::lean_obj_tag(v_value_1644_) == 0 {
                    leanh::lean_del_object(v___x_1630_);
                    v_val_1648_ = leanh::lean_ctor_get(v_value_1644_, 0);
                    v_isSharedCheck_1661_ = (!leanh::lean_is_exclusive(v_value_1644_)) as u8;
                    if v_isSharedCheck_1661_ == 0 {
                        v___x_1650_ = v_value_1644_;
                        v_isShared_1651_ = v_isSharedCheck_1661_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1648_);
                        leanh::lean_dec(v_value_1644_);
                        v___x_1650_ = leanh::lean_box(0);
                        v_isShared_1651_ = v_isSharedCheck_1661_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1646_);
                    leanh::lean_dec_ref(v_value_1644_);
                    leanh::lean_del_object(v___x_1641_);
                    v___y_1633_ = v_a_1619_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v_isShared_1651_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1650_, 1);
                    v___x_1653_ = v___x_1650_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_val_1648_);
                    v___x_1653_ = v_reuseFailAlloc_1660_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1642_ == 0 {
                    leanh::lean_ctor_set(v___x_1641_, 0, v___x_1653_);
                    v___x_1655_ = v___x_1641_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1653_);
                    v___x_1655_ = v_reuseFailAlloc_1659_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1647_ == 0 {
                    leanh::lean_ctor_set(v___x_1646_, 0, v___x_1655_);
                    v___x_1657_ = v___x_1646_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
                    v___x_1657_ = v_reuseFailAlloc_1658_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1657_;
            }
            11 => {
                if leanh::lean_obj_tag(v_val_1669_) == 6 {
                    v_val_1673_ = leanh::lean_ctor_get(v_val_1669_, 0);
                    v_isSharedCheck_1684_ = (!leanh::lean_is_exclusive(v_val_1669_)) as u8;
                    if v_isSharedCheck_1684_ == 0 {
                        v___x_1675_ = v_val_1669_;
                        v_isShared_1676_ = v_isSharedCheck_1684_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1673_);
                        leanh::lean_dec(v_val_1669_);
                        v___x_1675_ = leanh::lean_box(0);
                        v_isShared_1676_ = v_isSharedCheck_1684_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1671_);
                    leanh::lean_dec(v_val_1669_);
                    leanh::lean_dec_ref(v_args_1664_);
                    state = 1;
                    continue;
                }
            }
            12 => {
                v___x_1677_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1677_, 0, v_val_1673_);
                leanh::lean_ctor_set(v___x_1677_, 1, v_args_1664_);
                if v_isShared_1672_ == 0 {
                    leanh::lean_ctor_set(v___x_1671_, 0, v___x_1677_);
                    v___x_1679_ = v___x_1671_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1677_);
                    v___x_1679_ = v_reuseFailAlloc_1683_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_1676_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1675_, 0);
                    leanh::lean_ctor_set(v___x_1675_, 0, v___x_1679_);
                    v___x_1681_ = v___x_1675_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
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
                    v_reuseFailAlloc_1694_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
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
    mut v_fvarId_1696_: *mut leanh::LeanObject,
    mut v_a_1697_: *mut leanh::LeanObject,
    mut v_a_1698_: *mut leanh::LeanObject,
    mut v_a_1699_: *mut leanh::LeanObject,
    mut v_a_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
        v_fvarId_1696_,
        v_a_1697_,
        v_a_1698_,
        v_a_1699_,
    );
    leanh::lean_dec(v_a_1699_);
    leanh::lean_dec(v_a_1698_);
    leanh::lean_dec_ref(v_a_1697_);
    leanh::lean_dec(v_fvarId_1696_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtor_x3f(
    mut v_fvarId_1702_: *mut leanh::LeanObject,
    mut v_a_1703_: *mut leanh::LeanObject,
    mut v_a_1704_: *mut leanh::LeanObject,
    mut v_a_1705_: *mut leanh::LeanObject,
    mut v_a_1706_: *mut leanh::LeanObject,
    mut v_a_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1709_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
        v_fvarId_1702_,
        v_a_1703_,
        v_a_1705_,
        v_a_1707_,
    );
    return v___x_1709_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtor_x3f___boxed(
    mut v_fvarId_1710_: *mut leanh::LeanObject,
    mut v_a_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
    mut v_a_1713_: *mut leanh::LeanObject,
    mut v_a_1714_: *mut leanh::LeanObject,
    mut v_a_1715_: *mut leanh::LeanObject,
    mut v_a_1716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f(
        v_fvarId_1710_,
        v_a_1711_,
        v_a_1712_,
        v_a_1713_,
        v_a_1714_,
        v_a_1715_,
    );
    leanh::lean_dec(v_a_1715_);
    leanh::lean_dec_ref(v_a_1714_);
    leanh::lean_dec(v_a_1713_);
    leanh::lean_dec_ref(v_a_1712_);
    leanh::lean_dec_ref(v_a_1711_);
    leanh::lean_dec(v_fvarId_1710_);
    return v_res_1717_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0(
    mut v_00_u03b4_1718_: *mut leanh::LeanObject,
    mut v_t_1719_: *mut leanh::LeanObject,
    mut v_k_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_t_1719_, v_k_1720_);
    return v___x_1721_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___boxed(
    mut v_00_u03b4_1722_: *mut leanh::LeanObject,
    mut v_t_1723_: *mut leanh::LeanObject,
    mut v_k_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0(v_00_u03b4_1722_, v_t_1723_, v_k_1724_);
    leanh::lean_dec(v_k_1724_);
    leanh::lean_dec(v_t_1723_);
    return v_res_1725_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(
    mut v_fvarId_1726_: *mut leanh::LeanObject,
    mut v_a_1727_: *mut leanh::LeanObject,
    mut v_a_1728_: *mut leanh::LeanObject,
    mut v_a_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1735_: u8 = 0;
    let mut v_val_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v_a_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1731_) == 0 {
                    v_a_1732_ = leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1752_ = (!leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1752_ == 0 {
                        v___x_1734_ = v___x_1731_;
                        v_isShared_1735_ = v_isSharedCheck_1752_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1732_);
                        leanh::lean_dec(v___x_1731_);
                        v___x_1734_ = leanh::lean_box(0);
                        v_isShared_1735_ = v_isSharedCheck_1752_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1753_ = leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1760_ = (!leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1760_ == 0 {
                        v___x_1755_ = v___x_1731_;
                        v_isShared_1756_ = v_isSharedCheck_1760_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1753_);
                        leanh::lean_dec(v___x_1731_);
                        v___x_1755_ = leanh::lean_box(0);
                        v_isShared_1756_ = v_isSharedCheck_1760_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1732_) == 1 {
                    v_val_1736_ = leanh::lean_ctor_get(v_a_1732_, 0);
                    v_isSharedCheck_1747_ = (!leanh::lean_is_exclusive(v_a_1732_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1738_ = v_a_1732_;
                        v_isShared_1739_ = v_isSharedCheck_1747_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1736_);
                        leanh::lean_dec(v_a_1732_);
                        v___x_1738_ = leanh::lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1747_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1732_);
                    v___x_1748_ = leanh::lean_box(0);
                    if v_isShared_1735_ == 0 {
                        leanh::lean_ctor_set(v___x_1734_, 0, v___x_1748_);
                        v___x_1750_ = v___x_1734_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1751_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
                        v___x_1750_ = v_reuseFailAlloc_1751_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1740_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_1736_);
                leanh::lean_dec(v_val_1736_);
                if v_isShared_1739_ == 0 {
                    leanh::lean_ctor_set(v___x_1738_, 0, v___x_1740_);
                    v___x_1742_ = v___x_1738_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1740_);
                    v___x_1742_ = v_reuseFailAlloc_1746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1735_ == 0 {
                    leanh::lean_ctor_set(v___x_1734_, 0, v___x_1742_);
                    v___x_1744_ = v___x_1734_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
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
                    v_reuseFailAlloc_1759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
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
    mut v_fvarId_1761_: *mut leanh::LeanObject,
    mut v_a_1762_: *mut leanh::LeanObject,
    mut v_a_1763_: *mut leanh::LeanObject,
    mut v_a_1764_: *mut leanh::LeanObject,
    mut v_a_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(
        v_fvarId_1761_,
        v_a_1762_,
        v_a_1763_,
        v_a_1764_,
    );
    leanh::lean_dec(v_a_1764_);
    leanh::lean_dec(v_a_1763_);
    leanh::lean_dec_ref(v_a_1762_);
    leanh::lean_dec(v_fvarId_1761_);
    return v_res_1766_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtorName_x3f(
    mut v_fvarId_1767_: *mut leanh::LeanObject,
    mut v_a_1768_: *mut leanh::LeanObject,
    mut v_a_1769_: *mut leanh::LeanObject,
    mut v_a_1770_: *mut leanh::LeanObject,
    mut v_a_1771_: *mut leanh::LeanObject,
    mut v_a_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(
        v_fvarId_1767_,
        v_a_1768_,
        v_a_1770_,
        v_a_1772_,
    );
    return v___x_1774_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___boxed(
    mut v_fvarId_1775_: *mut leanh::LeanObject,
    mut v_a_1776_: *mut leanh::LeanObject,
    mut v_a_1777_: *mut leanh::LeanObject,
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
    mut v_a_1780_: *mut leanh::LeanObject,
    mut v_a_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f(
        v_fvarId_1775_,
        v_a_1776_,
        v_a_1777_,
        v_a_1778_,
        v_a_1779_,
        v_a_1780_,
    );
    leanh::lean_dec(v_a_1780_);
    leanh::lean_dec_ref(v_a_1779_);
    leanh::lean_dec(v_a_1778_);
    leanh::lean_dec_ref(v_a_1777_);
    leanh::lean_dec_ref(v_a_1776_);
    leanh::lean_dec(v_fvarId_1775_);
    return v_res_1782_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1783_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0);
    v___x_1785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1785_, 0, v___x_1784_);
    return v___x_1785_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1);
    v___x_1787_ = leanh::lean_unsigned_to_nat(0);
    v___x_1788_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1788_, 0, v___x_1787_);
    leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
    leanh::lean_ctor_set(v___x_1788_, 2, v___x_1787_);
    leanh::lean_ctor_set(v___x_1788_, 3, v___x_1787_);
    leanh::lean_ctor_set(v___x_1788_, 4, v___x_1786_);
    leanh::lean_ctor_set(v___x_1788_, 5, v___x_1786_);
    leanh::lean_ctor_set(v___x_1788_, 6, v___x_1786_);
    leanh::lean_ctor_set(v___x_1788_, 7, v___x_1786_);
    leanh::lean_ctor_set(v___x_1788_, 8, v___x_1786_);
    leanh::lean_ctor_set(v___x_1788_, 9, v___x_1786_);
    return v___x_1788_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1789_ = leanh::lean_unsigned_to_nat(32);
    v___x_1790_ = lean_mk_empty_array_with_capacity(v___x_1789_);
    v___x_1791_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1791_, 0, v___x_1790_);
    return v___x_1791_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1792_: usize = 0;
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = 5usize;
    v___x_1793_ = leanh::lean_unsigned_to_nat(0);
    v___x_1794_ = leanh::lean_unsigned_to_nat(32);
    v___x_1795_ = lean_mk_empty_array_with_capacity(v___x_1794_);
    v___x_1796_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3);
    v___x_1797_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1797_, 0, v___x_1796_);
    leanh::lean_ctor_set(v___x_1797_, 1, v___x_1795_);
    leanh::lean_ctor_set(v___x_1797_, 2, v___x_1793_);
    leanh::lean_ctor_set(v___x_1797_, 3, v___x_1793_);
    leanh::lean_ctor_set_usize(v___x_1797_, 4, v___x_1792_);
    return v___x_1797_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = leanh::lean_box(1);
    v___x_1799_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4);
    v___x_1800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1);
    v___x_1801_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 1, v___x_1799_);
    leanh::lean_ctor_set(v___x_1801_, 2, v___x_1798_);
    return v___x_1801_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(
    mut v_msgData_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = lean_st_ref_get(v___y_1804_);
    v_env_1807_ = leanh::lean_ctor_get(v___x_1806_, 0);
    leanh::lean_inc_ref(v_env_1807_);
    leanh::lean_dec(v___x_1806_);
    v_options_1808_ = leanh::lean_ctor_get(v___y_1803_, 2);
    v___x_1809_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2);
    v___x_1810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5);
    leanh::lean_inc_ref(v_options_1808_);
    v___x_1811_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1811_, 0, v_env_1807_);
    leanh::lean_ctor_set(v___x_1811_, 1, v___x_1809_);
    leanh::lean_ctor_set(v___x_1811_, 2, v___x_1810_);
    leanh::lean_ctor_set(v___x_1811_, 3, v_options_1808_);
    v___x_1812_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    leanh::lean_ctor_set(v___x_1812_, 1, v_msgData_1802_);
    v___x_1813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    return v___x_1813_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___boxed(
    mut v_msgData_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(v_msgData_1814_, v___y_1815_, v___y_1816_);
    leanh::lean_dec(v___y_1816_);
    leanh::lean_dec_ref(v___y_1815_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(
    mut v_msg_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
    mut v___y_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1823_ = leanh::lean_ctor_get(v___y_1820_, 5);
                v___x_1824_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(v_msg_1819_, v___y_1820_, v___y_1821_);
                v_a_1825_ = leanh::lean_ctor_get(v___x_1824_, 0);
                v_isSharedCheck_1833_ = (!leanh::lean_is_exclusive(v___x_1824_)) as u8;
                if v_isSharedCheck_1833_ == 0 {
                    v___x_1827_ = v___x_1824_;
                    v_isShared_1828_ = v_isSharedCheck_1833_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1825_);
                    leanh::lean_dec(v___x_1824_);
                    v___x_1827_ = leanh::lean_box(0);
                    v_isShared_1828_ = v_isSharedCheck_1833_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1823_);
                v___x_1829_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1829_, 0, v_ref_1823_);
                leanh::lean_ctor_set(v___x_1829_, 1, v_a_1825_);
                if v_isShared_1828_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1827_, 1);
                    leanh::lean_ctor_set(v___x_1827_, 0, v___x_1829_);
                    v___x_1831_ = v___x_1827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
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
    mut v_msg_1834_: *mut leanh::LeanObject,
    mut v___y_1835_: *mut leanh::LeanObject,
    mut v___y_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1834_, v___y_1835_, v___y_1836_);
    leanh::lean_dec(v___y_1836_);
    leanh::lean_dec_ref(v___y_1835_);
    return v_res_1838_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_1839_: *mut leanh::LeanObject,
    mut v_msg_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1856_: u8 = 0;
    let mut v_cancelTk_x3f_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1858_: u8 = 0;
    let mut v_inheritedTraceOptions_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1844_ = leanh::lean_ctor_get(v___y_1841_, 0);
    v_fileMap_1845_ = leanh::lean_ctor_get(v___y_1841_, 1);
    v_options_1846_ = leanh::lean_ctor_get(v___y_1841_, 2);
    v_currRecDepth_1847_ = leanh::lean_ctor_get(v___y_1841_, 3);
    v_maxRecDepth_1848_ = leanh::lean_ctor_get(v___y_1841_, 4);
    v_ref_1849_ = leanh::lean_ctor_get(v___y_1841_, 5);
    v_currNamespace_1850_ = leanh::lean_ctor_get(v___y_1841_, 6);
    v_openDecls_1851_ = leanh::lean_ctor_get(v___y_1841_, 7);
    v_initHeartbeats_1852_ = leanh::lean_ctor_get(v___y_1841_, 8);
    v_maxHeartbeats_1853_ = leanh::lean_ctor_get(v___y_1841_, 9);
    v_quotContext_1854_ = leanh::lean_ctor_get(v___y_1841_, 10);
    v_currMacroScope_1855_ = leanh::lean_ctor_get(v___y_1841_, 11);
    v_diag_1856_ = leanh::lean_ctor_get_uint8(
        v___y_1841_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1857_ = leanh::lean_ctor_get(v___y_1841_, 12);
    v_suppressElabErrors_1858_ = leanh::lean_ctor_get_uint8(
        v___y_1841_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1859_ = leanh::lean_ctor_get(v___y_1841_, 13);
    v_ref_1860_ = l_Lean_replaceRef(v_ref_1839_, v_ref_1849_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1859_);
    leanh::lean_inc(v_cancelTk_x3f_1857_);
    leanh::lean_inc(v_currMacroScope_1855_);
    leanh::lean_inc(v_quotContext_1854_);
    leanh::lean_inc(v_maxHeartbeats_1853_);
    leanh::lean_inc(v_initHeartbeats_1852_);
    leanh::lean_inc(v_openDecls_1851_);
    leanh::lean_inc(v_currNamespace_1850_);
    leanh::lean_inc(v_maxRecDepth_1848_);
    leanh::lean_inc(v_currRecDepth_1847_);
    leanh::lean_inc_ref(v_options_1846_);
    leanh::lean_inc_ref(v_fileMap_1845_);
    leanh::lean_inc_ref(v_fileName_1844_);
    v___x_1861_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1861_, 0, v_fileName_1844_);
    leanh::lean_ctor_set(v___x_1861_, 1, v_fileMap_1845_);
    leanh::lean_ctor_set(v___x_1861_, 2, v_options_1846_);
    leanh::lean_ctor_set(v___x_1861_, 3, v_currRecDepth_1847_);
    leanh::lean_ctor_set(v___x_1861_, 4, v_maxRecDepth_1848_);
    leanh::lean_ctor_set(v___x_1861_, 5, v_ref_1860_);
    leanh::lean_ctor_set(v___x_1861_, 6, v_currNamespace_1850_);
    leanh::lean_ctor_set(v___x_1861_, 7, v_openDecls_1851_);
    leanh::lean_ctor_set(v___x_1861_, 8, v_initHeartbeats_1852_);
    leanh::lean_ctor_set(v___x_1861_, 9, v_maxHeartbeats_1853_);
    leanh::lean_ctor_set(v___x_1861_, 10, v_quotContext_1854_);
    leanh::lean_ctor_set(v___x_1861_, 11, v_currMacroScope_1855_);
    leanh::lean_ctor_set(v___x_1861_, 12, v_cancelTk_x3f_1857_);
    leanh::lean_ctor_set(v___x_1861_, 13, v_inheritedTraceOptions_1859_);
    leanh::lean_ctor_set_uint8(
        v___x_1861_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1856_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1861_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1858_,
    );
    v___x_1862_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1840_, v___x_1861_, v___y_1842_);
    leanh::lean_dec_ref_known(v___x_1861_, 14);
    return v___x_1862_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_1863_: *mut leanh::LeanObject,
    mut v_msg_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1868_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1863_, v_msg_1864_, v___y_1865_, v___y_1866_);
    leanh::lean_dec(v___y_1866_);
    leanh::lean_dec_ref(v___y_1865_);
    leanh::lean_dec(v_ref_1863_);
    return v_res_1868_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
    v___x_1871_ = l_Lean_stringToMessageData(v___x_1870_);
    return v___x_1871_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
    v___x_1874_ = l_Lean_stringToMessageData(v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1876_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
    v___x_1877_ = l_Lean_stringToMessageData(v___x_1876_);
    return v___x_1877_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1880_ = l_Lean_stringToMessageData(v___x_1879_);
    return v___x_1880_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1883_ = l_Lean_stringToMessageData(v___x_1882_);
    return v___x_1883_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1886_ = l_Lean_stringToMessageData(v___x_1885_);
    return v___x_1886_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1888_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
    return v___x_1889_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1890_: *mut leanh::LeanObject,
    mut v_declHint_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: u8 = 0;
    let mut v_isExporting_1897_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: u8 = 0;
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1894_ = lean_st_ref_get(v___y_1892_);
                v_env_1895_ = leanh::lean_ctor_get(v___x_1894_, 0);
                leanh::lean_inc_ref(v_env_1895_);
                leanh::lean_dec(v___x_1894_);
                v___x_1896_ = l_Lean_Name_isAnonymous(v_declHint_1891_);
                if v___x_1896_ == 0 {
                    v_isExporting_1897_ = leanh::lean_ctor_get_uint8(
                        v_env_1895_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1897_ == 0 {
                        leanh::lean_dec_ref(v_env_1895_);
                        leanh::lean_dec(v_declHint_1891_);
                        v___x_1898_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1898_, 0, v_msg_1890_);
                        return v___x_1898_;
                    } else {
                        leanh::lean_inc_ref(v_env_1895_);
                        v___x_1899_ = l_Lean_Environment_setExporting(v_env_1895_, v___x_1896_);
                        leanh::lean_inc(v_declHint_1891_);
                        leanh::lean_inc_ref(v___x_1899_);
                        v___x_1900_ = l_Lean_Environment_contains(
                            v___x_1899_,
                            v_declHint_1891_,
                            v_isExporting_1897_,
                        );
                        if v___x_1900_ == 0 {
                            leanh::lean_dec_ref(v___x_1899_);
                            leanh::lean_dec_ref(v_env_1895_);
                            leanh::lean_dec(v_declHint_1891_);
                            v___x_1901_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1901_, 0, v_msg_1890_);
                            return v___x_1901_;
                        } else {
                            v___x_1902_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2);
                            v___x_1903_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5);
                            v___x_1904_ = l_Lean_Options_empty;
                            v___x_1905_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1905_, 0, v___x_1899_);
                            leanh::lean_ctor_set(v___x_1905_, 1, v___x_1902_);
                            leanh::lean_ctor_set(v___x_1905_, 2, v___x_1903_);
                            leanh::lean_ctor_set(v___x_1905_, 3, v___x_1904_);
                            leanh::lean_inc(v_declHint_1891_);
                            v___x_1906_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1891_, v___x_1896_);
                            v_c_1907_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1907_, 0, v___x_1905_);
                            leanh::lean_ctor_set(v_c_1907_, 1, v___x_1906_);
                            v___x_1908_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1895_,
                                v_declHint_1891_,
                            );
                            if leanh::lean_obj_tag(v___x_1908_) == 0 {
                                leanh::lean_dec_ref(v_env_1895_);
                                leanh::lean_dec(v_declHint_1891_);
                                v___x_1909_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                                v___x_1910_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1910_, 0, v___x_1909_);
                                leanh::lean_ctor_set(v___x_1910_, 1, v_c_1907_);
                                v___x_1911_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
                                v___x_1912_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1912_, 0, v___x_1910_);
                                leanh::lean_ctor_set(v___x_1912_, 1, v___x_1911_);
                                v___x_1913_ = l_Lean_MessageData_note(v___x_1912_);
                                v___x_1914_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1914_, 0, v_msg_1890_);
                                leanh::lean_ctor_set(v___x_1914_, 1, v___x_1913_);
                                v___x_1915_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1915_, 0, v___x_1914_);
                                return v___x_1915_;
                            } else {
                                v_val_1916_ = leanh::lean_ctor_get(v___x_1908_, 0);
                                v_isSharedCheck_1951_ =
                                    (!leanh::lean_is_exclusive(v___x_1908_)) as u8;
                                if v_isSharedCheck_1951_ == 0 {
                                    v___x_1918_ = v___x_1908_;
                                    v_isShared_1919_ = v_isSharedCheck_1951_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1916_);
                                    leanh::lean_dec(v___x_1908_);
                                    v___x_1918_ = leanh::lean_box(0);
                                    v_isShared_1919_ = v_isSharedCheck_1951_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1895_);
                    leanh::lean_dec(v_declHint_1891_);
                    v___x_1952_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1952_, 0, v_msg_1890_);
                    return v___x_1952_;
                }
            }
            1 => {
                v___x_1920_ = leanh::lean_box(0);
                v___x_1921_ = l_Lean_Environment_header(v_env_1895_);
                leanh::lean_dec_ref(v_env_1895_);
                v___x_1922_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1921_);
                v_mod_1923_ = lean_array_get(v___x_1920_, v___x_1922_, v_val_1916_);
                leanh::lean_dec(v_val_1916_);
                leanh::lean_dec_ref(v___x_1922_);
                v___x_1924_ = l_Lean_isPrivateName(v_declHint_1891_);
                leanh::lean_dec(v_declHint_1891_);
                if v___x_1924_ == 0 {
                    v___x_1925_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                    v___x_1926_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1926_, 0, v___x_1925_);
                    leanh::lean_ctor_set(v___x_1926_, 1, v_c_1907_);
                    v___x_1927_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_1928_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1928_, 0, v___x_1926_);
                    leanh::lean_ctor_set(v___x_1928_, 1, v___x_1927_);
                    v___x_1929_ = l_Lean_MessageData_ofName(v_mod_1923_);
                    v___x_1930_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1930_, 0, v___x_1928_);
                    leanh::lean_ctor_set(v___x_1930_, 1, v___x_1929_);
                    v___x_1931_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                    v___x_1932_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1932_, 0, v___x_1930_);
                    leanh::lean_ctor_set(v___x_1932_, 1, v___x_1931_);
                    v___x_1933_ = l_Lean_MessageData_note(v___x_1932_);
                    v___x_1934_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1934_, 0, v_msg_1890_);
                    leanh::lean_ctor_set(v___x_1934_, 1, v___x_1933_);
                    if v_isShared_1919_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1918_, 0);
                        leanh::lean_ctor_set(v___x_1918_, 0, v___x_1934_);
                        v___x_1936_ = v___x_1918_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1937_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
                        v___x_1936_ = v_reuseFailAlloc_1937_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1938_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                    v___x_1939_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1939_, 0, v___x_1938_);
                    leanh::lean_ctor_set(v___x_1939_, 1, v_c_1907_);
                    v___x_1940_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_1941_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1941_, 0, v___x_1939_);
                    leanh::lean_ctor_set(v___x_1941_, 1, v___x_1940_);
                    v___x_1942_ = l_Lean_MessageData_ofName(v_mod_1923_);
                    v___x_1943_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1943_, 0, v___x_1941_);
                    leanh::lean_ctor_set(v___x_1943_, 1, v___x_1942_);
                    v___x_1944_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_1945_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1945_, 0, v___x_1943_);
                    leanh::lean_ctor_set(v___x_1945_, 1, v___x_1944_);
                    v___x_1946_ = l_Lean_MessageData_note(v___x_1945_);
                    v___x_1947_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1947_, 0, v_msg_1890_);
                    leanh::lean_ctor_set(v___x_1947_, 1, v___x_1946_);
                    if v_isShared_1919_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1918_, 0);
                        leanh::lean_ctor_set(v___x_1918_, 0, v___x_1947_);
                        v___x_1949_ = v___x_1918_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
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
    mut v_msg_1953_: *mut leanh::LeanObject,
    mut v_declHint_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1953_, v_declHint_1954_, v___y_1955_);
    leanh::lean_dec(v___y_1955_);
    return v_res_1957_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_1958_: *mut leanh::LeanObject,
    mut v_declHint_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1963_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1958_, v_declHint_1959_, v___y_1961_);
                v_a_1964_ = leanh::lean_ctor_get(v___x_1963_, 0);
                v_isSharedCheck_1973_ = (!leanh::lean_is_exclusive(v___x_1963_)) as u8;
                if v_isSharedCheck_1973_ == 0 {
                    v___x_1966_ = v___x_1963_;
                    v_isShared_1967_ = v_isSharedCheck_1973_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1964_);
                    leanh::lean_dec(v___x_1963_);
                    v___x_1966_ = leanh::lean_box(0);
                    v_isShared_1967_ = v_isSharedCheck_1973_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1968_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1969_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1969_, 0, v___x_1968_);
                leanh::lean_ctor_set(v___x_1969_, 1, v_a_1964_);
                if v_isShared_1967_ == 0 {
                    leanh::lean_ctor_set(v___x_1966_, 0, v___x_1969_);
                    v___x_1971_ = v___x_1966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
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
    mut v_msg_1974_: *mut leanh::LeanObject,
    mut v_declHint_1975_: *mut leanh::LeanObject,
    mut v___y_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1979_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1974_, v_declHint_1975_, v___y_1976_, v___y_1977_);
    leanh::lean_dec(v___y_1977_);
    leanh::lean_dec_ref(v___y_1976_);
    return v_res_1979_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_1980_: *mut leanh::LeanObject,
    mut v_msg_1981_: *mut leanh::LeanObject,
    mut v_declHint_1982_: *mut leanh::LeanObject,
    mut v___y_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1986_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1981_, v_declHint_1982_, v___y_1983_, v___y_1984_);
    v_a_1987_ = leanh::lean_ctor_get(v___x_1986_, 0);
    leanh::lean_inc(v_a_1987_);
    leanh::lean_dec_ref(v___x_1986_);
    v___x_1988_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1980_, v_a_1987_, v___y_1983_, v___y_1984_);
    return v___x_1988_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_1989_: *mut leanh::LeanObject,
    mut v_msg_1990_: *mut leanh::LeanObject,
    mut v_declHint_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1995_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1989_, v_msg_1990_, v_declHint_1991_, v___y_1992_, v___y_1993_);
    leanh::lean_dec(v___y_1993_);
    leanh::lean_dec_ref(v___y_1992_);
    leanh::lean_dec(v_ref_1989_);
    return v_res_1995_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
    return v___x_1998_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2000_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
    return v___x_2001_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2002_: *mut leanh::LeanObject,
    mut v_constName_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2008_ = 0;
    leanh::lean_inc(v_constName_2003_);
    v___x_2009_ = l_Lean_MessageData_ofConstName(v_constName_2003_, v___x_2008_);
    v___x_2010_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2010_, 0, v___x_2007_);
    leanh::lean_ctor_set(v___x_2010_, 1, v___x_2009_);
    v___x_2011_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2012_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2012_, 0, v___x_2010_);
    leanh::lean_ctor_set(v___x_2012_, 1, v___x_2011_);
    v___x_2013_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2002_, v___x_2012_, v_constName_2003_, v___y_2004_, v___y_2005_);
    return v___x_2013_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2014_: *mut leanh::LeanObject,
    mut v_constName_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2019_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2014_, v_constName_2015_, v___y_2016_, v___y_2017_);
    leanh::lean_dec(v___y_2017_);
    leanh::lean_dec_ref(v___y_2016_);
    leanh::lean_dec(v_ref_2014_);
    return v_res_2019_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg(
    mut v_constName_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
    mut v___y_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2024_ = leanh::lean_ctor_get(v___y_2021_, 5);
    v___x_2025_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2024_, v_constName_2020_, v___y_2021_, v___y_2022_);
    return v___x_2025_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
    mut v___y_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg(v_constName_2026_, v___y_2027_, v___y_2028_);
    leanh::lean_dec(v___y_2028_);
    leanh::lean_dec_ref(v___y_2027_);
    return v_res_2030_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0(
    mut v_constName_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
    mut v___y_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2035_ = lean_st_ref_get(v___y_2033_);
                v_env_2036_ = leanh::lean_ctor_get(v___x_2035_, 0);
                leanh::lean_inc_ref(v_env_2036_);
                leanh::lean_dec(v___x_2035_);
                v___x_2037_ = 0;
                leanh::lean_inc(v_constName_2031_);
                v___x_2038_ =
                    l_Lean_Environment_find_x3f(v_env_2036_, v_constName_2031_, v___x_2037_);
                if leanh::lean_obj_tag(v___x_2038_) == 0 {
                    v___x_2039_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg(v_constName_2031_, v___y_2032_, v___y_2033_);
                    return v___x_2039_;
                } else {
                    leanh::lean_dec(v_constName_2031_);
                    v_val_2040_ = leanh::lean_ctor_get(v___x_2038_, 0);
                    v_isSharedCheck_2047_ = (!leanh::lean_is_exclusive(v___x_2038_)) as u8;
                    if v_isSharedCheck_2047_ == 0 {
                        v___x_2042_ = v___x_2038_;
                        v_isShared_2043_ = v_isSharedCheck_2047_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2040_);
                        leanh::lean_dec(v___x_2038_);
                        v___x_2042_ = leanh::lean_box(0);
                        v_isShared_2043_ = v_isSharedCheck_2047_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2043_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2042_, 0);
                    v___x_2045_ = v___x_2042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2046_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_val_2040_);
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
    mut v_constName_2048_: *mut leanh::LeanObject,
    mut v___y_2049_: *mut leanh::LeanObject,
    mut v___y_2050_: *mut leanh::LeanObject,
    mut v___y_2051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2052_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0(
        v_constName_2048_,
        v___y_2049_,
        v___y_2050_,
    );
    leanh::lean_dec(v___y_2050_);
    leanh::lean_dec_ref(v___y_2049_);
    return v_res_2052_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__2(
    mut v_sz_2053_: usize,
    mut v_i_2054_: usize,
    mut v_bs_2055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2056_: u8 = 0;
    let mut v_v_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: usize = 0;
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2056_ = lean_usize_dec_lt(v_i_2054_, v_sz_2053_);
                if v___x_2056_ == 0 {
                    return v_bs_2055_;
                } else {
                    v_v_2057_ = lean_array_uget(v_bs_2055_, v_i_2054_);
                    v___x_2058_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2059_ = lean_array_uset(v_bs_2055_, v_i_2054_, v___x_2058_);
                    if leanh::lean_obj_tag(v_v_2057_) == 1 {
                        v_fvarId_2066_ = leanh::lean_ctor_get(v_v_2057_, 0);
                        leanh::lean_inc(v_fvarId_2066_);
                        leanh::lean_dec_ref_known(v_v_2057_, 1);
                        v___x_2067_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2067_, 0, v_fvarId_2066_);
                        v___y_2061_ = v___x_2067_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2068_ = l_Lean_Expr_isErased(v_v_2057_);
                        if v___x_2068_ == 0 {
                            v___x_2069_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2069_, 0, v_v_2057_);
                            v___y_2061_ = v___x_2069_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_v_2057_);
                            v___x_2070_ = leanh::lean_box(0);
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
    mut v_sz_2071_: *mut leanh::LeanObject,
    mut v_i_2072_: *mut leanh::LeanObject,
    mut v_bs_2073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2074_: usize = 0;
    let mut v_i_boxed_2075_: usize = 0;
    let mut v_res_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2074_ = leanh::lean_unbox_usize(v_sz_2071_);
    leanh::lean_dec(v_sz_2071_);
    v_i_boxed_2075_ = leanh::lean_unbox_usize(v_i_2072_);
    leanh::lean_dec(v_i_2072_);
    v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__2(v_sz_boxed_2074_, v_i_boxed_2075_, v_bs_2073_);
    return v_res_2076_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1___redArg(
    mut v_a_2077_: *mut leanh::LeanObject,
    mut v_b_2078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v___x_2085_: u8 = 0;
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2079_ = leanh::lean_ctor_get(v_a_2077_, 0);
                v_start_2080_ = leanh::lean_ctor_get(v_a_2077_, 1);
                v_stop_2081_ = leanh::lean_ctor_get(v_a_2077_, 2);
                v_isSharedCheck_2094_ = (!leanh::lean_is_exclusive(v_a_2077_)) as u8;
                if v_isSharedCheck_2094_ == 0 {
                    v___x_2083_ = v_a_2077_;
                    v_isShared_2084_ = v_isSharedCheck_2094_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_2081_);
                    leanh::lean_inc(v_start_2080_);
                    leanh::lean_inc(v_array_2079_);
                    leanh::lean_dec(v_a_2077_);
                    v___x_2083_ = leanh::lean_box(0);
                    v_isShared_2084_ = v_isSharedCheck_2094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2085_ = lean_nat_dec_lt(v_start_2080_, v_stop_2081_);
                if v___x_2085_ == 0 {
                    leanh::lean_del_object(v___x_2083_);
                    leanh::lean_dec(v_stop_2081_);
                    leanh::lean_dec(v_start_2080_);
                    leanh::lean_dec_ref(v_array_2079_);
                    return v_b_2078_;
                } else {
                    v___x_2086_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2087_ = lean_nat_add(v_start_2080_, v___x_2086_);
                    leanh::lean_inc_ref(v_array_2079_);
                    if v_isShared_2084_ == 0 {
                        leanh::lean_ctor_set(v___x_2083_, 1, v___x_2087_);
                        v___x_2089_ = v___x_2083_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2093_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_array_2079_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2087_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_stop_2081_);
                        v___x_2089_ = v_reuseFailAlloc_2093_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2090_ = lean_array_fget(v_array_2079_, v_start_2080_);
                leanh::lean_dec(v_start_2080_);
                leanh::lean_dec_ref(v_array_2079_);
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
-> *mut leanh::LeanObject {
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2095_ = leanh::lean_box(0);
    v_dummy_2096_ = l_Lean_Expr_sort___override(v___x_2095_);
    return v_dummy_2096_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(
    mut v_type_2099_: *mut leanh::LeanObject,
    mut v_ind_2100_: *mut leanh::LeanObject,
    mut v_a_2101_: *mut leanh::LeanObject,
    mut v_a_2102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: u8 = 0;
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v_val_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v_numParams_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2136_: usize = 0;
    let mut v___x_2137_: usize = 0;
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2151_: u8 = 0;
    let mut v_a_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_2104_ = l_Lean_Expr_headBeta(v_type_2099_);
                v___x_2105_ = l_Lean_Expr_getAppFn(v_type_2104_);
                if leanh::lean_obj_tag(v___x_2105_) == 4 {
                    v_declName_2106_ = leanh::lean_ctor_get(v___x_2105_, 0);
                    leanh::lean_inc(v_declName_2106_);
                    v_us_2107_ = leanh::lean_ctor_get(v___x_2105_, 1);
                    leanh::lean_inc(v_us_2107_);
                    leanh::lean_dec_ref_known(v___x_2105_, 2);
                    v___x_2108_ = lean_name_eq(v_declName_2106_, v_ind_2100_);
                    if v___x_2108_ == 0 {
                        leanh::lean_dec(v_us_2107_);
                        leanh::lean_dec(v_declName_2106_);
                        leanh::lean_dec_ref(v_type_2104_);
                        v___x_2109_ = leanh::lean_box(0);
                        v___x_2110_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2110_, 0, v___x_2109_);
                        return v___x_2110_;
                    } else {
                        v___x_2111_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0(v_declName_2106_, v_a_2101_, v_a_2102_);
                        if leanh::lean_obj_tag(v___x_2111_) == 0 {
                            v_a_2112_ = leanh::lean_ctor_get(v___x_2111_, 0);
                            v_isSharedCheck_2151_ =
                                (!leanh::lean_is_exclusive(v___x_2111_)) as u8;
                            if v_isSharedCheck_2151_ == 0 {
                                v___x_2114_ = v___x_2111_;
                                v_isShared_2115_ = v_isSharedCheck_2151_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2112_);
                                leanh::lean_dec(v___x_2111_);
                                v___x_2114_ = leanh::lean_box(0);
                                v_isShared_2115_ = v_isSharedCheck_2151_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_us_2107_);
                            leanh::lean_dec_ref(v_type_2104_);
                            v_a_2152_ = leanh::lean_ctor_get(v___x_2111_, 0);
                            v_isSharedCheck_2159_ =
                                (!leanh::lean_is_exclusive(v___x_2111_)) as u8;
                            if v_isSharedCheck_2159_ == 0 {
                                v___x_2154_ = v___x_2111_;
                                v_isShared_2155_ = v_isSharedCheck_2159_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2152_);
                                leanh::lean_dec(v___x_2111_);
                                v___x_2154_ = leanh::lean_box(0);
                                v_isShared_2155_ = v_isSharedCheck_2159_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2105_);
                    leanh::lean_dec_ref(v_type_2104_);
                    v___x_2160_ = leanh::lean_box(0);
                    v___x_2161_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2161_, 0, v___x_2160_);
                    return v___x_2161_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2112_) == 5 {
                    v_val_2116_ = leanh::lean_ctor_get(v_a_2112_, 0);
                    v_isSharedCheck_2146_ = (!leanh::lean_is_exclusive(v_a_2112_)) as u8;
                    if v_isSharedCheck_2146_ == 0 {
                        v___x_2118_ = v_a_2112_;
                        v_isShared_2119_ = v_isSharedCheck_2146_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2116_);
                        leanh::lean_dec(v_a_2112_);
                        v___x_2118_ = leanh::lean_box(0);
                        v_isShared_2119_ = v_isSharedCheck_2146_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2112_);
                    leanh::lean_dec(v_us_2107_);
                    leanh::lean_dec_ref(v_type_2104_);
                    v___x_2147_ = leanh::lean_box(0);
                    if v_isShared_2115_ == 0 {
                        leanh::lean_ctor_set(v___x_2114_, 0, v___x_2147_);
                        v___x_2149_ = v___x_2114_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2150_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
                        v___x_2149_ = v_reuseFailAlloc_2150_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_numParams_2120_ = leanh::lean_ctor_get(v_val_2116_, 1);
                leanh::lean_inc(v_numParams_2120_);
                leanh::lean_dec_ref(v_val_2116_);
                v___x_2121_ = l_Lean_Expr_getAppNumArgs(v_type_2104_);
                v___x_2122_ = lean_nat_dec_le(v_numParams_2120_, v___x_2121_);
                if v___x_2122_ == 0 {
                    leanh::lean_dec(v___x_2121_);
                    leanh::lean_dec(v_numParams_2120_);
                    leanh::lean_del_object(v___x_2118_);
                    leanh::lean_dec(v_us_2107_);
                    leanh::lean_dec_ref(v_type_2104_);
                    v___x_2123_ = leanh::lean_box(0);
                    if v_isShared_2115_ == 0 {
                        leanh::lean_ctor_set(v___x_2114_, 0, v___x_2123_);
                        v___x_2125_ = v___x_2114_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
                        v___x_2125_ = v_reuseFailAlloc_2126_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_dummy_2127_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__0,
                    );
                    leanh::lean_inc(v___x_2121_);
                    v___x_2128_ = lean_mk_array(v___x_2121_, v_dummy_2127_);
                    v___x_2129_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2130_ = lean_nat_sub(v___x_2121_, v___x_2129_);
                    leanh::lean_dec(v___x_2121_);
                    v___x_2131_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_type_2104_,
                        v___x_2128_,
                        v___x_2130_,
                    );
                    v___x_2132_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2133_ =
                        l_Array_toSubarray___redArg(v___x_2131_, v___x_2132_, v_numParams_2120_);
                    v___x_2134_ = l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___closed__1;
                    v___x_2135_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1___redArg(v___x_2133_, v___x_2134_);
                    v_sz_2136_ = lean_array_size(v___x_2135_);
                    v___x_2137_ = 0usize;
                    v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__2(v_sz_2136_, v___x_2137_, v___x_2135_);
                    v___x_2139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2139_, 0, v_us_2107_);
                    leanh::lean_ctor_set(v___x_2139_, 1, v___x_2138_);
                    if v_isShared_2119_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2118_, 1);
                        leanh::lean_ctor_set(v___x_2118_, 0, v___x_2139_);
                        v___x_2141_ = v___x_2118_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2145_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2139_);
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
                    leanh::lean_ctor_set(v___x_2114_, 0, v___x_2141_);
                    v___x_2143_ = v___x_2114_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
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
                    v_reuseFailAlloc_2158_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
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
    mut v_type_2162_: *mut leanh::LeanObject,
    mut v_ind_2163_: *mut leanh::LeanObject,
    mut v_a_2164_: *mut leanh::LeanObject,
    mut v_a_2165_: *mut leanh::LeanObject,
    mut v_a_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ =
        l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(v_type_2162_, v_ind_2163_, v_a_2164_, v_a_2165_);
    leanh::lean_dec(v_a_2165_);
    leanh::lean_dec_ref(v_a_2164_);
    leanh::lean_dec(v_ind_2163_);
    return v_res_2167_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1(
    mut v_inst_2168_: *mut leanh::LeanObject,
    mut v_R_2169_: *mut leanh::LeanObject,
    mut v_a_2170_: *mut leanh::LeanObject,
    mut v_b_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1___redArg(v_a_2170_, v_b_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0(
    mut v_00_u03b1_2173_: *mut leanh::LeanObject,
    mut v_constName_2174_: *mut leanh::LeanObject,
    mut v___y_2175_: *mut leanh::LeanObject,
    mut v___y_2176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___redArg(v_constName_2174_, v___y_2175_, v___y_2176_);
    return v___x_2178_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_2179_: *mut leanh::LeanObject,
    mut v_constName_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
    mut v___y_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0(v_00_u03b1_2179_, v_constName_2180_, v___y_2181_, v___y_2182_);
    leanh::lean_dec(v___y_2182_);
    leanh::lean_dec_ref(v___y_2181_);
    return v_res_2184_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2185_: *mut leanh::LeanObject,
    mut v_ref_2186_: *mut leanh::LeanObject,
    mut v_constName_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
    mut v___y_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2186_, v_constName_2187_, v___y_2188_, v___y_2189_);
    return v___x_2191_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2192_: *mut leanh::LeanObject,
    mut v_ref_2193_: *mut leanh::LeanObject,
    mut v_constName_2194_: *mut leanh::LeanObject,
    mut v___y_2195_: *mut leanh::LeanObject,
    mut v___y_2196_: *mut leanh::LeanObject,
    mut v___y_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2192_, v_ref_2193_, v_constName_2194_, v___y_2195_, v___y_2196_);
    leanh::lean_dec(v___y_2196_);
    leanh::lean_dec_ref(v___y_2195_);
    leanh::lean_dec(v_ref_2193_);
    return v_res_2198_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_2199_: *mut leanh::LeanObject,
    mut v_ref_2200_: *mut leanh::LeanObject,
    mut v_msg_2201_: *mut leanh::LeanObject,
    mut v_declHint_2202_: *mut leanh::LeanObject,
    mut v___y_2203_: *mut leanh::LeanObject,
    mut v___y_2204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2206_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2200_, v_msg_2201_, v_declHint_2202_, v___y_2203_, v___y_2204_);
    return v___x_2206_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_2207_: *mut leanh::LeanObject,
    mut v_ref_2208_: *mut leanh::LeanObject,
    mut v_msg_2209_: *mut leanh::LeanObject,
    mut v_declHint_2210_: *mut leanh::LeanObject,
    mut v___y_2211_: *mut leanh::LeanObject,
    mut v___y_2212_: *mut leanh::LeanObject,
    mut v___y_2213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2214_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2207_, v_ref_2208_, v_msg_2209_, v_declHint_2210_, v___y_2211_, v___y_2212_);
    leanh::lean_dec(v___y_2212_);
    leanh::lean_dec_ref(v___y_2211_);
    leanh::lean_dec(v_ref_2208_);
    return v_res_2214_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_2215_: *mut leanh::LeanObject,
    mut v_declHint_2216_: *mut leanh::LeanObject,
    mut v___y_2217_: *mut leanh::LeanObject,
    mut v___y_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2215_, v_declHint_2216_, v___y_2218_);
    return v___x_2220_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_2221_: *mut leanh::LeanObject,
    mut v_declHint_2222_: *mut leanh::LeanObject,
    mut v___y_2223_: *mut leanh::LeanObject,
    mut v___y_2224_: *mut leanh::LeanObject,
    mut v___y_2225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2226_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2221_, v_declHint_2222_, v___y_2223_, v___y_2224_);
    leanh::lean_dec(v___y_2224_);
    leanh::lean_dec_ref(v___y_2223_);
    return v_res_2226_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_2227_: *mut leanh::LeanObject,
    mut v_ref_2228_: *mut leanh::LeanObject,
    mut v_msg_2229_: *mut leanh::LeanObject,
    mut v___y_2230_: *mut leanh::LeanObject,
    mut v___y_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2233_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2228_, v_msg_2229_, v___y_2230_, v___y_2231_);
    return v___x_2233_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_2234_: *mut leanh::LeanObject,
    mut v_ref_2235_: *mut leanh::LeanObject,
    mut v_msg_2236_: *mut leanh::LeanObject,
    mut v___y_2237_: *mut leanh::LeanObject,
    mut v___y_2238_: *mut leanh::LeanObject,
    mut v___y_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2234_, v_ref_2235_, v_msg_2236_, v___y_2237_, v___y_2238_);
    leanh::lean_dec(v___y_2238_);
    leanh::lean_dec_ref(v___y_2237_);
    leanh::lean_dec(v_ref_2235_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(
    mut v_00_u03b1_2241_: *mut leanh::LeanObject,
    mut v_msg_2242_: *mut leanh::LeanObject,
    mut v___y_2243_: *mut leanh::LeanObject,
    mut v___y_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2246_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2242_, v___y_2243_, v___y_2244_);
    return v___x_2246_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_2247_: *mut leanh::LeanObject,
    mut v_msg_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2247_, v_msg_2248_, v___y_2249_, v___y_2250_);
    leanh::lean_dec(v___y_2250_);
    leanh::lean_dec_ref(v___y_2249_);
    return v_res_2252_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_x_2253_: *mut leanh::LeanObject,
    mut v_x_2254_: *mut leanh::LeanObject,
    mut v_x_2255_: *mut leanh::LeanObject,
    mut v_x_2256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2261_: u8 = 0;
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2257_ = leanh::lean_ctor_get(v_x_2253_, 0);
                v_vs_2258_ = leanh::lean_ctor_get(v_x_2253_, 1);
                v_isSharedCheck_2282_ = (!leanh::lean_is_exclusive(v_x_2253_)) as u8;
                if v_isSharedCheck_2282_ == 0 {
                    v___x_2260_ = v_x_2253_;
                    v_isShared_2261_ = v_isSharedCheck_2282_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2258_);
                    leanh::lean_inc(v_ks_2257_);
                    leanh::lean_dec(v_x_2253_);
                    v___x_2260_ = leanh::lean_box(0);
                    v_isShared_2261_ = v_isSharedCheck_2282_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2262_ = lean_array_get_size(v_ks_2257_);
                v___x_2263_ = lean_nat_dec_lt(v_x_2254_, v___x_2262_);
                if v___x_2263_ == 0 {
                    leanh::lean_dec(v_x_2254_);
                    v___x_2264_ = lean_array_push(v_ks_2257_, v_x_2255_);
                    v___x_2265_ = lean_array_push(v_vs_2258_, v_x_2256_);
                    if v_isShared_2261_ == 0 {
                        leanh::lean_ctor_set(v___x_2260_, 1, v___x_2265_);
                        leanh::lean_ctor_set(v___x_2260_, 0, v___x_2264_);
                        v___x_2267_ = v___x_2260_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2268_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2264_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2265_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_ks_2257_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_vs_2258_);
                            v___x_2272_ = v_reuseFailAlloc_2276_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2277_ = lean_array_fset(v_ks_2257_, v_x_2254_, v_x_2255_);
                        v___x_2278_ = lean_array_fset(v_vs_2258_, v_x_2254_, v_x_2256_);
                        leanh::lean_dec(v_x_2254_);
                        if v_isShared_2261_ == 0 {
                            leanh::lean_ctor_set(v___x_2260_, 1, v___x_2278_);
                            leanh::lean_ctor_set(v___x_2260_, 0, v___x_2277_);
                            v___x_2280_ = v___x_2260_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2281_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2277_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2278_);
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
                v___x_2273_ = leanh::lean_unsigned_to_nat(1);
                v___x_2274_ = lean_nat_add(v_x_2254_, v___x_2273_);
                leanh::lean_dec(v_x_2254_);
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
    mut v_n_2283_: *mut leanh::LeanObject,
    mut v_k_2284_: *mut leanh::LeanObject,
    mut v_v_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_2292_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__0);
    v___x_2293_ = lean_usize_sub(v___x_2292_, v___x_2291_);
    return v___x_2293_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2294_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(
    mut v_x_2295_: *mut leanh::LeanObject,
    mut v_x_2296_: usize,
    mut v_x_2297_: usize,
    mut v_x_2298_: *mut leanh::LeanObject,
    mut v_x_2299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: usize = 0;
    let mut v___x_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: usize = 0;
    let mut v_j_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2310_: u8 = 0;
    let mut v_v_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_node_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2342_: u8 = 0;
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut v_unused_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2350_: u8 = 0;
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2355_: u8 = 0;
    let mut v_ks_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v_reuseFailAlloc_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2295_) == 0 {
                    v_es_2300_ = leanh::lean_ctor_get(v_x_2295_, 0);
                    v___x_2301_ = 5usize;
                    v___x_2302_ = 1usize;
                    v___x_2303_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1);
                    v___x_2304_ = lean_usize_land(v_x_2296_, v___x_2303_);
                    v_j_2305_ = lean_usize_to_nat(v___x_2304_);
                    v___x_2306_ = lean_array_get_size(v_es_2300_);
                    v___x_2307_ = lean_nat_dec_lt(v_j_2305_, v___x_2306_);
                    if v___x_2307_ == 0 {
                        leanh::lean_dec(v_j_2305_);
                        leanh::lean_dec(v_x_2299_);
                        leanh::lean_dec_ref(v_x_2298_);
                        return v_x_2295_;
                    } else {
                        leanh::lean_inc_ref(v_es_2300_);
                        v_isSharedCheck_2344_ = (!leanh::lean_is_exclusive(v_x_2295_)) as u8;
                        if v_isSharedCheck_2344_ == 0 {
                            v_unused_2345_ = leanh::lean_ctor_get(v_x_2295_, 0);
                            leanh::lean_dec(v_unused_2345_);
                            v___x_2309_ = v_x_2295_;
                            v_isShared_2310_ = v_isSharedCheck_2344_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2295_);
                            v___x_2309_ = leanh::lean_box(0);
                            v_isShared_2310_ = v_isSharedCheck_2344_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2346_ = leanh::lean_ctor_get(v_x_2295_, 0);
                    v_vs_2347_ = leanh::lean_ctor_get(v_x_2295_, 1);
                    v_isSharedCheck_2367_ = (!leanh::lean_is_exclusive(v_x_2295_)) as u8;
                    if v_isSharedCheck_2367_ == 0 {
                        v___x_2349_ = v_x_2295_;
                        v_isShared_2350_ = v_isSharedCheck_2367_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2347_);
                        leanh::lean_inc(v_ks_2346_);
                        leanh::lean_dec(v_x_2295_);
                        v___x_2349_ = leanh::lean_box(0);
                        v_isShared_2350_ = v_isSharedCheck_2367_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2311_ = lean_array_fget(v_es_2300_, v_j_2305_);
                v___x_2312_ = leanh::lean_box(0);
                v_xs_x27_2313_ = lean_array_fset(v_es_2300_, v_j_2305_, v___x_2312_);
                match leanh::lean_obj_tag(v_v_2311_) {
                    0 => {
                        v_key_2320_ = leanh::lean_ctor_get(v_v_2311_, 0);
                        v_val_2321_ = leanh::lean_ctor_get(v_v_2311_, 1);
                        v_isSharedCheck_2331_ = (!leanh::lean_is_exclusive(v_v_2311_)) as u8;
                        if v_isSharedCheck_2331_ == 0 {
                            v___x_2323_ = v_v_2311_;
                            v_isShared_2324_ = v_isSharedCheck_2331_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2321_);
                            leanh::lean_inc(v_key_2320_);
                            leanh::lean_dec(v_v_2311_);
                            v___x_2323_ = leanh::lean_box(0);
                            v_isShared_2324_ = v_isSharedCheck_2331_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2332_ = leanh::lean_ctor_get(v_v_2311_, 0);
                        v_isSharedCheck_2342_ = (!leanh::lean_is_exclusive(v_v_2311_)) as u8;
                        if v_isSharedCheck_2342_ == 0 {
                            v___x_2334_ = v_v_2311_;
                            v_isShared_2335_ = v_isSharedCheck_2342_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2332_);
                            leanh::lean_dec(v_v_2311_);
                            v___x_2334_ = leanh::lean_box(0);
                            v_isShared_2335_ = v_isSharedCheck_2342_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2343_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2343_, 0, v_x_2298_);
                        leanh::lean_ctor_set(v___x_2343_, 1, v_x_2299_);
                        v___y_2315_ = v___x_2343_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2316_ = lean_array_fset(v_xs_x27_2313_, v_j_2305_, v___y_2315_);
                leanh::lean_dec(v_j_2305_);
                if v_isShared_2310_ == 0 {
                    leanh::lean_ctor_set(v___x_2309_, 0, v___x_2316_);
                    v___x_2318_ = v___x_2309_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
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
                    leanh::lean_del_object(v___x_2323_);
                    v___x_2326_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2320_,
                        v_val_2321_,
                        v_x_2298_,
                        v_x_2299_,
                    );
                    v___x_2327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2327_, 0, v___x_2326_);
                    v___y_2315_ = v___x_2327_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2321_);
                    leanh::lean_dec(v_key_2320_);
                    if v_isShared_2324_ == 0 {
                        leanh::lean_ctor_set(v___x_2323_, 1, v_x_2299_);
                        leanh::lean_ctor_set(v___x_2323_, 0, v_x_2298_);
                        v___x_2329_ = v___x_2323_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2330_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_x_2298_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_x_2299_);
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
                    leanh::lean_ctor_set(v___x_2334_, 0, v___x_2338_);
                    v___x_2340_ = v___x_2334_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2341_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
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
                    v_reuseFailAlloc_2366_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_ks_2346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_vs_2347_);
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
                    v___x_2364_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2365_ = lean_nat_dec_lt(v___x_2363_, v___x_2364_);
                    leanh::lean_dec(v___x_2363_);
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
                    v_ks_2356_ = leanh::lean_ctor_get(v_newNode_2353_, 0);
                    leanh::lean_inc_ref(v_ks_2356_);
                    v_vs_2357_ = leanh::lean_ctor_get(v_newNode_2353_, 1);
                    leanh::lean_inc_ref(v_vs_2357_);
                    leanh::lean_dec_ref(v_newNode_2353_);
                    v___x_2358_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2359_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__2);
                    v___x_2360_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___redArg(v_x_2297_, v_ks_2356_, v_vs_2357_, v___x_2358_, v___x_2359_);
                    leanh::lean_dec_ref(v_vs_2357_);
                    leanh::lean_dec_ref(v_ks_2356_);
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
    mut v_keys_2369_: *mut leanh::LeanObject,
    mut v_vals_2370_: *mut leanh::LeanObject,
    mut v_i_2371_: *mut leanh::LeanObject,
    mut v_entries_2372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    let mut v_k_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u64 = 0;
    let mut v_h_2378_: usize = 0;
    let mut v___x_2379_: usize = 0;
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: usize = 0;
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: usize = 0;
    let mut v_h_2384_: usize = 0;
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2373_ = lean_array_get_size(v_keys_2369_);
                v___x_2374_ = lean_nat_dec_lt(v_i_2371_, v___x_2373_);
                if v___x_2374_ == 0 {
                    leanh::lean_dec(v_i_2371_);
                    return v_entries_2372_;
                } else {
                    v_k_2375_ = lean_array_fget_borrowed(v_keys_2369_, v_i_2371_);
                    v_v_2376_ = lean_array_fget_borrowed(v_vals_2370_, v_i_2371_);
                    v___x_2377_ = l_Lean_Expr_hash(v_k_2375_);
                    v_h_2378_ = lean_uint64_to_usize(v___x_2377_);
                    v___x_2379_ = 5usize;
                    v___x_2380_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2381_ = 1usize;
                    v___x_2382_ = lean_usize_sub(v_depth_2368_, v___x_2381_);
                    v___x_2383_ = lean_usize_mul(v___x_2379_, v___x_2382_);
                    v_h_2384_ = lean_usize_shift_right(v_h_2378_, v___x_2383_);
                    v___x_2385_ = lean_nat_add(v_i_2371_, v___x_2380_);
                    leanh::lean_dec(v_i_2371_);
                    leanh::lean_inc(v_v_2376_);
                    leanh::lean_inc(v_k_2375_);
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
    mut v_depth_2388_: *mut leanh::LeanObject,
    mut v_keys_2389_: *mut leanh::LeanObject,
    mut v_vals_2390_: *mut leanh::LeanObject,
    mut v_i_2391_: *mut leanh::LeanObject,
    mut v_entries_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2393_: usize = 0;
    let mut v_res_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2393_ = leanh::lean_unbox_usize(v_depth_2388_);
    leanh::lean_dec(v_depth_2388_);
    v_res_2394_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___redArg(v_depth_boxed_2393_, v_keys_2389_, v_vals_2390_, v_i_2391_, v_entries_2392_);
    leanh::lean_dec_ref(v_vals_2390_);
    leanh::lean_dec_ref(v_keys_2389_);
    return v_res_2394_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___boxed(
    mut v_x_2395_: *mut leanh::LeanObject,
    mut v_x_2396_: *mut leanh::LeanObject,
    mut v_x_2397_: *mut leanh::LeanObject,
    mut v_x_2398_: *mut leanh::LeanObject,
    mut v_x_2399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4558__boxed_2400_: usize = 0;
    let mut v_x_4559__boxed_2401_: usize = 0;
    let mut v_res_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4558__boxed_2400_ = leanh::lean_unbox_usize(v_x_2396_);
    leanh::lean_dec(v_x_2396_);
    v_x_4559__boxed_2401_ = leanh::lean_unbox_usize(v_x_2397_);
    leanh::lean_dec(v_x_2397_);
    v_res_2402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(v_x_2395_, v_x_4558__boxed_2400_, v_x_4559__boxed_2401_, v_x_2398_, v_x_2399_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2___redArg(
    mut v_x_2403_: *mut leanh::LeanObject,
    mut v_x_2404_: *mut leanh::LeanObject,
    mut v_x_2405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2406_: u64 = 0;
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: usize = 0;
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_Expr_hash(v_x_2404_);
    v___x_2407_ = lean_uint64_to_usize(v___x_2406_);
    v___x_2408_ = 1usize;
    v___x_2409_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(v_x_2403_, v___x_2407_, v___x_2408_, v_x_2404_, v_x_2405_);
    return v___x_2409_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg(
    mut v_msg_2410_: *mut leanh::LeanObject,
    mut v___y_2411_: *mut leanh::LeanObject,
    mut v___y_2412_: *mut leanh::LeanObject,
    mut v___y_2413_: *mut leanh::LeanObject,
    mut v___y_2414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2424_: u8 = 0;
    let mut v_env_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2429_: u8 = 0;
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut v_unused_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2443_: u8 = 0;
    let mut v_a_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2447_: u8 = 0;
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2416_ = leanh::lean_ctor_get(v___y_2413_, 2);
                v_ref_2417_ = leanh::lean_ctor_get(v___y_2413_, 5);
                v___x_2418_ = lean_st_ref_get(v___y_2414_);
                v___x_2419_ = lean_st_ref_get(v___y_2412_);
                v___x_2420_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2411_);
                if leanh::lean_obj_tag(v___x_2420_) == 0 {
                    v_a_2421_ = leanh::lean_ctor_get(v___x_2420_, 0);
                    v_isSharedCheck_2443_ = (!leanh::lean_is_exclusive(v___x_2420_)) as u8;
                    if v_isSharedCheck_2443_ == 0 {
                        v___x_2423_ = v___x_2420_;
                        v_isShared_2424_ = v_isSharedCheck_2443_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2421_);
                        leanh::lean_dec(v___x_2420_);
                        v___x_2423_ = leanh::lean_box(0);
                        v_isShared_2424_ = v_isSharedCheck_2443_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2419_);
                    leanh::lean_dec(v___x_2418_);
                    leanh::lean_dec_ref(v_msg_2410_);
                    v_a_2444_ = leanh::lean_ctor_get(v___x_2420_, 0);
                    v_isSharedCheck_2451_ = (!leanh::lean_is_exclusive(v___x_2420_)) as u8;
                    if v_isSharedCheck_2451_ == 0 {
                        v___x_2446_ = v___x_2420_;
                        v_isShared_2447_ = v_isSharedCheck_2451_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2444_);
                        leanh::lean_dec(v___x_2420_);
                        v___x_2446_ = leanh::lean_box(0);
                        v_isShared_2447_ = v_isSharedCheck_2451_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_2425_ = leanh::lean_ctor_get(v___x_2418_, 0);
                leanh::lean_inc_ref(v_env_2425_);
                leanh::lean_dec(v___x_2418_);
                v_lctx_2426_ = leanh::lean_ctor_get(v___x_2419_, 0);
                v_isSharedCheck_2441_ = (!leanh::lean_is_exclusive(v___x_2419_)) as u8;
                if v_isSharedCheck_2441_ == 0 {
                    v_unused_2442_ = leanh::lean_ctor_get(v___x_2419_, 1);
                    leanh::lean_dec(v_unused_2442_);
                    v___x_2428_ = v___x_2419_;
                    v_isShared_2429_ = v_isSharedCheck_2441_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lctx_2426_);
                    leanh::lean_dec(v___x_2419_);
                    v___x_2428_ = leanh::lean_box(0);
                    v_isShared_2429_ = v_isSharedCheck_2441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2430_ = (leanh::lean_unbox(v_a_2421_) as u8);
                leanh::lean_dec(v_a_2421_);
                v___x_2431_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2426_, v___x_2430_);
                leanh::lean_dec_ref(v_lctx_2426_);
                v___x_2432_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2);
                leanh::lean_inc_ref(v_options_2416_);
                v___x_2433_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2433_, 0, v_env_2425_);
                leanh::lean_ctor_set(v___x_2433_, 1, v___x_2432_);
                leanh::lean_ctor_set(v___x_2433_, 2, v___x_2431_);
                leanh::lean_ctor_set(v___x_2433_, 3, v_options_2416_);
                if v_isShared_2429_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2428_, 3);
                    leanh::lean_ctor_set(v___x_2428_, 1, v_msg_2410_);
                    leanh::lean_ctor_set(v___x_2428_, 0, v___x_2433_);
                    v___x_2435_ = v___x_2428_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2440_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_msg_2410_);
                    v___x_2435_ = v_reuseFailAlloc_2440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_ref_2417_);
                v___x_2436_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2436_, 0, v_ref_2417_);
                leanh::lean_ctor_set(v___x_2436_, 1, v___x_2435_);
                if v_isShared_2424_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2423_, 1);
                    leanh::lean_ctor_set(v___x_2423_, 0, v___x_2436_);
                    v___x_2438_ = v___x_2423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2439_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
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
                    v_reuseFailAlloc_2450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
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
    mut v_msg_2452_: *mut leanh::LeanObject,
    mut v___y_2453_: *mut leanh::LeanObject,
    mut v___y_2454_: *mut leanh::LeanObject,
    mut v___y_2455_: *mut leanh::LeanObject,
    mut v___y_2456_: *mut leanh::LeanObject,
    mut v___y_2457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2458_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg(v_msg_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
    leanh::lean_dec(v___y_2456_);
    leanh::lean_dec_ref(v___y_2455_);
    leanh::lean_dec(v___y_2454_);
    leanh::lean_dec_ref(v___y_2453_);
    return v_res_2458_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2459_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2459_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1(
    mut v_msg_2464_: *mut leanh::LeanObject,
    mut v___y_2465_: *mut leanh::LeanObject,
    mut v___y_2466_: *mut leanh::LeanObject,
    mut v___y_2467_: *mut leanh::LeanObject,
    mut v___y_2468_: *mut leanh::LeanObject,
    mut v___y_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v_toFunctor_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___f_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v_toFunctor_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___f_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189__overap_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2527_: u8 = 0;
    let mut v_unused_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_unused_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_unused_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v_unused_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2471_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__0);
                v___x_2472_ = l_StateRefT_x27_instMonad___redArg(v___x_2471_);
                v_toApplicative_2473_ = leanh::lean_ctor_get(v___x_2472_, 0);
                v_isSharedCheck_2535_ = (!leanh::lean_is_exclusive(v___x_2472_)) as u8;
                if v_isSharedCheck_2535_ == 0 {
                    v_unused_2536_ = leanh::lean_ctor_get(v___x_2472_, 1);
                    leanh::lean_dec(v_unused_2536_);
                    v___x_2475_ = v___x_2472_;
                    v_isShared_2476_ = v_isSharedCheck_2535_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2473_);
                    leanh::lean_dec(v___x_2472_);
                    v___x_2475_ = leanh::lean_box(0);
                    v_isShared_2476_ = v_isSharedCheck_2535_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2477_ = leanh::lean_ctor_get(v_toApplicative_2473_, 0);
                v_toSeq_2478_ = leanh::lean_ctor_get(v_toApplicative_2473_, 2);
                v_toSeqLeft_2479_ = leanh::lean_ctor_get(v_toApplicative_2473_, 3);
                v_toSeqRight_2480_ = leanh::lean_ctor_get(v_toApplicative_2473_, 4);
                v_isSharedCheck_2533_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2473_)) as u8;
                if v_isSharedCheck_2533_ == 0 {
                    v_unused_2534_ = leanh::lean_ctor_get(v_toApplicative_2473_, 1);
                    leanh::lean_dec(v_unused_2534_);
                    v___x_2482_ = v_toApplicative_2473_;
                    v_isShared_2483_ = v_isSharedCheck_2533_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2480_);
                    leanh::lean_inc(v_toSeqLeft_2479_);
                    leanh::lean_inc(v_toSeq_2478_);
                    leanh::lean_inc(v_toFunctor_2477_);
                    leanh::lean_dec(v_toApplicative_2473_);
                    v___x_2482_ = leanh::lean_box(0);
                    v_isShared_2483_ = v_isSharedCheck_2533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2484_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__1;
                v___f_2485_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__2;
                leanh::lean_inc_ref(v_toFunctor_2477_);
                v___f_2486_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2486_, 0, v_toFunctor_2477_);
                v___f_2487_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2487_, 0, v_toFunctor_2477_);
                v___x_2488_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2488_, 0, v___f_2486_);
                leanh::lean_ctor_set(v___x_2488_, 1, v___f_2487_);
                v___f_2489_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2489_, 0, v_toSeqRight_2480_);
                v___f_2490_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2490_, 0, v_toSeqLeft_2479_);
                v___f_2491_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2491_, 0, v_toSeq_2478_);
                if v_isShared_2483_ == 0 {
                    leanh::lean_ctor_set(v___x_2482_, 4, v___f_2489_);
                    leanh::lean_ctor_set(v___x_2482_, 3, v___f_2490_);
                    leanh::lean_ctor_set(v___x_2482_, 2, v___f_2491_);
                    leanh::lean_ctor_set(v___x_2482_, 1, v___f_2484_);
                    leanh::lean_ctor_set(v___x_2482_, 0, v___x_2488_);
                    v___x_2493_ = v___x_2482_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___f_2484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 2, v___f_2491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 3, v___f_2490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 4, v___f_2489_);
                    v___x_2493_ = v_reuseFailAlloc_2532_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2476_ == 0 {
                    leanh::lean_ctor_set(v___x_2475_, 1, v___f_2485_);
                    leanh::lean_ctor_set(v___x_2475_, 0, v___x_2493_);
                    v___x_2495_ = v___x_2475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___f_2485_);
                    v___x_2495_ = v_reuseFailAlloc_2531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2496_ = l_StateRefT_x27_instMonad___redArg(v___x_2495_);
                v_toApplicative_2497_ = leanh::lean_ctor_get(v___x_2496_, 0);
                v_isSharedCheck_2529_ = (!leanh::lean_is_exclusive(v___x_2496_)) as u8;
                if v_isSharedCheck_2529_ == 0 {
                    v_unused_2530_ = leanh::lean_ctor_get(v___x_2496_, 1);
                    leanh::lean_dec(v_unused_2530_);
                    v___x_2499_ = v___x_2496_;
                    v_isShared_2500_ = v_isSharedCheck_2529_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2497_);
                    leanh::lean_dec(v___x_2496_);
                    v___x_2499_ = leanh::lean_box(0);
                    v_isShared_2500_ = v_isSharedCheck_2529_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2501_ = leanh::lean_ctor_get(v_toApplicative_2497_, 0);
                v_toSeq_2502_ = leanh::lean_ctor_get(v_toApplicative_2497_, 2);
                v_toSeqLeft_2503_ = leanh::lean_ctor_get(v_toApplicative_2497_, 3);
                v_toSeqRight_2504_ = leanh::lean_ctor_get(v_toApplicative_2497_, 4);
                v_isSharedCheck_2527_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2497_)) as u8;
                if v_isSharedCheck_2527_ == 0 {
                    v_unused_2528_ = leanh::lean_ctor_get(v_toApplicative_2497_, 1);
                    leanh::lean_dec(v_unused_2528_);
                    v___x_2506_ = v_toApplicative_2497_;
                    v_isShared_2507_ = v_isSharedCheck_2527_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2504_);
                    leanh::lean_inc(v_toSeqLeft_2503_);
                    leanh::lean_inc(v_toSeq_2502_);
                    leanh::lean_inc(v_toFunctor_2501_);
                    leanh::lean_dec(v_toApplicative_2497_);
                    v___x_2506_ = leanh::lean_box(0);
                    v_isShared_2507_ = v_isSharedCheck_2527_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2508_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__3;
                v___f_2509_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___closed__4;
                leanh::lean_inc_ref(v_toFunctor_2501_);
                v___f_2510_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2510_, 0, v_toFunctor_2501_);
                v___f_2511_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2511_, 0, v_toFunctor_2501_);
                v___x_2512_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2512_, 0, v___f_2510_);
                leanh::lean_ctor_set(v___x_2512_, 1, v___f_2511_);
                v___f_2513_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2513_, 0, v_toSeqRight_2504_);
                v___f_2514_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2514_, 0, v_toSeqLeft_2503_);
                v___f_2515_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2515_, 0, v_toSeq_2502_);
                if v_isShared_2507_ == 0 {
                    leanh::lean_ctor_set(v___x_2506_, 4, v___f_2513_);
                    leanh::lean_ctor_set(v___x_2506_, 3, v___f_2514_);
                    leanh::lean_ctor_set(v___x_2506_, 2, v___f_2515_);
                    leanh::lean_ctor_set(v___x_2506_, 1, v___f_2508_);
                    leanh::lean_ctor_set(v___x_2506_, 0, v___x_2512_);
                    v___x_2517_ = v___x_2506_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2526_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 1, v___f_2508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 2, v___f_2515_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 3, v___f_2514_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2526_, 4, v___f_2513_);
                    v___x_2517_ = v_reuseFailAlloc_2526_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2500_ == 0 {
                    leanh::lean_ctor_set(v___x_2499_, 1, v___f_2509_);
                    leanh::lean_ctor_set(v___x_2499_, 0, v___x_2517_);
                    v___x_2519_ = v___x_2499_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2517_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___f_2509_);
                    v___x_2519_ = v_reuseFailAlloc_2525_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2520_ = l_ReaderT_instMonad___redArg(v___x_2519_);
                v___x_2521_ = leanh::lean_box(0);
                v___x_2522_ = l_instInhabitedOfMonad___redArg(v___x_2520_, v___x_2521_);
                v___x_4189__overap_2523_ = lean_panic_fn_borrowed(v___x_2522_, v_msg_2464_);
                leanh::lean_dec(v___x_2522_);
                leanh::lean_inc(v___y_2469_);
                leanh::lean_inc_ref(v___y_2468_);
                leanh::lean_inc(v___y_2467_);
                leanh::lean_inc_ref(v___y_2466_);
                leanh::lean_inc_ref(v___y_2465_);
                v___x_2524_ = leanh::lean_apply_6(
                    v___x_4189__overap_2523_,
                    v___y_2465_,
                    v___y_2466_,
                    v___y_2467_,
                    v___y_2468_,
                    v___y_2469_,
                    leanh::lean_box(0),
                );
                return v___x_2524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1___boxed(
    mut v_msg_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
    mut v___y_2539_: *mut leanh::LeanObject,
    mut v___y_2540_: *mut leanh::LeanObject,
    mut v___y_2541_: *mut leanh::LeanObject,
    mut v___y_2542_: *mut leanh::LeanObject,
    mut v___y_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1(v_msg_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
    leanh::lean_dec(v___y_2542_);
    leanh::lean_dec_ref(v___y_2541_);
    leanh::lean_dec(v___y_2540_);
    leanh::lean_dec_ref(v___y_2539_);
    leanh::lean_dec_ref(v___y_2538_);
    return v_res_2544_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__0;
    v___x_2547_ = l_Lean_stringToMessageData(v___x_2546_);
    return v___x_2547_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2551_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__4;
    v___x_2552_ = leanh::lean_unsigned_to_nat(11);
    v___x_2553_ = leanh::lean_unsigned_to_nat(122);
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
    mut v_constName_2557_: *mut leanh::LeanObject,
    mut v___y_2558_: *mut leanh::LeanObject,
    mut v___y_2559_: *mut leanh::LeanObject,
    mut v___y_2560_: *mut leanh::LeanObject,
    mut v___y_2561_: *mut leanh::LeanObject,
    mut v___y_2562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: u8 = 0;
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2577_: u8 = 0;
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2582_: u8 = 0;
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2592_: u8 = 0;
    let mut v_val_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2597_: u8 = 0;
    let mut v_a_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2572_ = lean_st_ref_get(v___y_2562_);
                v_env_2573_ = leanh::lean_ctor_get(v___x_2572_, 0);
                leanh::lean_inc_ref(v_env_2573_);
                leanh::lean_dec(v___x_2572_);
                v___x_2574_ = 0;
                leanh::lean_inc(v_constName_2557_);
                v___x_2575_ =
                    l_Lean_Environment_findAsync_x3f(v_env_2573_, v_constName_2557_, v___x_2574_);
                if leanh::lean_obj_tag(v___x_2575_) == 1 {
                    v_val_2576_ = leanh::lean_ctor_get(v___x_2575_, 0);
                    leanh::lean_inc(v_val_2576_);
                    leanh::lean_dec_ref_known(v___x_2575_, 1);
                    v_kind_2577_ = leanh::lean_ctor_get_uint8(
                        v_val_2576_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_2577_ == 6 {
                        v___x_2578_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2576_);
                        if leanh::lean_obj_tag(v___x_2578_) == 6 {
                            leanh::lean_dec(v_constName_2557_);
                            v_val_2579_ = leanh::lean_ctor_get(v___x_2578_, 0);
                            v_isSharedCheck_2586_ =
                                (!leanh::lean_is_exclusive(v___x_2578_)) as u8;
                            if v_isSharedCheck_2586_ == 0 {
                                v___x_2581_ = v___x_2578_;
                                v_isShared_2582_ = v_isSharedCheck_2586_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2579_);
                                leanh::lean_dec(v___x_2578_);
                                v___x_2581_ = leanh::lean_box(0);
                                v_isShared_2582_ = v_isSharedCheck_2586_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2578_);
                            v___x_2587_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__5);
                            v___x_2588_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__1(v___x_2587_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
                            if leanh::lean_obj_tag(v___x_2588_) == 0 {
                                v_a_2589_ = leanh::lean_ctor_get(v___x_2588_, 0);
                                v_isSharedCheck_2597_ =
                                    (!leanh::lean_is_exclusive(v___x_2588_)) as u8;
                                if v_isSharedCheck_2597_ == 0 {
                                    v___x_2591_ = v___x_2588_;
                                    v_isShared_2592_ = v_isSharedCheck_2597_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2589_);
                                    leanh::lean_dec(v___x_2588_);
                                    v___x_2591_ = leanh::lean_box(0);
                                    v_isShared_2592_ = v_isSharedCheck_2597_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_constName_2557_);
                                v_a_2598_ = leanh::lean_ctor_get(v___x_2588_, 0);
                                v_isSharedCheck_2605_ =
                                    (!leanh::lean_is_exclusive(v___x_2588_)) as u8;
                                if v_isSharedCheck_2605_ == 0 {
                                    v___x_2600_ = v___x_2588_;
                                    v_isShared_2601_ = v_isSharedCheck_2605_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2598_);
                                    leanh::lean_dec(v___x_2588_);
                                    v___x_2600_ = leanh::lean_box(0);
                                    v_isShared_2601_ = v_isSharedCheck_2605_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_2576_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2575_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2565_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
                v___x_2566_ = 0;
                v___x_2567_ = l_Lean_MessageData_ofConstName(v_constName_2557_, v___x_2566_);
                v___x_2568_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2568_, 0, v___x_2565_);
                leanh::lean_ctor_set(v___x_2568_, 1, v___x_2567_);
                v___x_2569_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___closed__1);
                v___x_2570_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2570_, 0, v___x_2568_);
                leanh::lean_ctor_set(v___x_2570_, 1, v___x_2569_);
                v___x_2571_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg(v___x_2570_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
                return v___x_2571_;
            }
            2 => {
                if v_isShared_2582_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2581_, 0);
                    v___x_2584_ = v___x_2581_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_val_2579_);
                    v___x_2584_ = v_reuseFailAlloc_2585_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2584_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_2589_) == 0 {
                    leanh::lean_del_object(v___x_2591_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_constName_2557_);
                    v_val_2593_ = leanh::lean_ctor_get(v_a_2589_, 0);
                    leanh::lean_inc(v_val_2593_);
                    leanh::lean_dec_ref_known(v_a_2589_, 1);
                    if v_isShared_2592_ == 0 {
                        leanh::lean_ctor_set(v___x_2591_, 0, v_val_2593_);
                        v___x_2595_ = v___x_2591_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2596_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_val_2593_);
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
                    v_reuseFailAlloc_2604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
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
    mut v_constName_2606_: *mut leanh::LeanObject,
    mut v___y_2607_: *mut leanh::LeanObject,
    mut v___y_2608_: *mut leanh::LeanObject,
    mut v___y_2609_: *mut leanh::LeanObject,
    mut v___y_2610_: *mut leanh::LeanObject,
    mut v___y_2611_: *mut leanh::LeanObject,
    mut v___y_2612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2613_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(v_constName_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
    leanh::lean_dec(v___y_2611_);
    leanh::lean_dec_ref(v___y_2610_);
    leanh::lean_dec(v___y_2609_);
    leanh::lean_dec_ref(v___y_2608_);
    leanh::lean_dec_ref(v___y_2607_);
    return v_res_2613_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1(
    mut v_sz_2614_: usize,
    mut v_i_2615_: usize,
    mut v_bs_2616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2617_: u8 = 0;
    let mut v_v_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: usize = 0;
    let mut v___x_2624_: usize = 0;
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2617_ = lean_usize_dec_lt(v_i_2615_, v_sz_2614_);
                if v___x_2617_ == 0 {
                    return v_bs_2616_;
                } else {
                    v_v_2618_ = lean_array_uget_borrowed(v_bs_2616_, v_i_2615_);
                    v_fvarId_2619_ = leanh::lean_ctor_get(v_v_2618_, 0);
                    leanh::lean_inc(v_fvarId_2619_);
                    v___x_2620_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2621_ = lean_array_uset(v_bs_2616_, v_i_2615_, v___x_2620_);
                    v___x_2622_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2622_, 0, v_fvarId_2619_);
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
    mut v_sz_2627_: *mut leanh::LeanObject,
    mut v_i_2628_: *mut leanh::LeanObject,
    mut v_bs_2629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2630_: usize = 0;
    let mut v_i_boxed_2631_: usize = 0;
    let mut v_res_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2630_ = leanh::lean_unbox_usize(v_sz_2627_);
    leanh::lean_dec(v_sz_2627_);
    v_i_boxed_2631_ = leanh::lean_unbox_usize(v_i_2628_);
    leanh::lean_dec(v_i_2628_);
    v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1(v_sz_boxed_2630_, v_i_boxed_2631_, v_bs_2629_);
    return v_res_2632_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(
    mut v_discr_2633_: *mut leanh::LeanObject,
    mut v_ctorName_2634_: *mut leanh::LeanObject,
    mut v_ctorFields_2635_: *mut leanh::LeanObject,
    mut v_a_2636_: *mut leanh::LeanObject,
    mut v_a_2637_: *mut leanh::LeanObject,
    mut v_a_2638_: *mut leanh::LeanObject,
    mut v_a_2639_: *mut leanh::LeanObject,
    mut v_a_2640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v_sz_2654_: usize = 0;
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v_name_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v_discrCtorMap_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorDiscrMap_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_unused_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2687_: u8 = 0;
    let mut v_discrCtorMap_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorDiscrMap_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2699_: u8 = 0;
    let mut v_a_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2703_: u8 = 0;
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_a_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v_a_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2642_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(v_ctorName_2634_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
                if leanh::lean_obj_tag(v___x_2642_) == 0 {
                    v_a_2643_ = leanh::lean_ctor_get(v___x_2642_, 0);
                    leanh::lean_inc(v_a_2643_);
                    leanh::lean_dec_ref_known(v___x_2642_, 1);
                    leanh::lean_inc(v_discr_2633_);
                    v___x_2644_ = l_Lean_Compiler_LCNF_getType(
                        v_discr_2633_,
                        v_a_2637_,
                        v_a_2638_,
                        v_a_2639_,
                        v_a_2640_,
                    );
                    if leanh::lean_obj_tag(v___x_2644_) == 0 {
                        v_a_2645_ = leanh::lean_ctor_get(v___x_2644_, 0);
                        leanh::lean_inc(v_a_2645_);
                        leanh::lean_dec_ref_known(v___x_2644_, 1);
                        v_toConstantVal_2646_ = leanh::lean_ctor_get(v_a_2643_, 0);
                        leanh::lean_inc_ref(v_toConstantVal_2646_);
                        v_induct_2647_ = leanh::lean_ctor_get(v_a_2643_, 1);
                        v_numParams_2648_ = leanh::lean_ctor_get(v_a_2643_, 3);
                        v___x_2649_ = l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(
                            v_a_2645_,
                            v_induct_2647_,
                            v_a_2639_,
                            v_a_2640_,
                        );
                        if leanh::lean_obj_tag(v___x_2649_) == 0 {
                            v_a_2650_ = leanh::lean_ctor_get(v___x_2649_, 0);
                            v_isSharedCheck_2699_ =
                                (!leanh::lean_is_exclusive(v___x_2649_)) as u8;
                            if v_isSharedCheck_2699_ == 0 {
                                v___x_2652_ = v___x_2649_;
                                v_isShared_2653_ = v_isSharedCheck_2699_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2650_);
                                leanh::lean_dec(v___x_2649_);
                                v___x_2652_ = leanh::lean_box(0);
                                v_isShared_2653_ = v_isSharedCheck_2699_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_toConstantVal_2646_);
                            leanh::lean_dec(v_a_2643_);
                            leanh::lean_dec_ref(v_ctorFields_2635_);
                            leanh::lean_dec(v_discr_2633_);
                            v_a_2700_ = leanh::lean_ctor_get(v___x_2649_, 0);
                            v_isSharedCheck_2707_ =
                                (!leanh::lean_is_exclusive(v___x_2649_)) as u8;
                            if v_isSharedCheck_2707_ == 0 {
                                v___x_2702_ = v___x_2649_;
                                v_isShared_2703_ = v_isSharedCheck_2707_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2700_);
                                leanh::lean_dec(v___x_2649_);
                                v___x_2702_ = leanh::lean_box(0);
                                v_isShared_2703_ = v_isSharedCheck_2707_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2643_);
                        leanh::lean_dec_ref(v_ctorFields_2635_);
                        leanh::lean_dec(v_discr_2633_);
                        v_a_2708_ = leanh::lean_ctor_get(v___x_2644_, 0);
                        v_isSharedCheck_2715_ =
                            (!leanh::lean_is_exclusive(v___x_2644_)) as u8;
                        if v_isSharedCheck_2715_ == 0 {
                            v___x_2710_ = v___x_2644_;
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2708_);
                            leanh::lean_dec(v___x_2644_);
                            v___x_2710_ = leanh::lean_box(0);
                            v_isShared_2711_ = v_isSharedCheck_2715_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_ctorFields_2635_);
                    leanh::lean_dec(v_discr_2633_);
                    v_a_2716_ = leanh::lean_ctor_get(v___x_2642_, 0);
                    v_isSharedCheck_2723_ = (!leanh::lean_is_exclusive(v___x_2642_)) as u8;
                    if v_isSharedCheck_2723_ == 0 {
                        v___x_2718_ = v___x_2642_;
                        v_isShared_2719_ = v_isSharedCheck_2723_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2716_);
                        leanh::lean_dec(v___x_2642_);
                        v___x_2718_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v_a_2650_) == 1 {
                    v_val_2657_ = leanh::lean_ctor_get(v_a_2650_, 0);
                    leanh::lean_inc(v_val_2657_);
                    leanh::lean_dec_ref_known(v_a_2650_, 1);
                    v_fst_2658_ = leanh::lean_ctor_get(v_val_2657_, 0);
                    v_snd_2659_ = leanh::lean_ctor_get(v_val_2657_, 1);
                    v_isSharedCheck_2687_ = (!leanh::lean_is_exclusive(v_val_2657_)) as u8;
                    if v_isSharedCheck_2687_ == 0 {
                        v___x_2661_ = v_val_2657_;
                        v_isShared_2662_ = v_isSharedCheck_2687_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2659_);
                        leanh::lean_inc(v_fst_2658_);
                        leanh::lean_dec(v_val_2657_);
                        v___x_2661_ = leanh::lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2687_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2650_);
                    leanh::lean_dec_ref(v_toConstantVal_2646_);
                    v_discrCtorMap_2688_ = leanh::lean_ctor_get(v_a_2636_, 0);
                    v_ctorDiscrMap_2689_ = leanh::lean_ctor_get(v_a_2636_, 1);
                    v___x_2690_ = leanh::lean_box(0);
                    leanh::lean_inc(v_numParams_2648_);
                    v___x_2691_ = lean_mk_array(v_numParams_2648_, v___x_2690_);
                    v___x_2692_ = l_Array_append___redArg(v___x_2691_, v___x_2656_);
                    leanh::lean_dec_ref(v___x_2656_);
                    v___x_2693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2693_, 0, v_a_2643_);
                    leanh::lean_ctor_set(v___x_2693_, 1, v___x_2692_);
                    leanh::lean_inc(v_discrCtorMap_2688_);
                    v___x_2694_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_2633_, v___x_2693_, v_discrCtorMap_2688_);
                    leanh::lean_inc_ref(v_ctorDiscrMap_2689_);
                    v___x_2695_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2695_, 0, v___x_2694_);
                    leanh::lean_ctor_set(v___x_2695_, 1, v_ctorDiscrMap_2689_);
                    if v_isShared_2653_ == 0 {
                        leanh::lean_ctor_set(v___x_2652_, 0, v___x_2695_);
                        v___x_2697_ = v___x_2652_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2698_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
                        v___x_2697_ = v_reuseFailAlloc_2698_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_name_2663_ = leanh::lean_ctor_get(v_toConstantVal_2646_, 0);
                v_isSharedCheck_2684_ =
                    (!leanh::lean_is_exclusive(v_toConstantVal_2646_)) as u8;
                if v_isSharedCheck_2684_ == 0 {
                    v_unused_2685_ = leanh::lean_ctor_get(v_toConstantVal_2646_, 2);
                    leanh::lean_dec(v_unused_2685_);
                    v_unused_2686_ = leanh::lean_ctor_get(v_toConstantVal_2646_, 1);
                    leanh::lean_dec(v_unused_2686_);
                    v___x_2665_ = v_toConstantVal_2646_;
                    v_isShared_2666_ = v_isSharedCheck_2684_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_name_2663_);
                    leanh::lean_dec(v_toConstantVal_2646_);
                    v___x_2665_ = leanh::lean_box(0);
                    v_isShared_2666_ = v_isSharedCheck_2684_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_discrCtorMap_2667_ = leanh::lean_ctor_get(v_a_2636_, 0);
                v_ctorDiscrMap_2668_ = leanh::lean_ctor_get(v_a_2636_, 1);
                v___x_2669_ = l_Array_append___redArg(v_snd_2659_, v___x_2656_);
                leanh::lean_dec_ref(v___x_2656_);
                leanh::lean_inc_ref(v___x_2669_);
                if v_isShared_2662_ == 0 {
                    leanh::lean_ctor_set(v___x_2661_, 1, v___x_2669_);
                    leanh::lean_ctor_set(v___x_2661_, 0, v_a_2643_);
                    v___x_2671_ = v___x_2661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2683_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2643_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2669_);
                    v___x_2671_ = v_reuseFailAlloc_2683_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2672_ = 0;
                if v_isShared_2666_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2665_, 3);
                    leanh::lean_ctor_set(v___x_2665_, 2, v___x_2669_);
                    leanh::lean_ctor_set(v___x_2665_, 1, v_fst_2658_);
                    v___x_2674_ = v___x_2665_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_name_2663_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_fst_2658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 2, v___x_2669_);
                    v___x_2674_ = v_reuseFailAlloc_2682_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc(v_discrCtorMap_2667_);
                leanh::lean_inc(v_discr_2633_);
                v___x_2675_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_2633_, v___x_2671_, v_discrCtorMap_2667_);
                v___x_2676_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_2672_, v___x_2674_);
                leanh::lean_inc_ref(v_ctorDiscrMap_2668_);
                v___x_2677_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2___redArg(v_ctorDiscrMap_2668_, v___x_2676_, v_discr_2633_);
                v___x_2678_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2678_, 0, v___x_2675_);
                leanh::lean_ctor_set(v___x_2678_, 1, v___x_2677_);
                if v_isShared_2653_ == 0 {
                    leanh::lean_ctor_set(v___x_2652_, 0, v___x_2678_);
                    v___x_2680_ = v___x_2652_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2681_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
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
                    v_reuseFailAlloc_2706_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
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
                    v_reuseFailAlloc_2714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
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
                    v_reuseFailAlloc_2722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
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
    mut v_discr_2724_: *mut leanh::LeanObject,
    mut v_ctorName_2725_: *mut leanh::LeanObject,
    mut v_ctorFields_2726_: *mut leanh::LeanObject,
    mut v_a_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
    mut v_a_2731_: *mut leanh::LeanObject,
    mut v_a_2732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2733_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2724_, v_ctorName_2725_, v_ctorFields_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
    leanh::lean_dec(v_a_2731_);
    leanh::lean_dec_ref(v_a_2730_);
    leanh::lean_dec(v_a_2729_);
    leanh::lean_dec_ref(v_a_2728_);
    leanh::lean_dec_ref(v_a_2727_);
    return v_res_2733_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0(
    mut v_00_u03b1_2734_: *mut leanh::LeanObject,
    mut v_msg_2735_: *mut leanh::LeanObject,
    mut v___y_2736_: *mut leanh::LeanObject,
    mut v___y_2737_: *mut leanh::LeanObject,
    mut v___y_2738_: *mut leanh::LeanObject,
    mut v___y_2739_: *mut leanh::LeanObject,
    mut v___y_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___redArg(v_msg_2735_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
    return v___x_2742_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0___boxed(
    mut v_00_u03b1_2743_: *mut leanh::LeanObject,
    mut v_msg_2744_: *mut leanh::LeanObject,
    mut v___y_2745_: *mut leanh::LeanObject,
    mut v___y_2746_: *mut leanh::LeanObject,
    mut v___y_2747_: *mut leanh::LeanObject,
    mut v___y_2748_: *mut leanh::LeanObject,
    mut v___y_2749_: *mut leanh::LeanObject,
    mut v___y_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2751_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0_spec__0(v_00_u03b1_2743_, v_msg_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
    leanh::lean_dec(v___y_2749_);
    leanh::lean_dec_ref(v___y_2748_);
    leanh::lean_dec(v___y_2747_);
    leanh::lean_dec_ref(v___y_2746_);
    leanh::lean_dec_ref(v___y_2745_);
    return v_res_2751_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2(
    mut v_00_u03b2_2752_: *mut leanh::LeanObject,
    mut v_x_2753_: *mut leanh::LeanObject,
    mut v_x_2754_: *mut leanh::LeanObject,
    mut v_x_2755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2___redArg(v_x_2753_, v_x_2754_, v_x_2755_);
    return v___x_2756_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4(
    mut v_00_u03b2_2757_: *mut leanh::LeanObject,
    mut v_x_2758_: *mut leanh::LeanObject,
    mut v_x_2759_: usize,
    mut v_x_2760_: usize,
    mut v_x_2761_: *mut leanh::LeanObject,
    mut v_x_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg(v_x_2758_, v_x_2759_, v_x_2760_, v_x_2761_, v_x_2762_);
    return v___x_2763_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___boxed(
    mut v_00_u03b2_2764_: *mut leanh::LeanObject,
    mut v_x_2765_: *mut leanh::LeanObject,
    mut v_x_2766_: *mut leanh::LeanObject,
    mut v_x_2767_: *mut leanh::LeanObject,
    mut v_x_2768_: *mut leanh::LeanObject,
    mut v_x_2769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5303__boxed_2770_: usize = 0;
    let mut v_x_5304__boxed_2771_: usize = 0;
    let mut v_res_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5303__boxed_2770_ = leanh::lean_unbox_usize(v_x_2766_);
    leanh::lean_dec(v_x_2766_);
    v_x_5304__boxed_2771_ = leanh::lean_unbox_usize(v_x_2767_);
    leanh::lean_dec(v_x_2767_);
    v_res_2772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4(v_00_u03b2_2764_, v_x_2765_, v_x_5303__boxed_2770_, v_x_5304__boxed_2771_, v_x_2768_, v_x_2769_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2773_: *mut leanh::LeanObject,
    mut v_n_2774_: *mut leanh::LeanObject,
    mut v_k_2775_: *mut leanh::LeanObject,
    mut v_v_2776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2777_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5___redArg(v_n_2774_, v_k_2775_, v_v_2776_);
    return v___x_2777_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6(
    mut v_00_u03b2_2778_: *mut leanh::LeanObject,
    mut v_depth_2779_: usize,
    mut v_keys_2780_: *mut leanh::LeanObject,
    mut v_vals_2781_: *mut leanh::LeanObject,
    mut v_heq_2782_: *mut leanh::LeanObject,
    mut v_i_2783_: *mut leanh::LeanObject,
    mut v_entries_2784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2785_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___redArg(v_depth_2779_, v_keys_2780_, v_vals_2781_, v_i_2783_, v_entries_2784_);
    return v___x_2785_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b2_2786_: *mut leanh::LeanObject,
    mut v_depth_2787_: *mut leanh::LeanObject,
    mut v_keys_2788_: *mut leanh::LeanObject,
    mut v_vals_2789_: *mut leanh::LeanObject,
    mut v_heq_2790_: *mut leanh::LeanObject,
    mut v_i_2791_: *mut leanh::LeanObject,
    mut v_entries_2792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2793_: usize = 0;
    let mut v_res_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2793_ = leanh::lean_unbox_usize(v_depth_2787_);
    leanh::lean_dec(v_depth_2787_);
    v_res_2794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__6(v_00_u03b2_2786_, v_depth_boxed_2793_, v_keys_2788_, v_vals_2789_, v_heq_2790_, v_i_2791_, v_entries_2792_);
    leanh::lean_dec_ref(v_vals_2789_);
    leanh::lean_dec_ref(v_keys_2788_);
    return v_res_2794_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_2795_: *mut leanh::LeanObject,
    mut v_x_2796_: *mut leanh::LeanObject,
    mut v_x_2797_: *mut leanh::LeanObject,
    mut v_x_2798_: *mut leanh::LeanObject,
    mut v_x_2799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4_spec__5_spec__6___redArg(v_x_2796_, v_x_2797_, v_x_2798_, v_x_2799_);
    return v___x_2800_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg(
    mut v_discr_2801_: *mut leanh::LeanObject,
    mut v_ctorName_2802_: *mut leanh::LeanObject,
    mut v_ctorFields_2803_: *mut leanh::LeanObject,
    mut v_x_2804_: *mut leanh::LeanObject,
    mut v_a_2805_: *mut leanh::LeanObject,
    mut v_a_2806_: *mut leanh::LeanObject,
    mut v_a_2807_: *mut leanh::LeanObject,
    mut v_a_2808_: *mut leanh::LeanObject,
    mut v_a_2809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2817_: u8 = 0;
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2811_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2801_, v_ctorName_2802_, v_ctorFields_2803_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
                if leanh::lean_obj_tag(v___x_2811_) == 0 {
                    v_a_2812_ = leanh::lean_ctor_get(v___x_2811_, 0);
                    leanh::lean_inc(v_a_2812_);
                    leanh::lean_dec_ref_known(v___x_2811_, 1);
                    leanh::lean_inc(v_a_2809_);
                    leanh::lean_inc_ref(v_a_2808_);
                    leanh::lean_inc(v_a_2807_);
                    leanh::lean_inc_ref(v_a_2806_);
                    v___x_2813_ = leanh::lean_apply_6(
                        v_x_2804_,
                        v_a_2812_,
                        v_a_2806_,
                        v_a_2807_,
                        v_a_2808_,
                        v_a_2809_,
                        leanh::lean_box(0),
                    );
                    return v___x_2813_;
                } else {
                    leanh::lean_dec_ref(v_x_2804_);
                    v_a_2814_ = leanh::lean_ctor_get(v___x_2811_, 0);
                    v_isSharedCheck_2821_ = (!leanh::lean_is_exclusive(v___x_2811_)) as u8;
                    if v_isSharedCheck_2821_ == 0 {
                        v___x_2816_ = v___x_2811_;
                        v_isShared_2817_ = v_isSharedCheck_2821_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2814_);
                        leanh::lean_dec(v___x_2811_);
                        v___x_2816_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2820_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
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
    mut v_discr_2822_: *mut leanh::LeanObject,
    mut v_ctorName_2823_: *mut leanh::LeanObject,
    mut v_ctorFields_2824_: *mut leanh::LeanObject,
    mut v_x_2825_: *mut leanh::LeanObject,
    mut v_a_2826_: *mut leanh::LeanObject,
    mut v_a_2827_: *mut leanh::LeanObject,
    mut v_a_2828_: *mut leanh::LeanObject,
    mut v_a_2829_: *mut leanh::LeanObject,
    mut v_a_2830_: *mut leanh::LeanObject,
    mut v_a_2831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2830_);
    leanh::lean_dec_ref(v_a_2829_);
    leanh::lean_dec(v_a_2828_);
    leanh::lean_dec_ref(v_a_2827_);
    leanh::lean_dec_ref(v_a_2826_);
    return v_res_2832_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp(
    mut v_00_u03b1_2833_: *mut leanh::LeanObject,
    mut v_discr_2834_: *mut leanh::LeanObject,
    mut v_ctorName_2835_: *mut leanh::LeanObject,
    mut v_ctorFields_2836_: *mut leanh::LeanObject,
    mut v_x_2837_: *mut leanh::LeanObject,
    mut v_a_2838_: *mut leanh::LeanObject,
    mut v_a_2839_: *mut leanh::LeanObject,
    mut v_a_2840_: *mut leanh::LeanObject,
    mut v_a_2841_: *mut leanh::LeanObject,
    mut v_a_2842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2850_: u8 = 0;
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2854_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2844_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2834_, v_ctorName_2835_, v_ctorFields_2836_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
                if leanh::lean_obj_tag(v___x_2844_) == 0 {
                    v_a_2845_ = leanh::lean_ctor_get(v___x_2844_, 0);
                    leanh::lean_inc(v_a_2845_);
                    leanh::lean_dec_ref_known(v___x_2844_, 1);
                    leanh::lean_inc(v_a_2842_);
                    leanh::lean_inc_ref(v_a_2841_);
                    leanh::lean_inc(v_a_2840_);
                    leanh::lean_inc_ref(v_a_2839_);
                    v___x_2846_ = leanh::lean_apply_6(
                        v_x_2837_,
                        v_a_2845_,
                        v_a_2839_,
                        v_a_2840_,
                        v_a_2841_,
                        v_a_2842_,
                        leanh::lean_box(0),
                    );
                    return v___x_2846_;
                } else {
                    leanh::lean_dec_ref(v_x_2837_);
                    v_a_2847_ = leanh::lean_ctor_get(v___x_2844_, 0);
                    v_isSharedCheck_2854_ = (!leanh::lean_is_exclusive(v___x_2844_)) as u8;
                    if v_isSharedCheck_2854_ == 0 {
                        v___x_2849_ = v___x_2844_;
                        v_isShared_2850_ = v_isSharedCheck_2854_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2847_);
                        leanh::lean_dec(v___x_2844_);
                        v___x_2849_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2853_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
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
    mut v_00_u03b1_2855_: *mut leanh::LeanObject,
    mut v_discr_2856_: *mut leanh::LeanObject,
    mut v_ctorName_2857_: *mut leanh::LeanObject,
    mut v_ctorFields_2858_: *mut leanh::LeanObject,
    mut v_x_2859_: *mut leanh::LeanObject,
    mut v_a_2860_: *mut leanh::LeanObject,
    mut v_a_2861_: *mut leanh::LeanObject,
    mut v_a_2862_: *mut leanh::LeanObject,
    mut v_a_2863_: *mut leanh::LeanObject,
    mut v_a_2864_: *mut leanh::LeanObject,
    mut v_a_2865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2864_);
    leanh::lean_dec_ref(v_a_2863_);
    leanh::lean_dec(v_a_2862_);
    leanh::lean_dec_ref(v_a_2861_);
    leanh::lean_dec_ref(v_a_2860_);
    return v_res_2866_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0(
    mut v_discr_2867_: *mut leanh::LeanObject,
    mut v_ctorName_2868_: *mut leanh::LeanObject,
    mut v_ctorFields_2869_: *mut leanh::LeanObject,
    mut v_00_u03b2_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2878_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2867_, v_ctorName_2868_, v_ctorFields_2869_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
                if leanh::lean_obj_tag(v___x_2878_) == 0 {
                    v_a_2879_ = leanh::lean_ctor_get(v___x_2878_, 0);
                    leanh::lean_inc(v_a_2879_);
                    leanh::lean_dec_ref_known(v___x_2878_, 1);
                    leanh::lean_inc(v___y_2876_);
                    leanh::lean_inc_ref(v___y_2875_);
                    leanh::lean_inc(v___y_2874_);
                    leanh::lean_inc_ref(v___y_2873_);
                    v___x_2880_ = leanh::lean_apply_6(
                        v___y_2871_,
                        v_a_2879_,
                        v___y_2873_,
                        v___y_2874_,
                        v___y_2875_,
                        v___y_2876_,
                        leanh::lean_box(0),
                    );
                    return v___x_2880_;
                } else {
                    leanh::lean_dec_ref(v___y_2871_);
                    v_a_2881_ = leanh::lean_ctor_get(v___x_2878_, 0);
                    v_isSharedCheck_2888_ = (!leanh::lean_is_exclusive(v___x_2878_)) as u8;
                    if v_isSharedCheck_2888_ == 0 {
                        v___x_2883_ = v___x_2878_;
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2881_);
                        leanh::lean_dec(v___x_2878_);
                        v___x_2883_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2887_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
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
    mut v_discr_2889_: *mut leanh::LeanObject,
    mut v_ctorName_2890_: *mut leanh::LeanObject,
    mut v_ctorFields_2891_: *mut leanh::LeanObject,
    mut v_00_u03b2_2892_: *mut leanh::LeanObject,
    mut v___y_2893_: *mut leanh::LeanObject,
    mut v___y_2894_: *mut leanh::LeanObject,
    mut v___y_2895_: *mut leanh::LeanObject,
    mut v___y_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2898_);
    leanh::lean_dec_ref(v___y_2897_);
    leanh::lean_dec(v___y_2896_);
    leanh::lean_dec_ref(v___y_2895_);
    leanh::lean_dec_ref(v___y_2894_);
    return v_res_2900_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg(
    mut v_inst_2901_: *mut leanh::LeanObject,
    mut v_discr_2902_: *mut leanh::LeanObject,
    mut v_ctorName_2903_: *mut leanh::LeanObject,
    mut v_ctorFields_2904_: *mut leanh::LeanObject,
    mut v_a_2905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2906_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    leanh::lean_closure_set(v___f_2906_, 0, v_discr_2902_);
    leanh::lean_closure_set(v___f_2906_, 1, v_ctorName_2903_);
    leanh::lean_closure_set(v___f_2906_, 2, v_ctorFields_2904_);
    v___x_2907_ = leanh::lean_apply_3(
        v_inst_2901_,
        leanh::lean_box(0),
        v___f_2906_,
        v_a_2905_,
    );
    return v___x_2907_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withDiscrCtor(
    mut v_m_2908_: *mut leanh::LeanObject,
    mut v_00_u03b1_2909_: *mut leanh::LeanObject,
    mut v_inst_2910_: *mut leanh::LeanObject,
    mut v_discr_2911_: *mut leanh::LeanObject,
    mut v_ctorName_2912_: *mut leanh::LeanObject,
    mut v_ctorFields_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2915_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    leanh::lean_closure_set(v___f_2915_, 0, v_discr_2911_);
    leanh::lean_closure_set(v___f_2915_, 1, v_ctorName_2912_);
    leanh::lean_closure_set(v___f_2915_, 2, v_ctorFields_2913_);
    v___x_2916_ = leanh::lean_apply_3(
        v_inst_2910_,
        leanh::lean_box(0),
        v___f_2915_,
        v_a_2914_,
    );
    return v___x_2916_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2917_: *mut leanh::LeanObject,
    mut v_vals_2918_: *mut leanh::LeanObject,
    mut v_i_2919_: *mut leanh::LeanObject,
    mut v_k_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2921_ = lean_array_get_size(v_keys_2917_);
                v___x_2922_ = lean_nat_dec_lt(v_i_2919_, v___x_2921_);
                if v___x_2922_ == 0 {
                    leanh::lean_dec(v_i_2919_);
                    v___x_2923_ = leanh::lean_box(0);
                    return v___x_2923_;
                } else {
                    v_k_x27_2924_ = lean_array_fget_borrowed(v_keys_2917_, v_i_2919_);
                    v___x_2925_ = lean_expr_eqv(v_k_2920_, v_k_x27_2924_);
                    if v___x_2925_ == 0 {
                        v___x_2926_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2927_ = lean_nat_add(v_i_2919_, v___x_2926_);
                        leanh::lean_dec(v_i_2919_);
                        v_i_2919_ = v___x_2927_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2929_ = lean_array_fget_borrowed(v_vals_2918_, v_i_2919_);
                        leanh::lean_dec(v_i_2919_);
                        leanh::lean_inc(v___x_2929_);
                        v___x_2930_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2930_, 0, v___x_2929_);
                        return v___x_2930_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2931_: *mut leanh::LeanObject,
    mut v_vals_2932_: *mut leanh::LeanObject,
    mut v_i_2933_: *mut leanh::LeanObject,
    mut v_k_2934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2935_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2931_, v_vals_2932_, v_i_2933_, v_k_2934_);
    leanh::lean_dec_ref(v_k_2934_);
    leanh::lean_dec_ref(v_vals_2932_);
    leanh::lean_dec_ref(v_keys_2931_);
    return v_res_2935_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(
    mut v_x_2936_: *mut leanh::LeanObject,
    mut v_x_2937_: usize,
    mut v_x_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: usize = 0;
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: usize = 0;
    let mut v_j_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: usize = 0;
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2936_) == 0 {
                    v_es_2939_ = leanh::lean_ctor_get(v_x_2936_, 0);
                    v___x_2940_ = leanh::lean_box(2);
                    v___x_2941_ = 5usize;
                    v___x_2942_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__2_spec__4___redArg___closed__1);
                    v___x_2943_ = lean_usize_land(v_x_2937_, v___x_2942_);
                    v_j_2944_ = lean_usize_to_nat(v___x_2943_);
                    v___x_2945_ = lean_array_get_borrowed(v___x_2940_, v_es_2939_, v_j_2944_);
                    leanh::lean_dec(v_j_2944_);
                    match leanh::lean_obj_tag(v___x_2945_) {
                        0 => {
                            v_key_2946_ = leanh::lean_ctor_get(v___x_2945_, 0);
                            v_val_2947_ = leanh::lean_ctor_get(v___x_2945_, 1);
                            v___x_2948_ = lean_expr_eqv(v_x_2938_, v_key_2946_);
                            if v___x_2948_ == 0 {
                                v___x_2949_ = leanh::lean_box(0);
                                return v___x_2949_;
                            } else {
                                leanh::lean_inc(v_val_2947_);
                                v___x_2950_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2950_, 0, v_val_2947_);
                                return v___x_2950_;
                            }
                        }
                        1 => {
                            v_node_2951_ = leanh::lean_ctor_get(v___x_2945_, 0);
                            v___x_2952_ = lean_usize_shift_right(v_x_2937_, v___x_2941_);
                            v_x_2936_ = v_node_2951_;
                            v_x_2937_ = v___x_2952_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2954_ = leanh::lean_box(0);
                            return v___x_2954_;
                        }
                    }
                } else {
                    v_ks_2955_ = leanh::lean_ctor_get(v_x_2936_, 0);
                    v_vs_2956_ = leanh::lean_ctor_get(v_x_2936_, 1);
                    v___x_2957_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2958_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2955_, v_vs_2956_, v___x_2957_, v_x_2938_);
                    return v___x_2958_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2959_: *mut leanh::LeanObject,
    mut v_x_2960_: *mut leanh::LeanObject,
    mut v_x_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1257__boxed_2962_: usize = 0;
    let mut v_res_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1257__boxed_2962_ = leanh::lean_unbox_usize(v_x_2960_);
    leanh::lean_dec(v_x_2960_);
    v_res_2963_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_2959_, v_x_1257__boxed_2962_, v_x_2961_);
    leanh::lean_dec_ref(v_x_2961_);
    leanh::lean_dec_ref(v_x_2959_);
    return v_res_2963_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(
    mut v_x_2964_: *mut leanh::LeanObject,
    mut v_x_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2966_: u64 = 0;
    let mut v___x_2967_: usize = 0;
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2966_ = l_Lean_Expr_hash(v_x_2965_);
    v___x_2967_ = lean_uint64_to_usize(v___x_2966_);
    v___x_2968_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_2964_, v___x_2967_, v_x_2965_);
    return v___x_2968_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg___boxed(
    mut v_x_2969_: *mut leanh::LeanObject,
    mut v_x_2970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_x_2969_, v_x_2970_);
    leanh::lean_dec_ref(v_x_2970_);
    leanh::lean_dec_ref(v_x_2969_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(
    mut v_e_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
    mut v_a_2974_: *mut leanh::LeanObject,
    mut v_a_2975_: *mut leanh::LeanObject,
    mut v_a_2976_: *mut leanh::LeanObject,
    mut v_a_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctorDiscrMap_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v___x_2989_: u8 = 0;
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut v_a_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_a_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ctorDiscrMap_2979_ = leanh::lean_ctor_get(v_a_2973_, 1);
                v___x_2980_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_ctorDiscrMap_2979_, v_e_2972_);
                if leanh::lean_obj_tag(v___x_2980_) == 1 {
                    v_val_2981_ = leanh::lean_ctor_get(v___x_2980_, 0);
                    leanh::lean_inc(v_val_2981_);
                    v___x_2982_ = l_Lean_Compiler_LCNF_getType(
                        v_val_2981_,
                        v_a_2974_,
                        v_a_2975_,
                        v_a_2976_,
                        v_a_2977_,
                    );
                    if leanh::lean_obj_tag(v___x_2982_) == 0 {
                        v_a_2983_ = leanh::lean_ctor_get(v___x_2982_, 0);
                        leanh::lean_inc(v_a_2983_);
                        leanh::lean_dec_ref_known(v___x_2982_, 1);
                        v___x_2984_ = l_Lean_Compiler_LCNF_inferType(
                            v_e_2972_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_,
                        );
                        if leanh::lean_obj_tag(v___x_2984_) == 0 {
                            v_a_2985_ = leanh::lean_ctor_get(v___x_2984_, 0);
                            v_isSharedCheck_2997_ =
                                (!leanh::lean_is_exclusive(v___x_2984_)) as u8;
                            if v_isSharedCheck_2997_ == 0 {
                                v___x_2987_ = v___x_2984_;
                                v_isShared_2988_ = v_isSharedCheck_2997_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2985_);
                                leanh::lean_dec(v___x_2984_);
                                v___x_2987_ = leanh::lean_box(0);
                                v_isShared_2988_ = v_isSharedCheck_2997_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2983_);
                            leanh::lean_dec_ref_known(v___x_2980_, 1);
                            v_a_2998_ = leanh::lean_ctor_get(v___x_2984_, 0);
                            v_isSharedCheck_3005_ =
                                (!leanh::lean_is_exclusive(v___x_2984_)) as u8;
                            if v_isSharedCheck_3005_ == 0 {
                                v___x_3000_ = v___x_2984_;
                                v_isShared_3001_ = v_isSharedCheck_3005_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2998_);
                                leanh::lean_dec(v___x_2984_);
                                v___x_3000_ = leanh::lean_box(0);
                                v_isShared_3001_ = v_isSharedCheck_3005_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_2980_, 1);
                        leanh::lean_dec_ref(v_e_2972_);
                        v_a_3006_ = leanh::lean_ctor_get(v___x_2982_, 0);
                        v_isSharedCheck_3013_ =
                            (!leanh::lean_is_exclusive(v___x_2982_)) as u8;
                        if v_isSharedCheck_3013_ == 0 {
                            v___x_3008_ = v___x_2982_;
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3006_);
                            leanh::lean_dec(v___x_2982_);
                            v___x_3008_ = leanh::lean_box(0);
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2980_);
                    leanh::lean_dec_ref(v_e_2972_);
                    v___x_3014_ = leanh::lean_box(0);
                    v___x_3015_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3015_, 0, v___x_3014_);
                    return v___x_3015_;
                }
            }
            1 => {
                v___x_2989_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2983_, v_a_2985_);
                if v___x_2989_ == 0 {
                    leanh::lean_dec_ref_known(v___x_2980_, 1);
                    v___x_2990_ = leanh::lean_box(0);
                    if v_isShared_2988_ == 0 {
                        leanh::lean_ctor_set(v___x_2987_, 0, v___x_2990_);
                        v___x_2992_ = v___x_2987_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2993_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
                        v___x_2992_ = v_reuseFailAlloc_2993_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2988_ == 0 {
                        leanh::lean_ctor_set(v___x_2987_, 0, v___x_2980_);
                        v___x_2995_ = v___x_2987_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2996_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2980_);
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
                    v_reuseFailAlloc_3004_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
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
                    v_reuseFailAlloc_3012_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
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
    mut v_e_3016_: *mut leanh::LeanObject,
    mut v_a_3017_: *mut leanh::LeanObject,
    mut v_a_3018_: *mut leanh::LeanObject,
    mut v_a_3019_: *mut leanh::LeanObject,
    mut v_a_3020_: *mut leanh::LeanObject,
    mut v_a_3021_: *mut leanh::LeanObject,
    mut v_a_3022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3023_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(
        v_e_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_,
    );
    leanh::lean_dec(v_a_3021_);
    leanh::lean_dec_ref(v_a_3020_);
    leanh::lean_dec(v_a_3019_);
    leanh::lean_dec_ref(v_a_3018_);
    leanh::lean_dec_ref(v_a_3017_);
    return v_res_3023_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0(
    mut v_00_u03b2_3024_: *mut leanh::LeanObject,
    mut v_x_3025_: *mut leanh::LeanObject,
    mut v_x_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_x_3025_, v_x_3026_);
    return v___x_3027_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___boxed(
    mut v_00_u03b2_3028_: *mut leanh::LeanObject,
    mut v_x_3029_: *mut leanh::LeanObject,
    mut v_x_3030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3031_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0(v_00_u03b2_3028_, v_x_3029_, v_x_3030_);
    leanh::lean_dec_ref(v_x_3030_);
    leanh::lean_dec_ref(v_x_3029_);
    return v_res_3031_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0(
    mut v_00_u03b2_3032_: *mut leanh::LeanObject,
    mut v_x_3033_: *mut leanh::LeanObject,
    mut v_x_3034_: usize,
    mut v_x_3035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3036_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_3033_, v_x_3034_, v_x_3035_);
    return v___x_3036_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_3037_: *mut leanh::LeanObject,
    mut v_x_3038_: *mut leanh::LeanObject,
    mut v_x_3039_: *mut leanh::LeanObject,
    mut v_x_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1401__boxed_3041_: usize = 0;
    let mut v_res_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1401__boxed_3041_ = leanh::lean_unbox_usize(v_x_3039_);
    leanh::lean_dec(v_x_3039_);
    v_res_3042_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0(v_00_u03b2_3037_, v_x_3038_, v_x_1401__boxed_3041_, v_x_3040_);
    leanh::lean_dec_ref(v_x_3040_);
    leanh::lean_dec_ref(v_x_3038_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3043_: *mut leanh::LeanObject,
    mut v_keys_3044_: *mut leanh::LeanObject,
    mut v_vals_3045_: *mut leanh::LeanObject,
    mut v_heq_3046_: *mut leanh::LeanObject,
    mut v_i_3047_: *mut leanh::LeanObject,
    mut v_k_3048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3049_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3044_, v_vals_3045_, v_i_3047_, v_k_3048_);
    return v___x_3049_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3050_: *mut leanh::LeanObject,
    mut v_keys_3051_: *mut leanh::LeanObject,
    mut v_vals_3052_: *mut leanh::LeanObject,
    mut v_heq_3053_: *mut leanh::LeanObject,
    mut v_i_3054_: *mut leanh::LeanObject,
    mut v_k_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3050_, v_keys_3051_, v_vals_3052_, v_heq_3053_, v_i_3054_, v_k_3055_);
    leanh::lean_dec_ref(v_k_3055_);
    leanh::lean_dec_ref(v_vals_3052_);
    leanh::lean_dec_ref(v_keys_3051_);
    return v_res_3056_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_DiscrM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_DiscrM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
}