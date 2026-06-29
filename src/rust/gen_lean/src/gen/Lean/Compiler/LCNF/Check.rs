// Lean compiler output
// Module: Lean.Compiler.LCNF.Check
// Imports: Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.CompatibleTypes
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_size, lean_array_size, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_eqv, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl,
    l_Lean_Compiler_LCNF_Arg_toExpr___redArg, l_Lean_Compiler_LCNF_FunDecl_getArity___redArg,
    l_Lean_Compiler_LCNF_instBEqLetDecl_beq, l_Lean_Compiler_LCNF_instBEqParam_beq___redArg,
    l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::CompatibleTypes::{
    initialize_Lean_Compiler_LCNF_CompatibleTypes,
    l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes,
    runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_getBinderName, l_Lean_Compiler_LCNF_getConfig___redArg,
    l_Lean_Compiler_LCNF_getFunDecl, l_Lean_Compiler_LCNF_getLetDecl,
    l_Lean_Compiler_LCNF_getParam, l_Lean_Compiler_LCNF_getPurity___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    l_Lean_Compiler_LCNF_Arg_inferType, l_Lean_Compiler_LCNF_Code_inferType,
    l_Lean_Compiler_LCNF_LetValue_inferType, l_Lean_Compiler_LCNF_inferType,
    l_Lean_Compiler_LCNF_mkForallParams,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PrettyPrinter::{
    initialize_Lean_Compiler_LCNF_PrettyPrinter,
    runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Expr_isErased;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvar___override, l_Lean_Expr_headBeta, l_Lean_FVarIdSet_insert,
    l_Lean_instBEqFVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 111, 117, 116, 32, 111, 102, 32, 115, 99, 111, 112,
        101, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 97, 116, 32, 76, 67, 78, 70, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 97, 114, 103, 117, 109, 101, 110, 116, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [10, 98, 117, 116, 32, 105, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 106, 117, 109, 112, 32, 116, 111, 32, 111, 117, 116,
        32, 111, 102, 32, 115, 99, 111, 112, 101, 32, 106, 111, 105, 110, 32, 112, 111, 105, 110,
        116, 32, 96, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 67, 78, 70, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 109, 105, 115, 109, 97,
        116, 99, 104, 32, 97, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        96, 44, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 118, 97, 108, 117, 101, 32, 105,
        110, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        76, 67, 78, 70, 32, 108, 101, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 97, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        96, 44, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 109, 97, 116, 99, 104, 32, 118, 97,
        108, 117, 101, 32, 105, 110, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 97, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        96, 44, 32, 118, 97, 108, 117, 101, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 44, 32, 102, 114, 101, 101, 32, 118,
        97, 114, 105, 97, 98, 108, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 117, 110,
        105, 113, 117, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4_value:
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
    m_fun: l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value:
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
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17_value:
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
    m_fun: l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [76, 67, 78, 70, 32, 99, 104, 101, 99, 107, 0],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        76, 67, 78, 70, 32, 108, 111, 99, 97, 108, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32,
        100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 109, 105, 115, 109, 97, 116, 99,
        104, 32, 97, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        96, 44, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 105, 110, 32, 108, 111,
        99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 100, 111, 101, 115, 32, 109, 97,
        116, 99, 104, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        96, 44, 32, 116, 121, 112, 101, 32, 105, 110, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110,
        116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [10, 101, 120, 112, 101, 99, 116, 101, 100, 0],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        96, 44, 32, 98, 105, 110, 100, 101, 114, 32, 110, 97, 109, 101, 32, 105, 110, 32, 108, 111,
        99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__1_value: crate::leanh::LeanStringObject<
    33,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 32, 96, 103, 111, 116, 111, 96, 44,
        32, 106, 111, 105, 110, 32, 112, 111, 105, 110, 116, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__3_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 104, 97, 115, 32, 35, 0],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__5_value: crate::leanh::LeanStringObject<
    19,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 44, 32, 98, 117, 116, 32, 35, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__7_value: crate::leanh::LeanStringObject<
    15,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        32, 119, 101, 114, 101, 32, 112, 114, 111, 118, 105, 100, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 32, 96, 99, 97, 115, 101, 115, 96, 44, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [96, 32, 104, 97, 115, 32, 35, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [32, 102, 105, 101, 108, 100, 115, 44, 32, 98, 117, 116, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 104, 97, 115, 32, 35, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 111, 102, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 110, 97, 109, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 32, 96, 99, 97, 115, 101, 115, 96, 44, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [96, 32, 111, 99, 99, 117, 114, 115, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 111, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0_value:
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
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(
    mut v_a_3307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v_checkTypes_3314_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_a_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3309_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_3307_);
                if crate::leanh::lean_obj_tag(v___x_3309_) == 0 {
                    v_a_3310_ = crate::leanh::lean_ctor_get(v___x_3309_, 0);
                    v_isSharedCheck_3319_ = (!crate::leanh::lean_is_exclusive(v___x_3309_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3312_ = v___x_3309_;
                        v_isShared_3313_ = v_isSharedCheck_3319_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3310_);
                        crate::leanh::lean_dec(v___x_3309_);
                        v___x_3312_ = crate::leanh::lean_box(0);
                        v_isShared_3313_ = v_isSharedCheck_3319_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3320_ = crate::leanh::lean_ctor_get(v___x_3309_, 0);
                    v_isSharedCheck_3327_ = (!crate::leanh::lean_is_exclusive(v___x_3309_)) as u8;
                    if v_isSharedCheck_3327_ == 0 {
                        v___x_3322_ = v___x_3309_;
                        v_isShared_3323_ = v_isSharedCheck_3327_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3320_);
                        crate::leanh::lean_dec(v___x_3309_);
                        v___x_3322_ = crate::leanh::lean_box(0);
                        v_isShared_3323_ = v_isSharedCheck_3327_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_checkTypes_3314_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3310_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                crate::leanh::lean_dec(v_a_3310_);
                v___x_3315_ = crate::leanh::lean_box((v_checkTypes_3314_) as usize);
                if v_isShared_3313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3312_, 0, v___x_3315_);
                    v___x_3317_ = v___x_3312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
                    v___x_3317_ = v_reuseFailAlloc_3318_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3317_;
            }
            3 => {
                if v_isShared_3323_ == 0 {
                    v___x_3325_ = v___x_3322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3326_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
                    v___x_3325_ = v_reuseFailAlloc_3326_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg___boxed(
    mut v_a_3328_: *mut crate::leanh::LeanObject,
    mut v_a_3329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3330_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_3328_);
    crate::leanh::lean_dec_ref(v_a_3328_);
    return v_res_3330_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes(
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_3334_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes___boxed(
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3348_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes(
        v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_,
    );
    crate::leanh::lean_dec(v_a_3346_);
    crate::leanh::lean_dec_ref(v_a_3345_);
    crate::leanh::lean_dec(v_a_3344_);
    crate::leanh::lean_dec_ref(v_a_3343_);
    crate::leanh::lean_dec_ref(v_a_3342_);
    crate::leanh::lean_dec(v_a_3341_);
    crate::leanh::lean_dec_ref(v_a_3340_);
    return v_res_3348_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3349_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3349_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3350_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0);
    v___x_3351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3351_, 0, v___x_3350_);
    return v___x_3351_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3352_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1);
    v___x_3353_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3354_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3354_, 0, v___x_3353_);
    crate::leanh::lean_ctor_set(v___x_3354_, 1, v___x_3353_);
    crate::leanh::lean_ctor_set(v___x_3354_, 2, v___x_3353_);
    crate::leanh::lean_ctor_set(v___x_3354_, 3, v___x_3353_);
    crate::leanh::lean_ctor_set(v___x_3354_, 4, v___x_3352_);
    crate::leanh::lean_ctor_set(v___x_3354_, 5, v___x_3352_);
    crate::leanh::lean_ctor_set(v___x_3354_, 6, v___x_3352_);
    crate::leanh::lean_ctor_set(v___x_3354_, 7, v___x_3352_);
    crate::leanh::lean_ctor_set(v___x_3354_, 8, v___x_3352_);
    crate::leanh::lean_ctor_set(v___x_3354_, 9, v___x_3352_);
    return v___x_3354_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
    mut v_msg_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
    mut v___y_3358_: *mut crate::leanh::LeanObject,
    mut v___y_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v_env_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_unused_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3388_: u8 = 0;
    let mut v_a_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3392_: u8 = 0;
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3361_ = crate::leanh::lean_ctor_get(v___y_3358_, 2);
                v_ref_3362_ = crate::leanh::lean_ctor_get(v___y_3358_, 5);
                v___x_3363_ = lean_st_ref_get(v___y_3359_);
                v___x_3364_ = lean_st_ref_get(v___y_3357_);
                v___x_3365_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3356_);
                if crate::leanh::lean_obj_tag(v___x_3365_) == 0 {
                    v_a_3366_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
                    v_isSharedCheck_3388_ = (!crate::leanh::lean_is_exclusive(v___x_3365_)) as u8;
                    if v_isSharedCheck_3388_ == 0 {
                        v___x_3368_ = v___x_3365_;
                        v_isShared_3369_ = v_isSharedCheck_3388_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3366_);
                        crate::leanh::lean_dec(v___x_3365_);
                        v___x_3368_ = crate::leanh::lean_box(0);
                        v_isShared_3369_ = v_isSharedCheck_3388_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3364_);
                    crate::leanh::lean_dec(v___x_3363_);
                    crate::leanh::lean_dec_ref(v_msg_3355_);
                    v_a_3389_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
                    v_isSharedCheck_3396_ = (!crate::leanh::lean_is_exclusive(v___x_3365_)) as u8;
                    if v_isSharedCheck_3396_ == 0 {
                        v___x_3391_ = v___x_3365_;
                        v_isShared_3392_ = v_isSharedCheck_3396_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3389_);
                        crate::leanh::lean_dec(v___x_3365_);
                        v___x_3391_ = crate::leanh::lean_box(0);
                        v_isShared_3392_ = v_isSharedCheck_3396_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3370_ = crate::leanh::lean_ctor_get(v___x_3363_, 0);
                crate::leanh::lean_inc_ref(v_env_3370_);
                crate::leanh::lean_dec(v___x_3363_);
                v_lctx_3371_ = crate::leanh::lean_ctor_get(v___x_3364_, 0);
                v_isSharedCheck_3386_ = (!crate::leanh::lean_is_exclusive(v___x_3364_)) as u8;
                if v_isSharedCheck_3386_ == 0 {
                    v_unused_3387_ = crate::leanh::lean_ctor_get(v___x_3364_, 1);
                    crate::leanh::lean_dec(v_unused_3387_);
                    v___x_3373_ = v___x_3364_;
                    v_isShared_3374_ = v_isSharedCheck_3386_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_3371_);
                    crate::leanh::lean_dec(v___x_3364_);
                    v___x_3373_ = crate::leanh::lean_box(0);
                    v_isShared_3374_ = v_isSharedCheck_3386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3375_ = (crate::leanh::lean_unbox(v_a_3366_) as u8);
                crate::leanh::lean_dec(v_a_3366_);
                v___x_3376_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3371_, v___x_3375_);
                crate::leanh::lean_dec_ref(v_lctx_3371_);
                v___x_3377_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                crate::leanh::lean_inc_ref(v_options_3361_);
                v___x_3378_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3378_, 0, v_env_3370_);
                crate::leanh::lean_ctor_set(v___x_3378_, 1, v___x_3377_);
                crate::leanh::lean_ctor_set(v___x_3378_, 2, v___x_3376_);
                crate::leanh::lean_ctor_set(v___x_3378_, 3, v_options_3361_);
                if v_isShared_3374_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3373_, 3);
                    crate::leanh::lean_ctor_set(v___x_3373_, 1, v_msg_3355_);
                    crate::leanh::lean_ctor_set(v___x_3373_, 0, v___x_3378_);
                    v___x_3380_ = v___x_3373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_msg_3355_);
                    v___x_3380_ = v_reuseFailAlloc_3385_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_ref_3362_);
                v___x_3381_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3381_, 0, v_ref_3362_);
                crate::leanh::lean_ctor_set(v___x_3381_, 1, v___x_3380_);
                if v_isShared_3369_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3368_, 1);
                    crate::leanh::lean_ctor_set(v___x_3368_, 0, v___x_3381_);
                    v___x_3383_ = v___x_3368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
                    v___x_3383_ = v_reuseFailAlloc_3384_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3383_;
            }
            5 => {
                if v_isShared_3392_ == 0 {
                    v___x_3394_ = v___x_3391_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
                    v___x_3394_ = v_reuseFailAlloc_3395_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___boxed(
    mut v_msg_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3403_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
            v_msg_3397_,
            v___y_3398_,
            v___y_3399_,
            v___y_3400_,
            v___y_3401_,
        );
    crate::leanh::lean_dec(v___y_3401_);
    crate::leanh::lean_dec_ref(v___y_3400_);
    crate::leanh::lean_dec(v___y_3399_);
    crate::leanh::lean_dec_ref(v___y_3398_);
    return v_res_3403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1(
    mut v_00_u03b1_3404_: *mut crate::leanh::LeanObject,
    mut v_msg_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
    mut v___y_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
    mut v___y_3410_: *mut crate::leanh::LeanObject,
    mut v___y_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
            v_msg_3405_,
            v___y_3409_,
            v___y_3410_,
            v___y_3411_,
            v___y_3412_,
        );
    return v___x_3414_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___boxed(
    mut v_00_u03b1_3415_: *mut crate::leanh::LeanObject,
    mut v_msg_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
    mut v___y_3419_: *mut crate::leanh::LeanObject,
    mut v___y_3420_: *mut crate::leanh::LeanObject,
    mut v___y_3421_: *mut crate::leanh::LeanObject,
    mut v___y_3422_: *mut crate::leanh::LeanObject,
    mut v___y_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1(
        v_00_u03b1_3415_,
        v_msg_3416_,
        v___y_3417_,
        v___y_3418_,
        v___y_3419_,
        v___y_3420_,
        v___y_3421_,
        v___y_3422_,
        v___y_3423_,
    );
    crate::leanh::lean_dec(v___y_3423_);
    crate::leanh::lean_dec_ref(v___y_3422_);
    crate::leanh::lean_dec(v___y_3421_);
    crate::leanh::lean_dec_ref(v___y_3420_);
    crate::leanh::lean_dec_ref(v___y_3419_);
    crate::leanh::lean_dec(v___y_3418_);
    crate::leanh::lean_dec_ref(v___y_3417_);
    return v_res_3425_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(
    mut v_k_3426_: *mut crate::leanh::LeanObject,
    mut v_t_3427_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3427_) == 0 {
                    v_k_3428_ = crate::leanh::lean_ctor_get(v_t_3427_, 1);
                    v_l_3429_ = crate::leanh::lean_ctor_get(v_t_3427_, 3);
                    v_r_3430_ = crate::leanh::lean_ctor_get(v_t_3427_, 4);
                    v___x_3431_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3426_, v_k_3428_);
                    match v___x_3431_ {
                        0 => {
                            v_t_3427_ = v_l_3429_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_3433_ = 1;
                            return v___x_3433_;
                        }
                        _ => {
                            v_t_3427_ = v_r_3430_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_3435_ = 0;
                    return v___x_3435_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg___boxed(
    mut v_k_3436_: *mut crate::leanh::LeanObject,
    mut v_t_3437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3438_: u8 = 0;
    let mut v_r_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3438_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_k_3436_, v_t_3437_);
    crate::leanh::lean_dec(v_t_3437_);
    crate::leanh::lean_dec(v_k_3436_);
    v_r_3439_ = crate::leanh::lean_box((v_res_3438_) as usize);
    return v_r_3439_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0;
    v___x_3442_ = l_Lean_stringToMessageData(v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFVar(
    mut v_fvarId_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
    mut v_a_3448_: *mut crate::leanh::LeanObject,
    mut v_a_3449_: *mut crate::leanh::LeanObject,
    mut v_a_3450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3463_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_3452_ = crate::leanh::lean_ctor_get(v_a_3444_, 1);
                v___x_3453_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_fvarId_3443_, v_vars_3452_);
                if v___x_3453_ == 0 {
                    v___x_3454_ = l_Lean_Compiler_LCNF_getBinderName(
                        v_fvarId_3443_,
                        v_a_3447_,
                        v_a_3448_,
                        v_a_3449_,
                        v_a_3450_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3454_) == 0 {
                        v_a_3455_ = crate::leanh::lean_ctor_get(v___x_3454_, 0);
                        crate::leanh::lean_inc(v_a_3455_);
                        crate::leanh::lean_dec_ref_known(v___x_3454_, 1);
                        v___x_3456_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1,
                        );
                        v___x_3457_ = l_Lean_MessageData_ofName(v_a_3455_);
                        v___x_3458_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3458_, 0, v___x_3456_);
                        crate::leanh::lean_ctor_set(v___x_3458_, 1, v___x_3457_);
                        v___x_3459_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_3458_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
                        return v___x_3459_;
                    } else {
                        v_a_3460_ = crate::leanh::lean_ctor_get(v___x_3454_, 0);
                        v_isSharedCheck_3467_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3454_)) as u8;
                        if v_isSharedCheck_3467_ == 0 {
                            v___x_3462_ = v___x_3454_;
                            v_isShared_3463_ = v_isSharedCheck_3467_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3460_);
                            crate::leanh::lean_dec(v___x_3454_);
                            v___x_3462_ = crate::leanh::lean_box(0);
                            v_isShared_3463_ = v_isSharedCheck_3467_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_3443_);
                    v___x_3468_ = crate::leanh::lean_box(0);
                    v___x_3469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3469_, 0, v___x_3468_);
                    return v___x_3469_;
                }
            }
            1 => {
                if v_isShared_3463_ == 0 {
                    v___x_3465_ = v___x_3462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
                    v___x_3465_ = v_reuseFailAlloc_3466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFVar___boxed(
    mut v_fvarId_3470_: *mut crate::leanh::LeanObject,
    mut v_a_3471_: *mut crate::leanh::LeanObject,
    mut v_a_3472_: *mut crate::leanh::LeanObject,
    mut v_a_3473_: *mut crate::leanh::LeanObject,
    mut v_a_3474_: *mut crate::leanh::LeanObject,
    mut v_a_3475_: *mut crate::leanh::LeanObject,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
    mut v_a_3477_: *mut crate::leanh::LeanObject,
    mut v_a_3478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3479_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(
        v_fvarId_3470_,
        v_a_3471_,
        v_a_3472_,
        v_a_3473_,
        v_a_3474_,
        v_a_3475_,
        v_a_3476_,
        v_a_3477_,
    );
    crate::leanh::lean_dec(v_a_3477_);
    crate::leanh::lean_dec_ref(v_a_3476_);
    crate::leanh::lean_dec(v_a_3475_);
    crate::leanh::lean_dec_ref(v_a_3474_);
    crate::leanh::lean_dec_ref(v_a_3473_);
    crate::leanh::lean_dec(v_a_3472_);
    crate::leanh::lean_dec_ref(v_a_3471_);
    return v_res_3479_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(
    mut v_00_u03b2_3480_: *mut crate::leanh::LeanObject,
    mut v_k_3481_: *mut crate::leanh::LeanObject,
    mut v_t_3482_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3483_: u8 = 0;
    v___x_3483_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_k_3481_, v_t_3482_);
    return v___x_3483_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___boxed(
    mut v_00_u03b2_3484_: *mut crate::leanh::LeanObject,
    mut v_k_3485_: *mut crate::leanh::LeanObject,
    mut v_t_3486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3487_: u8 = 0;
    let mut v_r_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3487_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(v_00_u03b2_3484_, v_k_3485_, v_t_3486_);
    crate::leanh::lean_dec(v_t_3486_);
    crate::leanh::lean_dec(v_k_3485_);
    v_r_3488_ = crate::leanh::lean_box((v_res_3487_) as usize);
    return v_r_3488_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
    v___x_3491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3491_, 0, v___x_3490_);
    return v___x_3491_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3492_: usize = 0;
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = 5usize;
    v___x_3493_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3494_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3495_ = lean_mk_empty_array_with_capacity(v___x_3494_);
    v___x_3496_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0);
    v___x_3497_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3497_, 0, v___x_3496_);
    crate::leanh::lean_ctor_set(v___x_3497_, 1, v___x_3495_);
    crate::leanh::lean_ctor_set(v___x_3497_, 2, v___x_3493_);
    crate::leanh::lean_ctor_set(v___x_3497_, 3, v___x_3493_);
    crate::leanh::lean_ctor_set_usize(v___x_3497_, 4, v___x_3492_);
    return v___x_3497_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3498_ = crate::leanh::lean_box(1);
    v___x_3499_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_3500_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1);
    v___x_3501_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3501_, 0, v___x_3500_);
    crate::leanh::lean_ctor_set(v___x_3501_, 1, v___x_3499_);
    crate::leanh::lean_ctor_set(v___x_3501_, 2, v___x_3498_);
    return v___x_3501_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
    mut v___y_3504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3506_ = lean_st_ref_get(v___y_3504_);
    v_env_3507_ = crate::leanh::lean_ctor_get(v___x_3506_, 0);
    crate::leanh::lean_inc_ref(v_env_3507_);
    crate::leanh::lean_dec(v___x_3506_);
    v_options_3508_ = crate::leanh::lean_ctor_get(v___y_3503_, 2);
    v___x_3509_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
    v___x_3510_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
    crate::leanh::lean_inc_ref(v_options_3508_);
    v___x_3511_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3511_, 0, v_env_3507_);
    crate::leanh::lean_ctor_set(v___x_3511_, 1, v___x_3509_);
    crate::leanh::lean_ctor_set(v___x_3511_, 2, v___x_3510_);
    crate::leanh::lean_ctor_set(v___x_3511_, 3, v_options_3508_);
    v___x_3512_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3512_, 0, v___x_3511_);
    crate::leanh::lean_ctor_set(v___x_3512_, 1, v_msgData_3502_);
    v___x_3513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3512_);
    return v___x_3513_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_3514_: *mut crate::leanh::LeanObject,
    mut v___y_3515_: *mut crate::leanh::LeanObject,
    mut v___y_3516_: *mut crate::leanh::LeanObject,
    mut v___y_3517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3518_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_3514_, v___y_3515_, v___y_3516_);
    crate::leanh::lean_dec(v___y_3516_);
    crate::leanh::lean_dec_ref(v___y_3515_);
    return v_res_3518_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_3519_: *mut crate::leanh::LeanObject,
    mut v___y_3520_: *mut crate::leanh::LeanObject,
    mut v___y_3521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3523_ = crate::leanh::lean_ctor_get(v___y_3520_, 5);
                v___x_3524_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_3519_, v___y_3520_, v___y_3521_);
                v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                v_isSharedCheck_3533_ = (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                if v_isSharedCheck_3533_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3525_);
                    crate::leanh::lean_dec(v___x_3524_);
                    v___x_3527_ = crate::leanh::lean_box(0);
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3523_);
                v___x_3529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3529_, 0, v_ref_3523_);
                crate::leanh::lean_ctor_set(v___x_3529_, 1, v_a_3525_);
                if v_isShared_3528_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3527_, 1);
                    crate::leanh::lean_ctor_set(v___x_3527_, 0, v___x_3529_);
                    v___x_3531_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
                    v___x_3531_ = v_reuseFailAlloc_3532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_3534_: *mut crate::leanh::LeanObject,
    mut v___y_3535_: *mut crate::leanh::LeanObject,
    mut v___y_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3538_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3534_, v___y_3535_, v___y_3536_);
    crate::leanh::lean_dec(v___y_3536_);
    crate::leanh::lean_dec_ref(v___y_3535_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_3539_: *mut crate::leanh::LeanObject,
    mut v_msg_3540_: *mut crate::leanh::LeanObject,
    mut v___y_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3556_: u8 = 0;
    let mut v_cancelTk_x3f_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3558_: u8 = 0;
    let mut v_inheritedTraceOptions_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3544_ = crate::leanh::lean_ctor_get(v___y_3541_, 0);
    v_fileMap_3545_ = crate::leanh::lean_ctor_get(v___y_3541_, 1);
    v_options_3546_ = crate::leanh::lean_ctor_get(v___y_3541_, 2);
    v_currRecDepth_3547_ = crate::leanh::lean_ctor_get(v___y_3541_, 3);
    v_maxRecDepth_3548_ = crate::leanh::lean_ctor_get(v___y_3541_, 4);
    v_ref_3549_ = crate::leanh::lean_ctor_get(v___y_3541_, 5);
    v_currNamespace_3550_ = crate::leanh::lean_ctor_get(v___y_3541_, 6);
    v_openDecls_3551_ = crate::leanh::lean_ctor_get(v___y_3541_, 7);
    v_initHeartbeats_3552_ = crate::leanh::lean_ctor_get(v___y_3541_, 8);
    v_maxHeartbeats_3553_ = crate::leanh::lean_ctor_get(v___y_3541_, 9);
    v_quotContext_3554_ = crate::leanh::lean_ctor_get(v___y_3541_, 10);
    v_currMacroScope_3555_ = crate::leanh::lean_ctor_get(v___y_3541_, 11);
    v_diag_3556_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3541_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3557_ = crate::leanh::lean_ctor_get(v___y_3541_, 12);
    v_suppressElabErrors_3558_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3541_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3559_ = crate::leanh::lean_ctor_get(v___y_3541_, 13);
    v_ref_3560_ = l_Lean_replaceRef(v_ref_3539_, v_ref_3549_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3559_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3557_);
    crate::leanh::lean_inc(v_currMacroScope_3555_);
    crate::leanh::lean_inc(v_quotContext_3554_);
    crate::leanh::lean_inc(v_maxHeartbeats_3553_);
    crate::leanh::lean_inc(v_initHeartbeats_3552_);
    crate::leanh::lean_inc(v_openDecls_3551_);
    crate::leanh::lean_inc(v_currNamespace_3550_);
    crate::leanh::lean_inc(v_maxRecDepth_3548_);
    crate::leanh::lean_inc(v_currRecDepth_3547_);
    crate::leanh::lean_inc_ref(v_options_3546_);
    crate::leanh::lean_inc_ref(v_fileMap_3545_);
    crate::leanh::lean_inc_ref(v_fileName_3544_);
    v___x_3561_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3561_, 0, v_fileName_3544_);
    crate::leanh::lean_ctor_set(v___x_3561_, 1, v_fileMap_3545_);
    crate::leanh::lean_ctor_set(v___x_3561_, 2, v_options_3546_);
    crate::leanh::lean_ctor_set(v___x_3561_, 3, v_currRecDepth_3547_);
    crate::leanh::lean_ctor_set(v___x_3561_, 4, v_maxRecDepth_3548_);
    crate::leanh::lean_ctor_set(v___x_3561_, 5, v_ref_3560_);
    crate::leanh::lean_ctor_set(v___x_3561_, 6, v_currNamespace_3550_);
    crate::leanh::lean_ctor_set(v___x_3561_, 7, v_openDecls_3551_);
    crate::leanh::lean_ctor_set(v___x_3561_, 8, v_initHeartbeats_3552_);
    crate::leanh::lean_ctor_set(v___x_3561_, 9, v_maxHeartbeats_3553_);
    crate::leanh::lean_ctor_set(v___x_3561_, 10, v_quotContext_3554_);
    crate::leanh::lean_ctor_set(v___x_3561_, 11, v_currMacroScope_3555_);
    crate::leanh::lean_ctor_set(v___x_3561_, 12, v_cancelTk_x3f_3557_);
    crate::leanh::lean_ctor_set(v___x_3561_, 13, v_inheritedTraceOptions_3559_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3561_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3556_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3561_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3558_,
    );
    v___x_3562_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3540_, v___x_3561_, v___y_3542_);
    crate::leanh::lean_dec_ref_known(v___x_3561_, 14);
    return v___x_3562_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_3563_: *mut crate::leanh::LeanObject,
    mut v_msg_3564_: *mut crate::leanh::LeanObject,
    mut v___y_3565_: *mut crate::leanh::LeanObject,
    mut v___y_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3563_, v_msg_3564_, v___y_3565_, v___y_3566_);
    crate::leanh::lean_dec(v___y_3566_);
    crate::leanh::lean_dec_ref(v___y_3565_);
    crate::leanh::lean_dec(v_ref_3563_);
    return v_res_3568_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3570_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_3571_ = l_Lean_stringToMessageData(v___x_3570_);
    return v___x_3571_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3573_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
    v___x_3574_ = l_Lean_stringToMessageData(v___x_3573_);
    return v___x_3574_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3576_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
    v___x_3577_ = l_Lean_stringToMessageData(v___x_3576_);
    return v___x_3577_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3579_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_3580_ = l_Lean_stringToMessageData(v___x_3579_);
    return v___x_3580_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_3583_ = l_Lean_stringToMessageData(v___x_3582_);
    return v___x_3583_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3585_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_3586_ = l_Lean_stringToMessageData(v___x_3585_);
    return v___x_3586_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3588_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_3589_ = l_Lean_stringToMessageData(v___x_3588_);
    return v___x_3589_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_3590_: *mut crate::leanh::LeanObject,
    mut v_declHint_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v_isExporting_3597_: u8 = 0;
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3619_: u8 = 0;
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: u8 = 0;
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3594_ = lean_st_ref_get(v___y_3592_);
                v_env_3595_ = crate::leanh::lean_ctor_get(v___x_3594_, 0);
                crate::leanh::lean_inc_ref(v_env_3595_);
                crate::leanh::lean_dec(v___x_3594_);
                v___x_3596_ = l_Lean_Name_isAnonymous(v_declHint_3591_);
                if v___x_3596_ == 0 {
                    v_isExporting_3597_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_3595_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3597_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_3595_);
                        crate::leanh::lean_dec(v_declHint_3591_);
                        v___x_3598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3598_, 0, v_msg_3590_);
                        return v___x_3598_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_3595_);
                        v___x_3599_ = l_Lean_Environment_setExporting(v_env_3595_, v___x_3596_);
                        crate::leanh::lean_inc(v_declHint_3591_);
                        crate::leanh::lean_inc_ref(v___x_3599_);
                        v___x_3600_ = l_Lean_Environment_contains(
                            v___x_3599_,
                            v_declHint_3591_,
                            v_isExporting_3597_,
                        );
                        if v___x_3600_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3599_);
                            crate::leanh::lean_dec_ref(v_env_3595_);
                            crate::leanh::lean_dec(v_declHint_3591_);
                            v___x_3601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3601_, 0, v_msg_3590_);
                            return v___x_3601_;
                        } else {
                            v___x_3602_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                            v___x_3603_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_3604_ = l_Lean_Options_empty;
                            v___x_3605_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3605_, 0, v___x_3599_);
                            crate::leanh::lean_ctor_set(v___x_3605_, 1, v___x_3602_);
                            crate::leanh::lean_ctor_set(v___x_3605_, 2, v___x_3603_);
                            crate::leanh::lean_ctor_set(v___x_3605_, 3, v___x_3604_);
                            crate::leanh::lean_inc(v_declHint_3591_);
                            v___x_3606_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3591_, v___x_3596_);
                            v_c_3607_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_3607_, 0, v___x_3605_);
                            crate::leanh::lean_ctor_set(v_c_3607_, 1, v___x_3606_);
                            v___x_3608_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3595_,
                                v_declHint_3591_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3608_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_3595_);
                                crate::leanh::lean_dec(v_declHint_3591_);
                                v___x_3609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_3610_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3609_);
                                crate::leanh::lean_ctor_set(v___x_3610_, 1, v_c_3607_);
                                v___x_3611_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_3612_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3612_, 0, v___x_3610_);
                                crate::leanh::lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                                v___x_3613_ = l_Lean_MessageData_note(v___x_3612_);
                                v___x_3614_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3614_, 0, v_msg_3590_);
                                crate::leanh::lean_ctor_set(v___x_3614_, 1, v___x_3613_);
                                v___x_3615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3615_, 0, v___x_3614_);
                                return v___x_3615_;
                            } else {
                                v_val_3616_ = crate::leanh::lean_ctor_get(v___x_3608_, 0);
                                v_isSharedCheck_3651_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3608_)) as u8;
                                if v_isSharedCheck_3651_ == 0 {
                                    v___x_3618_ = v___x_3608_;
                                    v_isShared_3619_ = v_isSharedCheck_3651_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3616_);
                                    crate::leanh::lean_dec(v___x_3608_);
                                    v___x_3618_ = crate::leanh::lean_box(0);
                                    v_isShared_3619_ = v_isSharedCheck_3651_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3595_);
                    crate::leanh::lean_dec(v_declHint_3591_);
                    v___x_3652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3652_, 0, v_msg_3590_);
                    return v___x_3652_;
                }
            }
            1 => {
                v___x_3620_ = crate::leanh::lean_box(0);
                v___x_3621_ = l_Lean_Environment_header(v_env_3595_);
                crate::leanh::lean_dec_ref(v_env_3595_);
                v___x_3622_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3621_);
                v_mod_3623_ = lean_array_get(v___x_3620_, v___x_3622_, v_val_3616_);
                crate::leanh::lean_dec(v_val_3616_);
                crate::leanh::lean_dec_ref(v___x_3622_);
                v___x_3624_ = l_Lean_isPrivateName(v_declHint_3591_);
                crate::leanh::lean_dec(v_declHint_3591_);
                if v___x_3624_ == 0 {
                    v___x_3625_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_3626_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3626_, 0, v___x_3625_);
                    crate::leanh::lean_ctor_set(v___x_3626_, 1, v_c_3607_);
                    v___x_3627_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_3628_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3628_, 0, v___x_3626_);
                    crate::leanh::lean_ctor_set(v___x_3628_, 1, v___x_3627_);
                    v___x_3629_ = l_Lean_MessageData_ofName(v_mod_3623_);
                    v___x_3630_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3630_, 0, v___x_3628_);
                    crate::leanh::lean_ctor_set(v___x_3630_, 1, v___x_3629_);
                    v___x_3631_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_3632_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3632_, 0, v___x_3630_);
                    crate::leanh::lean_ctor_set(v___x_3632_, 1, v___x_3631_);
                    v___x_3633_ = l_Lean_MessageData_note(v___x_3632_);
                    v___x_3634_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3634_, 0, v_msg_3590_);
                    crate::leanh::lean_ctor_set(v___x_3634_, 1, v___x_3633_);
                    if v_isShared_3619_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3618_, 0);
                        crate::leanh::lean_ctor_set(v___x_3618_, 0, v___x_3634_);
                        v___x_3636_ = v___x_3618_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
                        v___x_3636_ = v_reuseFailAlloc_3637_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_3639_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3639_, 0, v___x_3638_);
                    crate::leanh::lean_ctor_set(v___x_3639_, 1, v_c_3607_);
                    v___x_3640_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_3641_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3641_, 0, v___x_3639_);
                    crate::leanh::lean_ctor_set(v___x_3641_, 1, v___x_3640_);
                    v___x_3642_ = l_Lean_MessageData_ofName(v_mod_3623_);
                    v___x_3643_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3643_, 0, v___x_3641_);
                    crate::leanh::lean_ctor_set(v___x_3643_, 1, v___x_3642_);
                    v___x_3644_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_3645_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3645_, 0, v___x_3643_);
                    crate::leanh::lean_ctor_set(v___x_3645_, 1, v___x_3644_);
                    v___x_3646_ = l_Lean_MessageData_note(v___x_3645_);
                    v___x_3647_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3647_, 0, v_msg_3590_);
                    crate::leanh::lean_ctor_set(v___x_3647_, 1, v___x_3646_);
                    if v_isShared_3619_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3618_, 0);
                        crate::leanh::lean_ctor_set(v___x_3618_, 0, v___x_3647_);
                        v___x_3649_ = v___x_3618_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3650_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
                        v___x_3649_ = v_reuseFailAlloc_3650_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3636_;
            }
            3 => {
                return v___x_3649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_3653_: *mut crate::leanh::LeanObject,
    mut v_declHint_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3653_, v_declHint_3654_, v___y_3655_);
    crate::leanh::lean_dec(v___y_3655_);
    return v_res_3657_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_3658_: *mut crate::leanh::LeanObject,
    mut v_declHint_3659_: *mut crate::leanh::LeanObject,
    mut v___y_3660_: *mut crate::leanh::LeanObject,
    mut v___y_3661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3667_: u8 = 0;
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3658_, v_declHint_3659_, v___y_3661_);
                v_a_3664_ = crate::leanh::lean_ctor_get(v___x_3663_, 0);
                v_isSharedCheck_3673_ = (!crate::leanh::lean_is_exclusive(v___x_3663_)) as u8;
                if v_isSharedCheck_3673_ == 0 {
                    v___x_3666_ = v___x_3663_;
                    v_isShared_3667_ = v_isSharedCheck_3673_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3664_);
                    crate::leanh::lean_dec(v___x_3663_);
                    v___x_3666_ = crate::leanh::lean_box(0);
                    v_isShared_3667_ = v_isSharedCheck_3673_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3668_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3669_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3669_, 0, v___x_3668_);
                crate::leanh::lean_ctor_set(v___x_3669_, 1, v_a_3664_);
                if v_isShared_3667_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3666_, 0, v___x_3669_);
                    v___x_3671_ = v___x_3666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
                    v___x_3671_ = v_reuseFailAlloc_3672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3671_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_3674_: *mut crate::leanh::LeanObject,
    mut v_declHint_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3679_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3674_, v_declHint_3675_, v___y_3676_, v___y_3677_);
    crate::leanh::lean_dec(v___y_3677_);
    crate::leanh::lean_dec_ref(v___y_3676_);
    return v_res_3679_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_3680_: *mut crate::leanh::LeanObject,
    mut v_msg_3681_: *mut crate::leanh::LeanObject,
    mut v_declHint_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3686_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3681_, v_declHint_3682_, v___y_3683_, v___y_3684_);
    v_a_3687_ = crate::leanh::lean_ctor_get(v___x_3686_, 0);
    crate::leanh::lean_inc(v_a_3687_);
    crate::leanh::lean_dec_ref(v___x_3686_);
    v___x_3688_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3680_, v_a_3687_, v___y_3683_, v___y_3684_);
    return v___x_3688_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_3689_: *mut crate::leanh::LeanObject,
    mut v_msg_3690_: *mut crate::leanh::LeanObject,
    mut v_declHint_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
    mut v___y_3693_: *mut crate::leanh::LeanObject,
    mut v___y_3694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3689_, v_msg_3690_, v_declHint_3691_, v___y_3692_, v___y_3693_);
    crate::leanh::lean_dec(v___y_3693_);
    crate::leanh::lean_dec_ref(v___y_3692_);
    crate::leanh::lean_dec(v_ref_3689_);
    return v_res_3695_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(
    mut v_ref_3702_: *mut crate::leanh::LeanObject,
    mut v_constName_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u8 = 0;
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3707_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_3708_ = 0;
    crate::leanh::lean_inc(v_constName_3703_);
    v___x_3709_ = l_Lean_MessageData_ofConstName(v_constName_3703_, v___x_3708_);
    v___x_3710_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3710_, 0, v___x_3707_);
    crate::leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
    v___x_3711_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_3712_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3712_, 0, v___x_3710_);
    crate::leanh::lean_ctor_set(v___x_3712_, 1, v___x_3711_);
    v___x_3713_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3702_, v___x_3712_, v_constName_3703_, v___y_3704_, v___y_3705_);
    return v___x_3713_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_3714_: *mut crate::leanh::LeanObject,
    mut v_constName_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3719_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3714_, v_constName_3715_, v___y_3716_, v___y_3717_);
    crate::leanh::lean_dec(v___y_3717_);
    crate::leanh::lean_dec_ref(v___y_3716_);
    crate::leanh::lean_dec(v_ref_3714_);
    return v_res_3719_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(
    mut v_constName_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3724_ = crate::leanh::lean_ctor_get(v___y_3721_, 5);
    v___x_3725_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3724_, v_constName_3720_, v___y_3721_, v___y_3722_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg___boxed(
    mut v_constName_3726_: *mut crate::leanh::LeanObject,
    mut v___y_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3726_, v___y_3727_, v___y_3728_);
    crate::leanh::lean_dec(v___y_3728_);
    crate::leanh::lean_dec_ref(v___y_3727_);
    return v_res_3730_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(
    mut v_constName_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3735_ = lean_st_ref_get(v___y_3733_);
                v_env_3736_ = crate::leanh::lean_ctor_get(v___x_3735_, 0);
                crate::leanh::lean_inc_ref(v_env_3736_);
                crate::leanh::lean_dec(v___x_3735_);
                v___x_3737_ = 0;
                crate::leanh::lean_inc(v_constName_3731_);
                v___x_3738_ =
                    l_Lean_Environment_find_x3f(v_env_3736_, v_constName_3731_, v___x_3737_);
                if crate::leanh::lean_obj_tag(v___x_3738_) == 0 {
                    v___x_3739_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3731_, v___y_3732_, v___y_3733_);
                    return v___x_3739_;
                } else {
                    crate::leanh::lean_dec(v_constName_3731_);
                    v_val_3740_ = crate::leanh::lean_ctor_get(v___x_3738_, 0);
                    v_isSharedCheck_3747_ = (!crate::leanh::lean_is_exclusive(v___x_3738_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3742_ = v___x_3738_;
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3740_);
                        crate::leanh::lean_dec(v___x_3738_);
                        v___x_3742_ = crate::leanh::lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3743_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3742_, 0);
                    v___x_3745_ = v___x_3742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_val_3740_);
                    v___x_3745_ = v_reuseFailAlloc_3746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0___boxed(
    mut v_constName_3748_: *mut crate::leanh::LeanObject,
    mut v___y_3749_: *mut crate::leanh::LeanObject,
    mut v___y_3750_: *mut crate::leanh::LeanObject,
    mut v___y_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(
        v_constName_3748_,
        v___y_3749_,
        v___y_3750_,
    );
    crate::leanh::lean_dec(v___y_3750_);
    crate::leanh::lean_dec_ref(v___y_3749_);
    return v_res_3752_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(
    mut v_f_3753_: *mut crate::leanh::LeanObject,
    mut v_i_3754_: *mut crate::leanh::LeanObject,
    mut v_a_3755_: *mut crate::leanh::LeanObject,
    mut v_a_3756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3763_: u8 = 0;
    let mut v_val_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: u8 = 0;
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_a_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3780_: u8 = 0;
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_f_3753_) == 4 {
                    v_declName_3758_ = crate::leanh::lean_ctor_get(v_f_3753_, 0);
                    crate::leanh::lean_inc(v_declName_3758_);
                    crate::leanh::lean_dec_ref_known(v_f_3753_, 2);
                    v___x_3759_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(v_declName_3758_, v_a_3755_, v_a_3756_);
                    if crate::leanh::lean_obj_tag(v___x_3759_) == 0 {
                        v_a_3760_ = crate::leanh::lean_ctor_get(v___x_3759_, 0);
                        v_isSharedCheck_3776_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3759_)) as u8;
                        if v_isSharedCheck_3776_ == 0 {
                            v___x_3762_ = v___x_3759_;
                            v_isShared_3763_ = v_isSharedCheck_3776_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3760_);
                            crate::leanh::lean_dec(v___x_3759_);
                            v___x_3762_ = crate::leanh::lean_box(0);
                            v_isShared_3763_ = v_isSharedCheck_3776_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3777_ = crate::leanh::lean_ctor_get(v___x_3759_, 0);
                        v_isSharedCheck_3784_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3759_)) as u8;
                        if v_isSharedCheck_3784_ == 0 {
                            v___x_3779_ = v___x_3759_;
                            v_isShared_3780_ = v_isSharedCheck_3784_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3777_);
                            crate::leanh::lean_dec(v___x_3759_);
                            v___x_3779_ = crate::leanh::lean_box(0);
                            v_isShared_3780_ = v_isSharedCheck_3784_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_3753_);
                    v___x_3785_ = 0;
                    v___x_3786_ = crate::leanh::lean_box((v___x_3785_) as usize);
                    v___x_3787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3787_, 0, v___x_3786_);
                    return v___x_3787_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3760_) == 6 {
                    v_val_3764_ = crate::leanh::lean_ctor_get(v_a_3760_, 0);
                    crate::leanh::lean_inc_ref(v_val_3764_);
                    crate::leanh::lean_dec_ref_known(v_a_3760_, 1);
                    v_numParams_3765_ = crate::leanh::lean_ctor_get(v_val_3764_, 3);
                    crate::leanh::lean_inc(v_numParams_3765_);
                    crate::leanh::lean_dec_ref(v_val_3764_);
                    v___x_3766_ = lean_nat_dec_lt(v_i_3754_, v_numParams_3765_);
                    crate::leanh::lean_dec(v_numParams_3765_);
                    v___x_3767_ = crate::leanh::lean_box((v___x_3766_) as usize);
                    if v_isShared_3763_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3762_, 0, v___x_3767_);
                        v___x_3769_ = v___x_3762_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
                        v___x_3769_ = v_reuseFailAlloc_3770_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3760_);
                    v___x_3771_ = 0;
                    v___x_3772_ = crate::leanh::lean_box((v___x_3771_) as usize);
                    if v_isShared_3763_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3762_, 0, v___x_3772_);
                        v___x_3774_ = v___x_3762_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
                        v___x_3774_ = v_reuseFailAlloc_3775_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3769_;
            }
            3 => {
                return v___x_3774_;
            }
            4 => {
                if v_isShared_3780_ == 0 {
                    v___x_3782_ = v___x_3779_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
                    v___x_3782_ = v_reuseFailAlloc_3783_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_isCtorParam___boxed(
    mut v_f_3788_: *mut crate::leanh::LeanObject,
    mut v_i_3789_: *mut crate::leanh::LeanObject,
    mut v_a_3790_: *mut crate::leanh::LeanObject,
    mut v_a_3791_: *mut crate::leanh::LeanObject,
    mut v_a_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3793_ =
        l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(v_f_3788_, v_i_3789_, v_a_3790_, v_a_3791_);
    crate::leanh::lean_dec(v_a_3791_);
    crate::leanh::lean_dec_ref(v_a_3790_);
    crate::leanh::lean_dec(v_i_3789_);
    return v_res_3793_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0(
    mut v_00_u03b1_3794_: *mut crate::leanh::LeanObject,
    mut v_constName_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
    mut v___y_3797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3799_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3795_, v___y_3796_, v___y_3797_);
    return v___x_3799_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___boxed(
    mut v_00_u03b1_3800_: *mut crate::leanh::LeanObject,
    mut v_constName_3801_: *mut crate::leanh::LeanObject,
    mut v___y_3802_: *mut crate::leanh::LeanObject,
    mut v___y_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3805_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0(v_00_u03b1_3800_, v_constName_3801_, v___y_3802_, v___y_3803_);
    crate::leanh::lean_dec(v___y_3803_);
    crate::leanh::lean_dec_ref(v___y_3802_);
    return v_res_3805_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3806_: *mut crate::leanh::LeanObject,
    mut v_ref_3807_: *mut crate::leanh::LeanObject,
    mut v_constName_3808_: *mut crate::leanh::LeanObject,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3807_, v_constName_3808_, v___y_3809_, v___y_3810_);
    return v___x_3812_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3813_: *mut crate::leanh::LeanObject,
    mut v_ref_3814_: *mut crate::leanh::LeanObject,
    mut v_constName_3815_: *mut crate::leanh::LeanObject,
    mut v___y_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3819_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1(v_00_u03b1_3813_, v_ref_3814_, v_constName_3815_, v___y_3816_, v___y_3817_);
    crate::leanh::lean_dec(v___y_3817_);
    crate::leanh::lean_dec_ref(v___y_3816_);
    crate::leanh::lean_dec(v_ref_3814_);
    return v_res_3819_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_3820_: *mut crate::leanh::LeanObject,
    mut v_ref_3821_: *mut crate::leanh::LeanObject,
    mut v_msg_3822_: *mut crate::leanh::LeanObject,
    mut v_declHint_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3821_, v_msg_3822_, v_declHint_3823_, v___y_3824_, v___y_3825_);
    return v___x_3827_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_3828_: *mut crate::leanh::LeanObject,
    mut v_ref_3829_: *mut crate::leanh::LeanObject,
    mut v_msg_3830_: *mut crate::leanh::LeanObject,
    mut v_declHint_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3828_, v_ref_3829_, v_msg_3830_, v_declHint_3831_, v___y_3832_, v___y_3833_);
    crate::leanh::lean_dec(v___y_3833_);
    crate::leanh::lean_dec_ref(v___y_3832_);
    crate::leanh::lean_dec(v_ref_3829_);
    return v_res_3835_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_3836_: *mut crate::leanh::LeanObject,
    mut v_declHint_3837_: *mut crate::leanh::LeanObject,
    mut v___y_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3836_, v_declHint_3837_, v___y_3839_);
    return v___x_3841_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_3842_: *mut crate::leanh::LeanObject,
    mut v_declHint_3843_: *mut crate::leanh::LeanObject,
    mut v___y_3844_: *mut crate::leanh::LeanObject,
    mut v___y_3845_: *mut crate::leanh::LeanObject,
    mut v___y_3846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3842_, v_declHint_3843_, v___y_3844_, v___y_3845_);
    crate::leanh::lean_dec(v___y_3845_);
    crate::leanh::lean_dec_ref(v___y_3844_);
    return v_res_3847_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_3848_: *mut crate::leanh::LeanObject,
    mut v_ref_3849_: *mut crate::leanh::LeanObject,
    mut v_msg_3850_: *mut crate::leanh::LeanObject,
    mut v___y_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3849_, v_msg_3850_, v___y_3851_, v___y_3852_);
    return v___x_3854_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_3855_: *mut crate::leanh::LeanObject,
    mut v_ref_3856_: *mut crate::leanh::LeanObject,
    mut v_msg_3857_: *mut crate::leanh::LeanObject,
    mut v___y_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3855_, v_ref_3856_, v_msg_3857_, v___y_3858_, v___y_3859_);
    crate::leanh::lean_dec(v___y_3859_);
    crate::leanh::lean_dec_ref(v___y_3858_);
    crate::leanh::lean_dec(v_ref_3856_);
    return v_res_3861_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_3862_: *mut crate::leanh::LeanObject,
    mut v_msg_3863_: *mut crate::leanh::LeanObject,
    mut v___y_3864_: *mut crate::leanh::LeanObject,
    mut v___y_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3863_, v___y_3864_, v___y_3865_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_3868_: *mut crate::leanh::LeanObject,
    mut v_msg_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
    mut v___y_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3873_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3868_, v_msg_3869_, v___y_3870_, v___y_3871_);
    crate::leanh::lean_dec(v___y_3871_);
    crate::leanh::lean_dec_ref(v___y_3870_);
    return v_res_3873_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(
    mut v_sz_3874_: usize,
    mut v_i_3875_: usize,
    mut v_bs_3876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3877_: u8 = 0;
    let mut v_v_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: usize = 0;
    let mut v___x_3883_: usize = 0;
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3877_ = lean_usize_dec_lt(v_i_3875_, v_sz_3874_);
                if v___x_3877_ == 0 {
                    return v_bs_3876_;
                } else {
                    v_v_3878_ = lean_array_uget(v_bs_3876_, v_i_3875_);
                    v___x_3879_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3880_ = lean_array_uset(v_bs_3876_, v_i_3875_, v___x_3879_);
                    v___x_3881_ = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v_v_3878_);
                    v___x_3882_ = 1usize;
                    v___x_3883_ = lean_usize_add(v_i_3875_, v___x_3882_);
                    v___x_3884_ = lean_array_uset(v_bs_x27_3880_, v_i_3875_, v___x_3881_);
                    v_i_3875_ = v___x_3883_;
                    v_bs_3876_ = v___x_3884_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0___boxed(
    mut v_sz_3886_: *mut crate::leanh::LeanObject,
    mut v_i_3887_: *mut crate::leanh::LeanObject,
    mut v_bs_3888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3889_: usize = 0;
    let mut v_i_boxed_3890_: usize = 0;
    let mut v_res_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3889_ = crate::leanh::lean_unbox_usize(v_sz_3886_);
    crate::leanh::lean_dec(v_sz_3886_);
    v_i_boxed_3890_ = crate::leanh::lean_unbox_usize(v_i_3887_);
    crate::leanh::lean_dec(v_i_3887_);
    v_res_3891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(v_sz_boxed_3889_, v_i_boxed_3890_, v_bs_3888_);
    return v_res_3891_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0;
    v___x_3894_ = l_Lean_stringToMessageData(v___x_3893_);
    return v___x_3894_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3896_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2;
    v___x_3897_ = l_Lean_stringToMessageData(v___x_3896_);
    return v___x_3897_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3899_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4;
    v___x_3900_ = l_Lean_stringToMessageData(v___x_3899_);
    return v___x_3900_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6;
    v___x_3903_ = l_Lean_stringToMessageData(v___x_3902_);
    return v___x_3903_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(
    mut v___x_3904_: *mut crate::leanh::LeanObject,
    mut v___x_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v_args_3907_: *mut crate::leanh::LeanObject,
    mut v_f_3908_: *mut crate::leanh::LeanObject,
    mut v_____x_3909_: *mut crate::leanh::LeanObject,
    mut v_fType_3910_: *mut crate::leanh::LeanObject,
    mut v_j_3911_: *mut crate::leanh::LeanObject,
    mut v___y_3912_: *mut crate::leanh::LeanObject,
    mut v___y_3913_: *mut crate::leanh::LeanObject,
    mut v___y_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
    mut v___y_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v___x_3935_: u8 = 0;
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: u8 = 0;
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3943_: usize = 0;
    let mut v___x_3944_: usize = 0;
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut v_a_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_a_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_a_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3920_ = crate::leanh::lean_ctor_get(v_____x_3909_, 0);
                v_snd_3921_ = crate::leanh::lean_ctor_get(v_____x_3909_, 1);
                v_isSharedCheck_3995_ = (!crate::leanh::lean_is_exclusive(v_____x_3909_)) as u8;
                if v_isSharedCheck_3995_ == 0 {
                    v___x_3923_ = v_____x_3909_;
                    v_isShared_3924_ = v_isSharedCheck_3995_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3921_);
                    crate::leanh::lean_inc(v_fst_3920_);
                    crate::leanh::lean_dec(v_____x_3909_);
                    v___x_3923_ = crate::leanh::lean_box(0);
                    v_isShared_3924_ = v_isSharedCheck_3995_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3932_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v___y_3915_);
                if crate::leanh::lean_obj_tag(v___x_3932_) == 0 {
                    v_a_3933_ = crate::leanh::lean_ctor_get(v___x_3932_, 0);
                    crate::leanh::lean_inc(v_a_3933_);
                    crate::leanh::lean_dec_ref_known(v___x_3932_, 1);
                    v___x_3934_ = (crate::leanh::lean_unbox(v_a_3933_) as u8);
                    crate::leanh::lean_dec(v_a_3933_);
                    if v___x_3934_ == 0 {
                        crate::leanh::lean_dec(v_fst_3920_);
                        crate::leanh::lean_dec_ref(v_f_3908_);
                        crate::leanh::lean_dec_ref(v_args_3907_);
                        crate::leanh::lean_dec(v___x_3905_);
                        state = 2;
                        continue;
                    } else {
                        v___x_3935_ = 0;
                        crate::leanh::lean_inc(v___x_3905_);
                        v___x_3936_ = l_Lean_Compiler_LCNF_Arg_inferType(
                            v___x_3935_,
                            v___x_3905_,
                            v___y_3915_,
                            v___y_3916_,
                            v___y_3917_,
                            v___y_3918_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3936_) == 0 {
                            v_a_3937_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                            crate::leanh::lean_inc_n(v_a_3937_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_3936_, 1);
                            crate::leanh::lean_inc_ref(v_args_3907_);
                            v___x_3938_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(
                                v_fst_3920_,
                                v_j_3911_,
                                v_a_3906_,
                                v_args_3907_,
                            );
                            crate::leanh::lean_dec(v_fst_3920_);
                            crate::leanh::lean_inc_ref(v___x_3938_);
                            v___x_3939_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_a_3937_,
                                v___x_3938_,
                                v___y_3914_,
                                v___y_3915_,
                                v___y_3916_,
                                v___y_3917_,
                                v___y_3918_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3939_) == 0 {
                                v_a_3940_ = crate::leanh::lean_ctor_get(v___x_3939_, 0);
                                crate::leanh::lean_inc(v_a_3940_);
                                crate::leanh::lean_dec_ref_known(v___x_3939_, 1);
                                v___x_3941_ = (crate::leanh::lean_unbox(v_a_3940_) as u8);
                                crate::leanh::lean_dec(v_a_3940_);
                                if v___x_3941_ == 0 {
                                    v___x_3942_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1);
                                    v_sz_3943_ = lean_array_size(v_args_3907_);
                                    v___x_3944_ = 0usize;
                                    v___x_3945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(v_sz_3943_, v___x_3944_, v_args_3907_);
                                    v___x_3946_ = l_Lean_mkAppN(v_f_3908_, v___x_3945_);
                                    crate::leanh::lean_dec_ref(v___x_3945_);
                                    v___x_3947_ = l_Lean_indentExpr(v___x_3946_);
                                    v___x_3948_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3948_, 0, v___x_3942_);
                                    crate::leanh::lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                                    v___x_3949_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3);
                                    v___x_3950_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                                    crate::leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                                    v___x_3951_ =
                                        l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v___x_3905_);
                                    v___x_3952_ = l_Lean_MessageData_ofExpr(v___x_3951_);
                                    v___x_3953_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3953_, 0, v___x_3950_);
                                    crate::leanh::lean_ctor_set(v___x_3953_, 1, v___x_3952_);
                                    v___x_3954_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5);
                                    v___x_3955_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3955_, 0, v___x_3953_);
                                    crate::leanh::lean_ctor_set(v___x_3955_, 1, v___x_3954_);
                                    v___x_3956_ = l_Lean_indentExpr(v_a_3937_);
                                    v___x_3957_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3957_, 0, v___x_3955_);
                                    crate::leanh::lean_ctor_set(v___x_3957_, 1, v___x_3956_);
                                    v___x_3958_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                                    v___x_3959_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3959_, 0, v___x_3957_);
                                    crate::leanh::lean_ctor_set(v___x_3959_, 1, v___x_3958_);
                                    v___x_3960_ = l_Lean_indentExpr(v___x_3938_);
                                    v___x_3961_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_3959_);
                                    crate::leanh::lean_ctor_set(v___x_3961_, 1, v___x_3960_);
                                    v___x_3962_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_3961_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
                                    if crate::leanh::lean_obj_tag(v___x_3962_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3962_, 1);
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_del_object(v___x_3923_);
                                        crate::leanh::lean_dec(v_snd_3921_);
                                        crate::leanh::lean_dec(v_j_3911_);
                                        crate::leanh::lean_dec(v___x_3904_);
                                        v_a_3963_ = crate::leanh::lean_ctor_get(v___x_3962_, 0);
                                        v_isSharedCheck_3970_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3962_)) as u8;
                                        if v_isSharedCheck_3970_ == 0 {
                                            v___x_3965_ = v___x_3962_;
                                            v_isShared_3966_ = v_isSharedCheck_3970_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3963_);
                                            crate::leanh::lean_dec(v___x_3962_);
                                            v___x_3965_ = crate::leanh::lean_box(0);
                                            v_isShared_3966_ = v_isSharedCheck_3970_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3938_);
                                    crate::leanh::lean_dec(v_a_3937_);
                                    crate::leanh::lean_dec_ref(v_f_3908_);
                                    crate::leanh::lean_dec_ref(v_args_3907_);
                                    crate::leanh::lean_dec(v___x_3905_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3938_);
                                crate::leanh::lean_dec(v_a_3937_);
                                crate::leanh::lean_del_object(v___x_3923_);
                                crate::leanh::lean_dec(v_snd_3921_);
                                crate::leanh::lean_dec(v_j_3911_);
                                crate::leanh::lean_dec_ref(v_f_3908_);
                                crate::leanh::lean_dec_ref(v_args_3907_);
                                crate::leanh::lean_dec(v___x_3905_);
                                crate::leanh::lean_dec(v___x_3904_);
                                v_a_3971_ = crate::leanh::lean_ctor_get(v___x_3939_, 0);
                                v_isSharedCheck_3978_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3939_)) as u8;
                                if v_isSharedCheck_3978_ == 0 {
                                    v___x_3973_ = v___x_3939_;
                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3971_);
                                    crate::leanh::lean_dec(v___x_3939_);
                                    v___x_3973_ = crate::leanh::lean_box(0);
                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3923_);
                            crate::leanh::lean_dec(v_snd_3921_);
                            crate::leanh::lean_dec(v_fst_3920_);
                            crate::leanh::lean_dec(v_j_3911_);
                            crate::leanh::lean_dec_ref(v_f_3908_);
                            crate::leanh::lean_dec_ref(v_args_3907_);
                            crate::leanh::lean_dec(v___x_3905_);
                            crate::leanh::lean_dec(v___x_3904_);
                            v_a_3979_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                            v_isSharedCheck_3986_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3936_)) as u8;
                            if v_isSharedCheck_3986_ == 0 {
                                v___x_3981_ = v___x_3936_;
                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3979_);
                                crate::leanh::lean_dec(v___x_3936_);
                                v___x_3981_ = crate::leanh::lean_box(0);
                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3923_);
                    crate::leanh::lean_dec(v_snd_3921_);
                    crate::leanh::lean_dec(v_fst_3920_);
                    crate::leanh::lean_dec(v_j_3911_);
                    crate::leanh::lean_dec_ref(v_f_3908_);
                    crate::leanh::lean_dec_ref(v_args_3907_);
                    crate::leanh::lean_dec(v___x_3905_);
                    crate::leanh::lean_dec(v___x_3904_);
                    v_a_3987_ = crate::leanh::lean_ctor_get(v___x_3932_, 0);
                    v_isSharedCheck_3994_ = (!crate::leanh::lean_is_exclusive(v___x_3932_)) as u8;
                    if v_isSharedCheck_3994_ == 0 {
                        v___x_3989_ = v___x_3932_;
                        v_isShared_3990_ = v_isSharedCheck_3994_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3987_);
                        crate::leanh::lean_dec(v___x_3932_);
                        v___x_3989_ = crate::leanh::lean_box(0);
                        v_isShared_3990_ = v_isSharedCheck_3994_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3924_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3923_, 1, v_j_3911_);
                    crate::leanh::lean_ctor_set(v___x_3923_, 0, v_snd_3921_);
                    v___x_3927_ = v___x_3923_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_snd_3921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_j_3911_);
                    v___x_3927_ = v_reuseFailAlloc_3931_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3928_, 0, v___x_3904_);
                crate::leanh::lean_ctor_set(v___x_3928_, 1, v___x_3927_);
                v___x_3929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                v___x_3930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3930_, 0, v___x_3929_);
                return v___x_3930_;
            }
            4 => {
                if v_isShared_3966_ == 0 {
                    v___x_3968_ = v___x_3965_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
                    v___x_3968_ = v_reuseFailAlloc_3969_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3968_;
            }
            6 => {
                if v_isShared_3974_ == 0 {
                    v___x_3976_ = v___x_3973_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
                    v___x_3976_ = v_reuseFailAlloc_3977_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3976_;
            }
            8 => {
                if v_isShared_3982_ == 0 {
                    v___x_3984_ = v___x_3981_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
                    v___x_3984_ = v_reuseFailAlloc_3985_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3984_;
            }
            10 => {
                if v_isShared_3990_ == 0 {
                    v___x_3992_ = v___x_3989_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
                    v___x_3992_ = v_reuseFailAlloc_3993_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___boxed(
    mut v___x_3996_: *mut crate::leanh::LeanObject,
    mut v___x_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
    mut v_args_3999_: *mut crate::leanh::LeanObject,
    mut v_f_4000_: *mut crate::leanh::LeanObject,
    mut v_____x_4001_: *mut crate::leanh::LeanObject,
    mut v_fType_4002_: *mut crate::leanh::LeanObject,
    mut v_j_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4012_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_3996_, v___x_3997_, v_a_3998_, v_args_3999_, v_f_4000_, v_____x_4001_, v_fType_4002_, v_j_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
    crate::leanh::lean_dec(v___y_4010_);
    crate::leanh::lean_dec_ref(v___y_4009_);
    crate::leanh::lean_dec(v___y_4008_);
    crate::leanh::lean_dec_ref(v___y_4007_);
    crate::leanh::lean_dec_ref(v___y_4006_);
    crate::leanh::lean_dec(v___y_4005_);
    crate::leanh::lean_dec_ref(v___y_4004_);
    crate::leanh::lean_dec_ref(v_fType_4002_);
    crate::leanh::lean_dec(v_a_3998_);
    return v_res_4012_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(
    mut v_upperBound_4015_: *mut crate::leanh::LeanObject,
    mut v_args_4016_: *mut crate::leanh::LeanObject,
    mut v_f_4017_: *mut crate::leanh::LeanObject,
    mut v_a_4018_: *mut crate::leanh::LeanObject,
    mut v_b_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v_a_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v_a_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4050_: u8 = 0;
    let mut v___x_4051_: u8 = 0;
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v_fst_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_unused_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4051_ = lean_nat_dec_lt(v_a_4018_, v_upperBound_4015_);
                if v___x_4051_ == 0 {
                    crate::leanh::lean_dec(v_a_4018_);
                    crate::leanh::lean_dec_ref(v_f_4017_);
                    crate::leanh::lean_dec_ref(v_args_4016_);
                    v___x_4052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4052_, 0, v_b_4019_);
                    return v___x_4052_;
                } else {
                    v_snd_4053_ = crate::leanh::lean_ctor_get(v_b_4019_, 1);
                    v_isSharedCheck_4097_ = (!crate::leanh::lean_is_exclusive(v_b_4019_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v_unused_4098_ = crate::leanh::lean_ctor_get(v_b_4019_, 0);
                        crate::leanh::lean_dec(v_unused_4098_);
                        v___x_4055_ = v_b_4019_;
                        v_isShared_4056_ = v_isSharedCheck_4097_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4053_);
                        crate::leanh::lean_dec(v_b_4019_);
                        v___x_4055_ = crate::leanh::lean_box(0);
                        v_isShared_4056_ = v_isSharedCheck_4097_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4029_) == 0 {
                    v_a_4030_ = crate::leanh::lean_ctor_get(v___y_4029_, 0);
                    v_isSharedCheck_4042_ = (!crate::leanh::lean_is_exclusive(v___y_4029_)) as u8;
                    if v_isSharedCheck_4042_ == 0 {
                        v___x_4032_ = v___y_4029_;
                        v_isShared_4033_ = v_isSharedCheck_4042_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4030_);
                        crate::leanh::lean_dec(v___y_4029_);
                        v___x_4032_ = crate::leanh::lean_box(0);
                        v_isShared_4033_ = v_isSharedCheck_4042_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4018_);
                    crate::leanh::lean_dec_ref(v_f_4017_);
                    crate::leanh::lean_dec_ref(v_args_4016_);
                    v_a_4043_ = crate::leanh::lean_ctor_get(v___y_4029_, 0);
                    v_isSharedCheck_4050_ = (!crate::leanh::lean_is_exclusive(v___y_4029_)) as u8;
                    if v_isSharedCheck_4050_ == 0 {
                        v___x_4045_ = v___y_4029_;
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4043_);
                        crate::leanh::lean_dec(v___y_4029_);
                        v___x_4045_ = crate::leanh::lean_box(0);
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4030_) == 0 {
                    crate::leanh::lean_dec(v_a_4018_);
                    crate::leanh::lean_dec_ref(v_f_4017_);
                    crate::leanh::lean_dec_ref(v_args_4016_);
                    v_a_4034_ = crate::leanh::lean_ctor_get(v_a_4030_, 0);
                    crate::leanh::lean_inc(v_a_4034_);
                    crate::leanh::lean_dec_ref_known(v_a_4030_, 1);
                    if v_isShared_4033_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4032_, 0, v_a_4034_);
                        v___x_4036_ = v___x_4032_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4034_);
                        v___x_4036_ = v_reuseFailAlloc_4037_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4032_);
                    v_a_4038_ = crate::leanh::lean_ctor_get(v_a_4030_, 0);
                    crate::leanh::lean_inc(v_a_4038_);
                    crate::leanh::lean_dec_ref_known(v_a_4030_, 1);
                    v___x_4039_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4040_ = lean_nat_add(v_a_4018_, v___x_4039_);
                    crate::leanh::lean_dec(v_a_4018_);
                    v_a_4018_ = v___x_4040_;
                    v_b_4019_ = v_a_4038_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_4036_;
            }
            4 => {
                if v_isShared_4046_ == 0 {
                    v___x_4048_ = v___x_4045_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
                    v___x_4048_ = v_reuseFailAlloc_4049_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4048_;
            }
            6 => {
                v_fst_4057_ = crate::leanh::lean_ctor_get(v_snd_4053_, 0);
                v_snd_4058_ = crate::leanh::lean_ctor_get(v_snd_4053_, 1);
                v_isSharedCheck_4096_ = (!crate::leanh::lean_is_exclusive(v_snd_4053_)) as u8;
                if v_isSharedCheck_4096_ == 0 {
                    v___x_4060_ = v_snd_4053_;
                    v_isShared_4061_ = v_isSharedCheck_4096_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4058_);
                    crate::leanh::lean_inc(v_fst_4057_);
                    crate::leanh::lean_dec(v_snd_4053_);
                    v___x_4060_ = crate::leanh::lean_box(0);
                    v_isShared_4061_ = v_isSharedCheck_4096_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4062_ = l_Lean_Expr_isErased(v_fst_4057_);
                if v___x_4062_ == 0 {
                    v___x_4063_ = crate::leanh::lean_box(0);
                    v___x_4064_ = lean_array_fget_borrowed(v_args_4016_, v_a_4018_);
                    v___x_4065_ = l_Lean_Expr_headBeta(v_fst_4057_);
                    if crate::leanh::lean_obj_tag(v___x_4065_) == 7 {
                        crate::leanh::lean_del_object(v___x_4055_);
                        v_binderType_4066_ = crate::leanh::lean_ctor_get(v___x_4065_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_4066_);
                        v_body_4067_ = crate::leanh::lean_ctor_get(v___x_4065_, 2);
                        crate::leanh::lean_inc_ref(v_body_4067_);
                        if v_isShared_4061_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4060_, 1, v_body_4067_);
                            crate::leanh::lean_ctor_set(v___x_4060_, 0, v_binderType_4066_);
                            v___x_4069_ = v___x_4060_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4071_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4071_,
                                0,
                                v_binderType_4066_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_body_4067_);
                            v___x_4069_ = v_reuseFailAlloc_4071_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_args_4016_);
                        v___x_4072_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(
                            v___x_4065_,
                            v_snd_4058_,
                            v_a_4018_,
                            v_args_4016_,
                        );
                        crate::leanh::lean_dec_ref(v___x_4065_);
                        v___x_4073_ = l_Lean_Expr_headBeta(v___x_4072_);
                        if crate::leanh::lean_obj_tag(v___x_4073_) == 7 {
                            crate::leanh::lean_dec(v_snd_4058_);
                            crate::leanh::lean_del_object(v___x_4055_);
                            v_binderType_4074_ = crate::leanh::lean_ctor_get(v___x_4073_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_4074_);
                            v_body_4075_ = crate::leanh::lean_ctor_get(v___x_4073_, 2);
                            crate::leanh::lean_inc_ref(v_body_4075_);
                            if v_isShared_4061_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4060_, 1, v_body_4075_);
                                crate::leanh::lean_ctor_set(v___x_4060_, 0, v_binderType_4074_);
                                v___x_4077_ = v___x_4060_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_4079_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4079_,
                                    0,
                                    v_binderType_4074_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4079_,
                                    1,
                                    v_body_4075_,
                                );
                                v___x_4077_ = v_reuseFailAlloc_4079_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4018_);
                            crate::leanh::lean_dec_ref(v_f_4017_);
                            crate::leanh::lean_dec_ref(v_args_4016_);
                            v___x_4080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0;
                            if v_isShared_4061_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4060_, 0, v___x_4073_);
                                v___x_4082_ = v___x_4060_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4087_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4073_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_snd_4058_);
                                v___x_4082_ = v_reuseFailAlloc_4087_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4018_);
                    crate::leanh::lean_dec_ref(v_f_4017_);
                    crate::leanh::lean_dec_ref(v_args_4016_);
                    v___x_4088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0;
                    if v_isShared_4061_ == 0 {
                        v___x_4090_ = v___x_4060_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4095_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_fst_4057_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_snd_4058_);
                        v___x_4090_ = v_reuseFailAlloc_4095_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v_f_4017_);
                crate::leanh::lean_inc_ref(v_args_4016_);
                crate::leanh::lean_inc(v___x_4064_);
                v___x_4070_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_4063_, v___x_4064_, v_a_4018_, v_args_4016_, v_f_4017_, v___x_4069_, v___x_4065_, v_snd_4058_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
                crate::leanh::lean_dec_ref_known(v___x_4065_, 3);
                v___y_4029_ = v___x_4070_;
                state = 1;
                continue;
            }
            9 => {
                crate::leanh::lean_inc_ref(v_f_4017_);
                crate::leanh::lean_inc_ref(v_args_4016_);
                crate::leanh::lean_inc(v_a_4018_);
                crate::leanh::lean_inc(v___x_4064_);
                v___x_4078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_4063_, v___x_4064_, v_a_4018_, v_args_4016_, v_f_4017_, v___x_4077_, v___x_4073_, v_a_4018_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
                crate::leanh::lean_dec_ref_known(v___x_4073_, 3);
                v___y_4029_ = v___x_4078_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_4056_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4055_, 1, v___x_4082_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 0, v___x_4080_);
                    v___x_4084_ = v___x_4055_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4082_);
                    v___x_4084_ = v_reuseFailAlloc_4086_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4085_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4085_, 0, v___x_4084_);
                return v___x_4085_;
            }
            12 => {
                if v_isShared_4056_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4055_, 1, v___x_4090_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 0, v___x_4088_);
                    v___x_4092_ = v___x_4055_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4090_);
                    v___x_4092_ = v_reuseFailAlloc_4094_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4093_, 0, v___x_4092_);
                return v___x_4093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___boxed(
    mut v_upperBound_4099_: *mut crate::leanh::LeanObject,
    mut v_args_4100_: *mut crate::leanh::LeanObject,
    mut v_f_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v_b_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v_upperBound_4099_, v_args_4100_, v_f_4101_, v_a_4102_, v_b_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    crate::leanh::lean_dec(v___y_4110_);
    crate::leanh::lean_dec_ref(v___y_4109_);
    crate::leanh::lean_dec(v___y_4108_);
    crate::leanh::lean_dec_ref(v___y_4107_);
    crate::leanh::lean_dec_ref(v___y_4106_);
    crate::leanh::lean_dec(v___y_4105_);
    crate::leanh::lean_dec_ref(v___y_4104_);
    crate::leanh::lean_dec(v_upperBound_4099_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(
    mut v_f_4113_: *mut crate::leanh::LeanObject,
    mut v_args_4114_: *mut crate::leanh::LeanObject,
    mut v_a_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
    mut v_a_4117_: *mut crate::leanh::LeanObject,
    mut v_a_4118_: *mut crate::leanh::LeanObject,
    mut v_a_4119_: *mut crate::leanh::LeanObject,
    mut v_a_4120_: *mut crate::leanh::LeanObject,
    mut v_a_4121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4134_: u8 = 0;
    let mut v_fst_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4144_: u8 = 0;
    let mut v_a_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4152_: u8 = 0;
    let mut v_a_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4156_: u8 = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_f_4113_);
                v___x_4123_ = l_Lean_Compiler_LCNF_inferType(
                    v_f_4113_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_,
                );
                if crate::leanh::lean_obj_tag(v___x_4123_) == 0 {
                    v_a_4124_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                    crate::leanh::lean_inc(v_a_4124_);
                    crate::leanh::lean_dec_ref_known(v___x_4123_, 1);
                    v___x_4125_ = lean_array_get_size(v_args_4114_);
                    v___x_4126_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4127_ = crate::leanh::lean_box(0);
                    v___x_4128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4128_, 0, v_a_4124_);
                    crate::leanh::lean_ctor_set(v___x_4128_, 1, v___x_4126_);
                    v___x_4129_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4129_, 0, v___x_4127_);
                    crate::leanh::lean_ctor_set(v___x_4129_, 1, v___x_4128_);
                    v___x_4130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v___x_4125_, v_args_4114_, v_f_4113_, v___x_4126_, v___x_4129_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
                    if crate::leanh::lean_obj_tag(v___x_4130_) == 0 {
                        v_a_4131_ = crate::leanh::lean_ctor_get(v___x_4130_, 0);
                        v_isSharedCheck_4144_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4130_)) as u8;
                        if v_isSharedCheck_4144_ == 0 {
                            v___x_4133_ = v___x_4130_;
                            v_isShared_4134_ = v_isSharedCheck_4144_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4131_);
                            crate::leanh::lean_dec(v___x_4130_);
                            v___x_4133_ = crate::leanh::lean_box(0);
                            v_isShared_4134_ = v_isSharedCheck_4144_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4145_ = crate::leanh::lean_ctor_get(v___x_4130_, 0);
                        v_isSharedCheck_4152_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4130_)) as u8;
                        if v_isSharedCheck_4152_ == 0 {
                            v___x_4147_ = v___x_4130_;
                            v_isShared_4148_ = v_isSharedCheck_4152_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4145_);
                            crate::leanh::lean_dec(v___x_4130_);
                            v___x_4147_ = crate::leanh::lean_box(0);
                            v_isShared_4148_ = v_isSharedCheck_4152_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_4114_);
                    crate::leanh::lean_dec_ref(v_f_4113_);
                    v_a_4153_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                    v_isSharedCheck_4160_ = (!crate::leanh::lean_is_exclusive(v___x_4123_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4155_ = v___x_4123_;
                        v_isShared_4156_ = v_isSharedCheck_4160_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4153_);
                        crate::leanh::lean_dec(v___x_4123_);
                        v___x_4155_ = crate::leanh::lean_box(0);
                        v_isShared_4156_ = v_isSharedCheck_4160_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4135_ = crate::leanh::lean_ctor_get(v_a_4131_, 0);
                crate::leanh::lean_inc(v_fst_4135_);
                crate::leanh::lean_dec(v_a_4131_);
                if crate::leanh::lean_obj_tag(v_fst_4135_) == 0 {
                    v___x_4136_ = crate::leanh::lean_box(0);
                    if v_isShared_4134_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4133_, 0, v___x_4136_);
                        v___x_4138_ = v___x_4133_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
                        v___x_4138_ = v_reuseFailAlloc_4139_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_4140_ = crate::leanh::lean_ctor_get(v_fst_4135_, 0);
                    crate::leanh::lean_inc(v_val_4140_);
                    crate::leanh::lean_dec_ref_known(v_fst_4135_, 1);
                    if v_isShared_4134_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4133_, 0, v_val_4140_);
                        v___x_4142_ = v___x_4133_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_val_4140_);
                        v___x_4142_ = v_reuseFailAlloc_4143_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4138_;
            }
            3 => {
                return v___x_4142_;
            }
            4 => {
                if v_isShared_4148_ == 0 {
                    v___x_4150_ = v___x_4147_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4151_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
                    v___x_4150_ = v_reuseFailAlloc_4151_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4150_;
            }
            6 => {
                if v_isShared_4156_ == 0 {
                    v___x_4158_ = v___x_4155_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
                    v___x_4158_ = v_reuseFailAlloc_4159_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs___boxed(
    mut v_f_4161_: *mut crate::leanh::LeanObject,
    mut v_args_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: *mut crate::leanh::LeanObject,
    mut v_a_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
    mut v_a_4169_: *mut crate::leanh::LeanObject,
    mut v_a_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4171_ = l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(
        v_f_4161_,
        v_args_4162_,
        v_a_4163_,
        v_a_4164_,
        v_a_4165_,
        v_a_4166_,
        v_a_4167_,
        v_a_4168_,
        v_a_4169_,
    );
    crate::leanh::lean_dec(v_a_4169_);
    crate::leanh::lean_dec_ref(v_a_4168_);
    crate::leanh::lean_dec(v_a_4167_);
    crate::leanh::lean_dec_ref(v_a_4166_);
    crate::leanh::lean_dec_ref(v_a_4165_);
    crate::leanh::lean_dec(v_a_4164_);
    crate::leanh::lean_dec_ref(v_a_4163_);
    return v_res_4171_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1(
    mut v_upperBound_4172_: *mut crate::leanh::LeanObject,
    mut v_args_4173_: *mut crate::leanh::LeanObject,
    mut v_f_4174_: *mut crate::leanh::LeanObject,
    mut v_inst_4175_: *mut crate::leanh::LeanObject,
    mut v_R_4176_: *mut crate::leanh::LeanObject,
    mut v_a_4177_: *mut crate::leanh::LeanObject,
    mut v_b_4178_: *mut crate::leanh::LeanObject,
    mut v_c_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v_upperBound_4172_, v_args_4173_, v_f_4174_, v_a_4177_, v_b_4178_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
    return v___x_4188_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___boxed(
    mut v_upperBound_4189_: *mut crate::leanh::LeanObject,
    mut v_args_4190_: *mut crate::leanh::LeanObject,
    mut v_f_4191_: *mut crate::leanh::LeanObject,
    mut v_inst_4192_: *mut crate::leanh::LeanObject,
    mut v_R_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
    mut v_b_4195_: *mut crate::leanh::LeanObject,
    mut v_c_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4205_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1(
            v_upperBound_4189_,
            v_args_4190_,
            v_f_4191_,
            v_inst_4192_,
            v_R_4193_,
            v_a_4194_,
            v_b_4195_,
            v_c_4196_,
            v___y_4197_,
            v___y_4198_,
            v___y_4199_,
            v___y_4200_,
            v___y_4201_,
            v___y_4202_,
            v___y_4203_,
        );
    crate::leanh::lean_dec(v___y_4203_);
    crate::leanh::lean_dec_ref(v___y_4202_);
    crate::leanh::lean_dec(v___y_4201_);
    crate::leanh::lean_dec_ref(v___y_4200_);
    crate::leanh::lean_dec_ref(v___y_4199_);
    crate::leanh::lean_dec(v___y_4198_);
    crate::leanh::lean_dec_ref(v___y_4197_);
    crate::leanh::lean_dec(v_upperBound_4189_);
    return v_res_4205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(
    mut v_e_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
    mut v_a_4212_: *mut crate::leanh::LeanObject,
    mut v_a_4213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4222_: u8 = 0;
    let mut v_unused_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_4206_) {
                0 => {
                    v_isSharedCheck_4222_ = (!crate::leanh::lean_is_exclusive(v_e_4206_)) as u8;
                    if v_isSharedCheck_4222_ == 0 {
                        v_unused_4223_ = crate::leanh::lean_ctor_get(v_e_4206_, 0);
                        crate::leanh::lean_dec(v_unused_4223_);
                        v___x_4216_ = v_e_4206_;
                        v_isShared_4217_ = v_isSharedCheck_4222_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_e_4206_);
                        v___x_4216_ = crate::leanh::lean_box(0);
                        v_isShared_4217_ = v_isSharedCheck_4222_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4224_ = crate::leanh::lean_box(0);
                    v___x_4225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4225_, 0, v___x_4224_);
                    return v___x_4225_;
                }
                2 => {
                    v_struct_4226_ = crate::leanh::lean_ctor_get(v_e_4206_, 2);
                    crate::leanh::lean_inc(v_struct_4226_);
                    crate::leanh::lean_dec_ref_known(v_e_4206_, 3);
                    v___x_4227_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(
                        v_struct_4226_,
                        v_a_4207_,
                        v_a_4208_,
                        v_a_4209_,
                        v_a_4210_,
                        v_a_4211_,
                        v_a_4212_,
                        v_a_4213_,
                    );
                    return v___x_4227_;
                }
                3 => {
                    v_declName_4228_ = crate::leanh::lean_ctor_get(v_e_4206_, 0);
                    crate::leanh::lean_inc(v_declName_4228_);
                    v_us_4229_ = crate::leanh::lean_ctor_get(v_e_4206_, 1);
                    crate::leanh::lean_inc(v_us_4229_);
                    v_args_4230_ = crate::leanh::lean_ctor_get(v_e_4206_, 2);
                    crate::leanh::lean_inc_ref(v_args_4230_);
                    crate::leanh::lean_dec_ref_known(v_e_4206_, 3);
                    v___x_4231_ = l_Lean_mkConst(v_declName_4228_, v_us_4229_);
                    v___x_4232_ = l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(
                        v___x_4231_,
                        v_args_4230_,
                        v_a_4207_,
                        v_a_4208_,
                        v_a_4209_,
                        v_a_4210_,
                        v_a_4211_,
                        v_a_4212_,
                        v_a_4213_,
                    );
                    return v___x_4232_;
                }
                _ => {
                    v_fvarId_4233_ = crate::leanh::lean_ctor_get(v_e_4206_, 0);
                    crate::leanh::lean_inc_n(v_fvarId_4233_, 2);
                    v_args_4234_ = crate::leanh::lean_ctor_get(v_e_4206_, 1);
                    crate::leanh::lean_inc_ref(v_args_4234_);
                    crate::leanh::lean_dec_ref_known(v_e_4206_, 2);
                    v___x_4235_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(
                        v_fvarId_4233_,
                        v_a_4207_,
                        v_a_4208_,
                        v_a_4209_,
                        v_a_4210_,
                        v_a_4211_,
                        v_a_4212_,
                        v_a_4213_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4235_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4235_, 1);
                        v___x_4236_ = l_Lean_Expr_fvar___override(v_fvarId_4233_);
                        v___x_4237_ = l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(
                            v___x_4236_,
                            v_args_4234_,
                            v_a_4207_,
                            v_a_4208_,
                            v_a_4209_,
                            v_a_4210_,
                            v_a_4211_,
                            v_a_4212_,
                            v_a_4213_,
                        );
                        return v___x_4237_;
                    } else {
                        crate::leanh::lean_dec_ref(v_args_4234_);
                        crate::leanh::lean_dec(v_fvarId_4233_);
                        return v___x_4235_;
                    }
                }
            },
            1 => {
                v___x_4218_ = crate::leanh::lean_box(0);
                if v_isShared_4217_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4216_, 0, v___x_4218_);
                    v___x_4220_ = v___x_4216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4218_);
                    v___x_4220_ = v_reuseFailAlloc_4221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkLetValue___boxed(
    mut v_e_4238_: *mut crate::leanh::LeanObject,
    mut v_a_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
    mut v_a_4241_: *mut crate::leanh::LeanObject,
    mut v_a_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
    mut v_a_4244_: *mut crate::leanh::LeanObject,
    mut v_a_4245_: *mut crate::leanh::LeanObject,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4247_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(
        v_e_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_,
    );
    crate::leanh::lean_dec(v_a_4245_);
    crate::leanh::lean_dec_ref(v_a_4244_);
    crate::leanh::lean_dec(v_a_4243_);
    crate::leanh::lean_dec_ref(v_a_4242_);
    crate::leanh::lean_dec_ref(v_a_4241_);
    crate::leanh::lean_dec(v_a_4240_);
    crate::leanh::lean_dec_ref(v_a_4239_);
    return v_res_4247_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4249_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0;
    v___x_4250_ = l_Lean_stringToMessageData(v___x_4249_);
    return v___x_4250_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
    mut v_jp_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_jps_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: u8 = 0;
    v_jps_4258_ = crate::leanh::lean_ctor_get(v_a_4252_, 0);
    v___x_4259_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_jp_4251_, v_jps_4258_);
    if v___x_4259_ == 0 {
        let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4260_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1_once
            ),
            _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1,
        );
        v___x_4261_ = l_Lean_mkFVar(v_jp_4251_);
        v___x_4262_ = l_Lean_MessageData_ofExpr(v___x_4261_);
        v___x_4263_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4263_, 0, v___x_4260_);
        crate::leanh::lean_ctor_set(v___x_4263_, 1, v___x_4262_);
        v___x_4264_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
        v___x_4265_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4265_, 0, v___x_4263_);
        crate::leanh::lean_ctor_set(v___x_4265_, 1, v___x_4264_);
        v___x_4266_ =
            l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
                v___x_4265_,
                v_a_4253_,
                v_a_4254_,
                v_a_4255_,
                v_a_4256_,
            );
        return v___x_4266_;
    } else {
        let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_jp_4251_);
        v___x_4267_ = crate::leanh::lean_box(0);
        v___x_4268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4268_, 0, v___x_4267_);
        return v___x_4268_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___boxed(
    mut v_jp_4269_: *mut crate::leanh::LeanObject,
    mut v_a_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
    mut v_a_4274_: *mut crate::leanh::LeanObject,
    mut v_a_4275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4276_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
        v_jp_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_,
    );
    crate::leanh::lean_dec(v_a_4274_);
    crate::leanh::lean_dec_ref(v_a_4273_);
    crate::leanh::lean_dec(v_a_4272_);
    crate::leanh::lean_dec_ref(v_a_4271_);
    crate::leanh::lean_dec_ref(v_a_4270_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(
    mut v_jp_4277_: *mut crate::leanh::LeanObject,
    mut v_a_4278_: *mut crate::leanh::LeanObject,
    mut v_a_4279_: *mut crate::leanh::LeanObject,
    mut v_a_4280_: *mut crate::leanh::LeanObject,
    mut v_a_4281_: *mut crate::leanh::LeanObject,
    mut v_a_4282_: *mut crate::leanh::LeanObject,
    mut v_a_4283_: *mut crate::leanh::LeanObject,
    mut v_a_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
        v_jp_4277_, v_a_4278_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_,
    );
    return v___x_4286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___boxed(
    mut v_jp_4287_: *mut crate::leanh::LeanObject,
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v_a_4289_: *mut crate::leanh::LeanObject,
    mut v_a_4290_: *mut crate::leanh::LeanObject,
    mut v_a_4291_: *mut crate::leanh::LeanObject,
    mut v_a_4292_: *mut crate::leanh::LeanObject,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
    mut v_a_4294_: *mut crate::leanh::LeanObject,
    mut v_a_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4296_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(
        v_jp_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_,
    );
    crate::leanh::lean_dec(v_a_4294_);
    crate::leanh::lean_dec_ref(v_a_4293_);
    crate::leanh::lean_dec(v_a_4292_);
    crate::leanh::lean_dec_ref(v_a_4291_);
    crate::leanh::lean_dec_ref(v_a_4290_);
    crate::leanh::lean_dec(v_a_4289_);
    crate::leanh::lean_dec_ref(v_a_4288_);
    return v_res_4296_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4298_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0;
    v___x_4299_ = l_Lean_stringToMessageData(v___x_4298_);
    return v___x_4299_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4301_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2;
    v___x_4302_ = l_Lean_stringToMessageData(v___x_4301_);
    return v___x_4302_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
    mut v_param_4303_: *mut crate::leanh::LeanObject,
    mut v_a_4304_: *mut crate::leanh::LeanObject,
    mut v_a_4305_: *mut crate::leanh::LeanObject,
    mut v_a_4306_: *mut crate::leanh::LeanObject,
    mut v_a_4307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4317_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4309_ = crate::leanh::lean_ctor_get(v_param_4303_, 0);
                v_binderName_4310_ = crate::leanh::lean_ctor_get(v_param_4303_, 1);
                crate::leanh::lean_inc(v_binderName_4310_);
                v___x_4311_ = 0;
                crate::leanh::lean_inc(v_fvarId_4309_);
                v___x_4312_ = l_Lean_Compiler_LCNF_getParam(
                    v___x_4311_,
                    v_fvarId_4309_,
                    v_a_4304_,
                    v_a_4305_,
                    v_a_4306_,
                    v_a_4307_,
                );
                if crate::leanh::lean_obj_tag(v___x_4312_) == 0 {
                    v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4328_ = (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4315_ = v___x_4312_;
                        v_isShared_4316_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4313_);
                        crate::leanh::lean_dec(v___x_4312_);
                        v___x_4315_ = crate::leanh::lean_box(0);
                        v_isShared_4316_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_binderName_4310_);
                    crate::leanh::lean_dec_ref(v_param_4303_);
                    v_a_4329_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4336_ = (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4331_ = v___x_4312_;
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4329_);
                        crate::leanh::lean_dec(v___x_4312_);
                        v___x_4331_ = crate::leanh::lean_box(0);
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4317_ =
                    l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(v_param_4303_, v_a_4313_);
                crate::leanh::lean_dec(v_a_4313_);
                crate::leanh::lean_dec_ref(v_param_4303_);
                if v___x_4317_ == 0 {
                    crate::leanh::lean_del_object(v___x_4315_);
                    v___x_4318_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1,
                    );
                    v___x_4319_ = l_Lean_MessageData_ofName(v_binderName_4310_);
                    v___x_4320_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4320_, 0, v___x_4318_);
                    crate::leanh::lean_ctor_set(v___x_4320_, 1, v___x_4319_);
                    v___x_4321_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3,
                    );
                    v___x_4322_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4322_, 0, v___x_4320_);
                    crate::leanh::lean_ctor_set(v___x_4322_, 1, v___x_4321_);
                    v___x_4323_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4322_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_);
                    return v___x_4323_;
                } else {
                    crate::leanh::lean_dec(v_binderName_4310_);
                    v___x_4324_ = crate::leanh::lean_box(0);
                    if v_isShared_4316_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4315_, 0, v___x_4324_);
                        v___x_4326_ = v___x_4315_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
                        v___x_4326_ = v_reuseFailAlloc_4327_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4326_;
            }
            3 => {
                if v_isShared_4332_ == 0 {
                    v___x_4334_ = v___x_4331_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
                    v___x_4334_ = v_reuseFailAlloc_4335_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___boxed(
    mut v_param_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
    mut v_a_4342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4343_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
        v_param_4337_,
        v_a_4338_,
        v_a_4339_,
        v_a_4340_,
        v_a_4341_,
    );
    crate::leanh::lean_dec(v_a_4341_);
    crate::leanh::lean_dec_ref(v_a_4340_);
    crate::leanh::lean_dec(v_a_4339_);
    crate::leanh::lean_dec_ref(v_a_4338_);
    return v_res_4343_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParam(
    mut v_param_4344_: *mut crate::leanh::LeanObject,
    mut v_a_4345_: *mut crate::leanh::LeanObject,
    mut v_a_4346_: *mut crate::leanh::LeanObject,
    mut v_a_4347_: *mut crate::leanh::LeanObject,
    mut v_a_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
        v_param_4344_,
        v_a_4348_,
        v_a_4349_,
        v_a_4350_,
        v_a_4351_,
    );
    return v___x_4353_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParam___boxed(
    mut v_param_4354_: *mut crate::leanh::LeanObject,
    mut v_a_4355_: *mut crate::leanh::LeanObject,
    mut v_a_4356_: *mut crate::leanh::LeanObject,
    mut v_a_4357_: *mut crate::leanh::LeanObject,
    mut v_a_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4363_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam(
        v_param_4354_,
        v_a_4355_,
        v_a_4356_,
        v_a_4357_,
        v_a_4358_,
        v_a_4359_,
        v_a_4360_,
        v_a_4361_,
    );
    crate::leanh::lean_dec(v_a_4361_);
    crate::leanh::lean_dec_ref(v_a_4360_);
    crate::leanh::lean_dec(v_a_4359_);
    crate::leanh::lean_dec_ref(v_a_4358_);
    crate::leanh::lean_dec_ref(v_a_4357_);
    crate::leanh::lean_dec(v_a_4356_);
    crate::leanh::lean_dec_ref(v_a_4355_);
    return v_res_4363_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(
    mut v_as_4364_: *mut crate::leanh::LeanObject,
    mut v_i_4365_: usize,
    mut v_stop_4366_: usize,
    mut v_b_4367_: *mut crate::leanh::LeanObject,
    mut v___y_4368_: *mut crate::leanh::LeanObject,
    mut v___y_4369_: *mut crate::leanh::LeanObject,
    mut v___y_4370_: *mut crate::leanh::LeanObject,
    mut v___y_4371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: usize = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4373_ = lean_usize_dec_eq(v_i_4365_, v_stop_4366_);
                if v___x_4373_ == 0 {
                    v___x_4374_ = lean_array_uget_borrowed(v_as_4364_, v_i_4365_);
                    crate::leanh::lean_inc(v___x_4374_);
                    v___x_4375_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
                        v___x_4374_,
                        v___y_4368_,
                        v___y_4369_,
                        v___y_4370_,
                        v___y_4371_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4375_) == 0 {
                        v_a_4376_ = crate::leanh::lean_ctor_get(v___x_4375_, 0);
                        crate::leanh::lean_inc(v_a_4376_);
                        crate::leanh::lean_dec_ref_known(v___x_4375_, 1);
                        v___x_4377_ = 1usize;
                        v___x_4378_ = lean_usize_add(v_i_4365_, v___x_4377_);
                        v_i_4365_ = v___x_4378_;
                        v_b_4367_ = v_a_4376_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4375_;
                    }
                } else {
                    v___x_4380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4380_, 0, v_b_4367_);
                    return v___x_4380_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg___boxed(
    mut v_as_4381_: *mut crate::leanh::LeanObject,
    mut v_i_4382_: *mut crate::leanh::LeanObject,
    mut v_stop_4383_: *mut crate::leanh::LeanObject,
    mut v_b_4384_: *mut crate::leanh::LeanObject,
    mut v___y_4385_: *mut crate::leanh::LeanObject,
    mut v___y_4386_: *mut crate::leanh::LeanObject,
    mut v___y_4387_: *mut crate::leanh::LeanObject,
    mut v___y_4388_: *mut crate::leanh::LeanObject,
    mut v___y_4389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4390_: usize = 0;
    let mut v_stop_boxed_4391_: usize = 0;
    let mut v_res_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4390_ = crate::leanh::lean_unbox_usize(v_i_4382_);
    crate::leanh::lean_dec(v_i_4382_);
    v_stop_boxed_4391_ = crate::leanh::lean_unbox_usize(v_stop_4383_);
    crate::leanh::lean_dec(v_stop_4383_);
    v_res_4392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_as_4381_, v_i_boxed_4390_, v_stop_boxed_4391_, v_b_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
    crate::leanh::lean_dec(v___y_4388_);
    crate::leanh::lean_dec_ref(v___y_4387_);
    crate::leanh::lean_dec(v___y_4386_);
    crate::leanh::lean_dec_ref(v___y_4385_);
    crate::leanh::lean_dec_ref(v_as_4381_);
    return v_res_4392_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParams(
    mut v_params_4393_: *mut crate::leanh::LeanObject,
    mut v_a_4394_: *mut crate::leanh::LeanObject,
    mut v_a_4395_: *mut crate::leanh::LeanObject,
    mut v_a_4396_: *mut crate::leanh::LeanObject,
    mut v_a_4397_: *mut crate::leanh::LeanObject,
    mut v_a_4398_: *mut crate::leanh::LeanObject,
    mut v_a_4399_: *mut crate::leanh::LeanObject,
    mut v_a_4400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: u8 = 0;
    v___x_4402_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4403_ = lean_array_get_size(v_params_4393_);
    v___x_4404_ = crate::leanh::lean_box(0);
    v___x_4405_ = lean_nat_dec_lt(v___x_4402_, v___x_4403_);
    if v___x_4405_ == 0 {
        let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4406_, 0, v___x_4404_);
        return v___x_4406_;
    } else {
        let mut v___x_4407_: u8 = 0;
        v___x_4407_ = lean_nat_dec_le(v___x_4403_, v___x_4403_);
        if v___x_4407_ == 0 {
            if v___x_4405_ == 0 {
                let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4408_, 0, v___x_4404_);
                return v___x_4408_;
            } else {
                let mut v___x_4409_: usize = 0;
                let mut v___x_4410_: usize = 0;
                let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4409_ = 0usize;
                v___x_4410_ = lean_usize_of_nat(v___x_4403_);
                v___x_4411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_params_4393_, v___x_4409_, v___x_4410_, v___x_4404_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
                return v___x_4411_;
            }
        } else {
            let mut v___x_4412_: usize = 0;
            let mut v___x_4413_: usize = 0;
            let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4412_ = 0usize;
            v___x_4413_ = lean_usize_of_nat(v___x_4403_);
            v___x_4414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_params_4393_, v___x_4412_, v___x_4413_, v___x_4404_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
            return v___x_4414_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParams___boxed(
    mut v_params_4415_: *mut crate::leanh::LeanObject,
    mut v_a_4416_: *mut crate::leanh::LeanObject,
    mut v_a_4417_: *mut crate::leanh::LeanObject,
    mut v_a_4418_: *mut crate::leanh::LeanObject,
    mut v_a_4419_: *mut crate::leanh::LeanObject,
    mut v_a_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_Lean_Compiler_LCNF_Check_Pure_checkParams(
        v_params_4415_,
        v_a_4416_,
        v_a_4417_,
        v_a_4418_,
        v_a_4419_,
        v_a_4420_,
        v_a_4421_,
        v_a_4422_,
    );
    crate::leanh::lean_dec(v_a_4422_);
    crate::leanh::lean_dec_ref(v_a_4421_);
    crate::leanh::lean_dec(v_a_4420_);
    crate::leanh::lean_dec_ref(v_a_4419_);
    crate::leanh::lean_dec_ref(v_a_4418_);
    crate::leanh::lean_dec(v_a_4417_);
    crate::leanh::lean_dec_ref(v_a_4416_);
    crate::leanh::lean_dec_ref(v_params_4415_);
    return v_res_4424_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(
    mut v_as_4425_: *mut crate::leanh::LeanObject,
    mut v_i_4426_: usize,
    mut v_stop_4427_: usize,
    mut v_b_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
    mut v___y_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_as_4425_, v_i_4426_, v_stop_4427_, v_b_4428_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
    return v___x_4437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___boxed(
    mut v_as_4438_: *mut crate::leanh::LeanObject,
    mut v_i_4439_: *mut crate::leanh::LeanObject,
    mut v_stop_4440_: *mut crate::leanh::LeanObject,
    mut v_b_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
    mut v___y_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
    mut v___y_4446_: *mut crate::leanh::LeanObject,
    mut v___y_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4450_: usize = 0;
    let mut v_stop_boxed_4451_: usize = 0;
    let mut v_res_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4450_ = crate::leanh::lean_unbox_usize(v_i_4439_);
    crate::leanh::lean_dec(v_i_4439_);
    v_stop_boxed_4451_ = crate::leanh::lean_unbox_usize(v_stop_4440_);
    crate::leanh::lean_dec(v_stop_4440_);
    v_res_4452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(v_as_4438_, v_i_boxed_4450_, v_stop_boxed_4451_, v_b_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
    crate::leanh::lean_dec(v___y_4448_);
    crate::leanh::lean_dec_ref(v___y_4447_);
    crate::leanh::lean_dec(v___y_4446_);
    crate::leanh::lean_dec_ref(v___y_4445_);
    crate::leanh::lean_dec_ref(v___y_4444_);
    crate::leanh::lean_dec(v___y_4443_);
    crate::leanh::lean_dec_ref(v___y_4442_);
    crate::leanh::lean_dec_ref(v_as_4438_);
    return v_res_4452_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4454_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0;
    v___x_4455_ = l_Lean_stringToMessageData(v___x_4454_);
    return v___x_4455_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4457_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2;
    v___x_4458_ = l_Lean_stringToMessageData(v___x_4457_);
    return v___x_4458_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4;
    v___x_4461_ = l_Lean_stringToMessageData(v___x_4460_);
    return v___x_4461_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6;
    v___x_4464_ = l_Lean_stringToMessageData(v___x_4463_);
    return v___x_4464_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(
    mut v_letDecl_4465_: *mut crate::leanh::LeanObject,
    mut v_a_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4488_: u8 = 0;
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut v_a_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4504_: u8 = 0;
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4508_: u8 = 0;
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u8 = 0;
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: u8 = 0;
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_a_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4542_: u8 = 0;
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v_a_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4550_: u8 = 0;
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4474_ = crate::leanh::lean_ctor_get(v_letDecl_4465_, 0);
                v_binderName_4475_ = crate::leanh::lean_ctor_get(v_letDecl_4465_, 1);
                crate::leanh::lean_inc(v_binderName_4475_);
                v_type_4476_ = crate::leanh::lean_ctor_get(v_letDecl_4465_, 2);
                v_value_4477_ = crate::leanh::lean_ctor_get(v_letDecl_4465_, 3);
                crate::leanh::lean_inc(v_value_4477_);
                v___x_4509_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(
                    v_value_4477_,
                    v_a_4466_,
                    v_a_4467_,
                    v_a_4468_,
                    v_a_4469_,
                    v_a_4470_,
                    v_a_4471_,
                    v_a_4472_,
                );
                if crate::leanh::lean_obj_tag(v___x_4509_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4509_, 1);
                    v___x_4510_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_4469_);
                    if crate::leanh::lean_obj_tag(v___x_4510_) == 0 {
                        v_a_4511_ = crate::leanh::lean_ctor_get(v___x_4510_, 0);
                        crate::leanh::lean_inc(v_a_4511_);
                        crate::leanh::lean_dec_ref_known(v___x_4510_, 1);
                        v___x_4512_ = (crate::leanh::lean_unbox(v_a_4511_) as u8);
                        crate::leanh::lean_dec(v_a_4511_);
                        if v___x_4512_ == 0 {
                            v___y_4479_ = v_a_4469_;
                            v___y_4480_ = v_a_4470_;
                            v___y_4481_ = v_a_4471_;
                            v___y_4482_ = v_a_4472_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4513_ = 0;
                            crate::leanh::lean_inc(v_value_4477_);
                            v___x_4514_ = l_Lean_Compiler_LCNF_LetValue_inferType(
                                v___x_4513_,
                                v_value_4477_,
                                v_a_4469_,
                                v_a_4470_,
                                v_a_4471_,
                                v_a_4472_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4514_) == 0 {
                                v_a_4515_ = crate::leanh::lean_ctor_get(v___x_4514_, 0);
                                crate::leanh::lean_inc_n(v_a_4515_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_4514_, 1);
                                crate::leanh::lean_inc_ref(v_type_4476_);
                                v___x_4516_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                    v_type_4476_,
                                    v_a_4515_,
                                    v_a_4468_,
                                    v_a_4469_,
                                    v_a_4470_,
                                    v_a_4471_,
                                    v_a_4472_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4516_) == 0 {
                                    v_a_4517_ = crate::leanh::lean_ctor_get(v___x_4516_, 0);
                                    crate::leanh::lean_inc(v_a_4517_);
                                    crate::leanh::lean_dec_ref_known(v___x_4516_, 1);
                                    v___x_4518_ = (crate::leanh::lean_unbox(v_a_4517_) as u8);
                                    crate::leanh::lean_dec(v_a_4517_);
                                    if v___x_4518_ == 0 {
                                        crate::leanh::lean_inc_ref(v_type_4476_);
                                        crate::leanh::lean_dec_ref(v_letDecl_4465_);
                                        v___x_4519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once), _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5);
                                        v___x_4520_ = l_Lean_MessageData_ofName(v_binderName_4475_);
                                        v___x_4521_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4521_, 0, v___x_4519_);
                                        crate::leanh::lean_ctor_set(v___x_4521_, 1, v___x_4520_);
                                        v___x_4522_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once), _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7);
                                        v___x_4523_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4523_, 0, v___x_4521_);
                                        crate::leanh::lean_ctor_set(v___x_4523_, 1, v___x_4522_);
                                        v___x_4524_ = l_Lean_indentExpr(v_a_4515_);
                                        v___x_4525_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4525_, 0, v___x_4523_);
                                        crate::leanh::lean_ctor_set(v___x_4525_, 1, v___x_4524_);
                                        v___x_4526_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                                        v___x_4527_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4527_, 0, v___x_4525_);
                                        crate::leanh::lean_ctor_set(v___x_4527_, 1, v___x_4526_);
                                        v___x_4528_ = l_Lean_indentExpr(v_type_4476_);
                                        v___x_4529_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4529_, 0, v___x_4527_);
                                        crate::leanh::lean_ctor_set(v___x_4529_, 1, v___x_4528_);
                                        v___x_4530_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4529_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
                                        return v___x_4530_;
                                    } else {
                                        crate::leanh::lean_dec(v_a_4515_);
                                        v___y_4479_ = v_a_4469_;
                                        v___y_4480_ = v_a_4470_;
                                        v___y_4481_ = v_a_4471_;
                                        v___y_4482_ = v_a_4472_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4515_);
                                    crate::leanh::lean_dec(v_binderName_4475_);
                                    crate::leanh::lean_dec_ref(v_letDecl_4465_);
                                    v_a_4531_ = crate::leanh::lean_ctor_get(v___x_4516_, 0);
                                    v_isSharedCheck_4538_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4516_)) as u8;
                                    if v_isSharedCheck_4538_ == 0 {
                                        v___x_4533_ = v___x_4516_;
                                        v_isShared_4534_ = v_isSharedCheck_4538_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4531_);
                                        crate::leanh::lean_dec(v___x_4516_);
                                        v___x_4533_ = crate::leanh::lean_box(0);
                                        v_isShared_4534_ = v_isSharedCheck_4538_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_binderName_4475_);
                                crate::leanh::lean_dec_ref(v_letDecl_4465_);
                                v_a_4539_ = crate::leanh::lean_ctor_get(v___x_4514_, 0);
                                v_isSharedCheck_4546_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4514_)) as u8;
                                if v_isSharedCheck_4546_ == 0 {
                                    v___x_4541_ = v___x_4514_;
                                    v_isShared_4542_ = v_isSharedCheck_4546_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4539_);
                                    crate::leanh::lean_dec(v___x_4514_);
                                    v___x_4541_ = crate::leanh::lean_box(0);
                                    v_isShared_4542_ = v_isSharedCheck_4546_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_4475_);
                        crate::leanh::lean_dec_ref(v_letDecl_4465_);
                        v_a_4547_ = crate::leanh::lean_ctor_get(v___x_4510_, 0);
                        v_isSharedCheck_4554_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4510_)) as u8;
                        if v_isSharedCheck_4554_ == 0 {
                            v___x_4549_ = v___x_4510_;
                            v_isShared_4550_ = v_isSharedCheck_4554_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4547_);
                            crate::leanh::lean_dec(v___x_4510_);
                            v___x_4549_ = crate::leanh::lean_box(0);
                            v_isShared_4550_ = v_isSharedCheck_4554_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_binderName_4475_);
                    crate::leanh::lean_dec_ref(v_letDecl_4465_);
                    return v___x_4509_;
                }
            }
            1 => {
                v___x_4483_ = 0;
                crate::leanh::lean_inc(v_fvarId_4474_);
                v___x_4484_ = l_Lean_Compiler_LCNF_getLetDecl(
                    v___x_4483_,
                    v_fvarId_4474_,
                    v___y_4479_,
                    v___y_4480_,
                    v___y_4481_,
                    v___y_4482_,
                );
                if crate::leanh::lean_obj_tag(v___x_4484_) == 0 {
                    v_a_4485_ = crate::leanh::lean_ctor_get(v___x_4484_, 0);
                    v_isSharedCheck_4500_ = (!crate::leanh::lean_is_exclusive(v___x_4484_)) as u8;
                    if v_isSharedCheck_4500_ == 0 {
                        v___x_4487_ = v___x_4484_;
                        v_isShared_4488_ = v_isSharedCheck_4500_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4485_);
                        crate::leanh::lean_dec(v___x_4484_);
                        v___x_4487_ = crate::leanh::lean_box(0);
                        v_isShared_4488_ = v_isSharedCheck_4500_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_binderName_4475_);
                    crate::leanh::lean_dec_ref(v_letDecl_4465_);
                    v_a_4501_ = crate::leanh::lean_ctor_get(v___x_4484_, 0);
                    v_isSharedCheck_4508_ = (!crate::leanh::lean_is_exclusive(v___x_4484_)) as u8;
                    if v_isSharedCheck_4508_ == 0 {
                        v___x_4503_ = v___x_4484_;
                        v_isShared_4504_ = v_isSharedCheck_4508_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4501_);
                        crate::leanh::lean_dec(v___x_4484_);
                        v___x_4503_ = crate::leanh::lean_box(0);
                        v_isShared_4504_ = v_isSharedCheck_4508_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4489_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(
                    v___x_4483_,
                    v_letDecl_4465_,
                    v_a_4485_,
                );
                crate::leanh::lean_dec(v_a_4485_);
                crate::leanh::lean_dec_ref(v_letDecl_4465_);
                if v___x_4489_ == 0 {
                    crate::leanh::lean_del_object(v___x_4487_);
                    v___x_4490_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1,
                    );
                    v___x_4491_ = l_Lean_MessageData_ofName(v_binderName_4475_);
                    v___x_4492_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4492_, 0, v___x_4490_);
                    crate::leanh::lean_ctor_set(v___x_4492_, 1, v___x_4491_);
                    v___x_4493_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3,
                    );
                    v___x_4494_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4494_, 0, v___x_4492_);
                    crate::leanh::lean_ctor_set(v___x_4494_, 1, v___x_4493_);
                    v___x_4495_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4494_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
                    return v___x_4495_;
                } else {
                    crate::leanh::lean_dec(v_binderName_4475_);
                    v___x_4496_ = crate::leanh::lean_box(0);
                    if v_isShared_4488_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4487_, 0, v___x_4496_);
                        v___x_4498_ = v___x_4487_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
                        v___x_4498_ = v_reuseFailAlloc_4499_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4498_;
            }
            4 => {
                if v_isShared_4504_ == 0 {
                    v___x_4506_ = v___x_4503_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
                    v___x_4506_ = v_reuseFailAlloc_4507_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4506_;
            }
            6 => {
                if v_isShared_4534_ == 0 {
                    v___x_4536_ = v___x_4533_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
                    v___x_4536_ = v_reuseFailAlloc_4537_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4536_;
            }
            8 => {
                if v_isShared_4542_ == 0 {
                    v___x_4544_ = v___x_4541_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
                    v___x_4544_ = v_reuseFailAlloc_4545_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4544_;
            }
            10 => {
                if v_isShared_4550_ == 0 {
                    v___x_4552_ = v___x_4549_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
                    v___x_4552_ = v_reuseFailAlloc_4553_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4552_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___boxed(
    mut v_letDecl_4555_: *mut crate::leanh::LeanObject,
    mut v_a_4556_: *mut crate::leanh::LeanObject,
    mut v_a_4557_: *mut crate::leanh::LeanObject,
    mut v_a_4558_: *mut crate::leanh::LeanObject,
    mut v_a_4559_: *mut crate::leanh::LeanObject,
    mut v_a_4560_: *mut crate::leanh::LeanObject,
    mut v_a_4561_: *mut crate::leanh::LeanObject,
    mut v_a_4562_: *mut crate::leanh::LeanObject,
    mut v_a_4563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4564_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(
        v_letDecl_4555_,
        v_a_4556_,
        v_a_4557_,
        v_a_4558_,
        v_a_4559_,
        v_a_4560_,
        v_a_4561_,
        v_a_4562_,
    );
    crate::leanh::lean_dec(v_a_4562_);
    crate::leanh::lean_dec_ref(v_a_4561_);
    crate::leanh::lean_dec(v_a_4560_);
    crate::leanh::lean_dec_ref(v_a_4559_);
    crate::leanh::lean_dec_ref(v_a_4558_);
    crate::leanh::lean_dec(v_a_4557_);
    crate::leanh::lean_dec_ref(v_a_4556_);
    return v_res_4564_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(
    mut v_a_4565_: *mut crate::leanh::LeanObject,
    mut v_x_4566_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4567_: u8 = 0;
    let mut v_key_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4566_) == 0 {
                    v___x_4567_ = 0;
                    return v___x_4567_;
                } else {
                    v_key_4568_ = crate::leanh::lean_ctor_get(v_x_4566_, 0);
                    v_tail_4569_ = crate::leanh::lean_ctor_get(v_x_4566_, 2);
                    v___x_4570_ = l_Lean_instBEqFVarId_beq(v_key_4568_, v_a_4565_);
                    if v___x_4570_ == 0 {
                        v_x_4566_ = v_tail_4569_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4570_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg___boxed(
    mut v_a_4572_: *mut crate::leanh::LeanObject,
    mut v_x_4573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4574_: u8 = 0;
    let mut v_r_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_4572_, v_x_4573_);
    crate::leanh::lean_dec(v_x_4573_);
    crate::leanh::lean_dec(v_a_4572_);
    v_r_4575_ = crate::leanh::lean_box((v_res_4574_) as usize);
    return v_r_4575_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_4576_: *mut crate::leanh::LeanObject,
    mut v_x_4577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: u64 = 0;
    let mut v___x_4586_: u64 = 0;
    let mut v___x_4587_: u64 = 0;
    let mut v_fold_4588_: u64 = 0;
    let mut v___x_4589_: u64 = 0;
    let mut v___x_4590_: u64 = 0;
    let mut v___x_4591_: u64 = 0;
    let mut v___x_4592_: usize = 0;
    let mut v___x_4593_: usize = 0;
    let mut v___x_4594_: usize = 0;
    let mut v___x_4595_: usize = 0;
    let mut v___x_4596_: usize = 0;
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4577_) == 0 {
                    return v_x_4576_;
                } else {
                    v_key_4578_ = crate::leanh::lean_ctor_get(v_x_4577_, 0);
                    v_value_4579_ = crate::leanh::lean_ctor_get(v_x_4577_, 1);
                    v_tail_4580_ = crate::leanh::lean_ctor_get(v_x_4577_, 2);
                    v_isSharedCheck_4603_ = (!crate::leanh::lean_is_exclusive(v_x_4577_)) as u8;
                    if v_isSharedCheck_4603_ == 0 {
                        v___x_4582_ = v_x_4577_;
                        v_isShared_4583_ = v_isSharedCheck_4603_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4580_);
                        crate::leanh::lean_inc(v_value_4579_);
                        crate::leanh::lean_inc(v_key_4578_);
                        crate::leanh::lean_dec(v_x_4577_);
                        v___x_4582_ = crate::leanh::lean_box(0);
                        v_isShared_4583_ = v_isSharedCheck_4603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4584_ = lean_array_get_size(v_x_4576_);
                v___x_4585_ = l_Lean_instHashableFVarId_hash(v_key_4578_);
                v___x_4586_ = 32u64;
                v___x_4587_ = lean_uint64_shift_right(v___x_4585_, v___x_4586_);
                v_fold_4588_ = lean_uint64_xor(v___x_4585_, v___x_4587_);
                v___x_4589_ = 16u64;
                v___x_4590_ = lean_uint64_shift_right(v_fold_4588_, v___x_4589_);
                v___x_4591_ = lean_uint64_xor(v_fold_4588_, v___x_4590_);
                v___x_4592_ = lean_uint64_to_usize(v___x_4591_);
                v___x_4593_ = lean_usize_of_nat(v___x_4584_);
                v___x_4594_ = 1usize;
                v___x_4595_ = lean_usize_sub(v___x_4593_, v___x_4594_);
                v___x_4596_ = lean_usize_land(v___x_4592_, v___x_4595_);
                v___x_4597_ = lean_array_uget_borrowed(v_x_4576_, v___x_4596_);
                crate::leanh::lean_inc(v___x_4597_);
                if v_isShared_4583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4582_, 2, v___x_4597_);
                    v___x_4599_ = v___x_4582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4602_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_key_4578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_value_4579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 2, v___x_4597_);
                    v___x_4599_ = v_reuseFailAlloc_4602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4600_ = lean_array_uset(v_x_4576_, v___x_4596_, v___x_4599_);
                v_x_4576_ = v___x_4600_;
                v_x_4577_ = v_tail_4580_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(
    mut v_i_4604_: *mut crate::leanh::LeanObject,
    mut v_source_4605_: *mut crate::leanh::LeanObject,
    mut v_target_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: u8 = 0;
    let mut v_es_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4607_ = lean_array_get_size(v_source_4605_);
                v___x_4608_ = lean_nat_dec_lt(v_i_4604_, v___x_4607_);
                if v___x_4608_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4605_);
                    crate::leanh::lean_dec(v_i_4604_);
                    return v_target_4606_;
                } else {
                    v_es_4609_ = lean_array_fget(v_source_4605_, v_i_4604_);
                    v___x_4610_ = crate::leanh::lean_box(0);
                    v_source_4611_ = lean_array_fset(v_source_4605_, v_i_4604_, v___x_4610_);
                    v_target_4612_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4606_, v_es_4609_);
                    v___x_4613_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4614_ = lean_nat_add(v_i_4604_, v___x_4613_);
                    crate::leanh::lean_dec(v_i_4604_);
                    v_i_4604_ = v___x_4614_;
                    v_source_4605_ = v_source_4611_;
                    v_target_4606_ = v_target_4612_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(
    mut v_data_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4617_ = lean_array_get_size(v_data_4616_);
    v___x_4618_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4619_ = lean_nat_mul(v___x_4617_, v___x_4618_);
    v___x_4620_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4621_ = crate::leanh::lean_box(0);
    v___x_4622_ = lean_mk_array(v_nbuckets_4619_, v___x_4621_);
    v___x_4623_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(v___x_4620_, v_data_4616_, v___x_4622_);
    return v___x_4623_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(
    mut v_m_4624_: *mut crate::leanh::LeanObject,
    mut v_a_4625_: *mut crate::leanh::LeanObject,
    mut v_b_4626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: u64 = 0;
    let mut v___x_4631_: u64 = 0;
    let mut v___x_4632_: u64 = 0;
    let mut v_fold_4633_: u64 = 0;
    let mut v___x_4634_: u64 = 0;
    let mut v___x_4635_: u64 = 0;
    let mut v___x_4636_: u64 = 0;
    let mut v___x_4637_: usize = 0;
    let mut v___x_4638_: usize = 0;
    let mut v___x_4639_: usize = 0;
    let mut v___x_4640_: usize = 0;
    let mut v___x_4641_: usize = 0;
    let mut v_bkt_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: u8 = 0;
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4646_: u8 = 0;
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v_val_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v_unused_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4627_ = crate::leanh::lean_ctor_get(v_m_4624_, 0);
                v_buckets_4628_ = crate::leanh::lean_ctor_get(v_m_4624_, 1);
                v___x_4629_ = lean_array_get_size(v_buckets_4628_);
                v___x_4630_ = l_Lean_instHashableFVarId_hash(v_a_4625_);
                v___x_4631_ = 32u64;
                v___x_4632_ = lean_uint64_shift_right(v___x_4630_, v___x_4631_);
                v_fold_4633_ = lean_uint64_xor(v___x_4630_, v___x_4632_);
                v___x_4634_ = 16u64;
                v___x_4635_ = lean_uint64_shift_right(v_fold_4633_, v___x_4634_);
                v___x_4636_ = lean_uint64_xor(v_fold_4633_, v___x_4635_);
                v___x_4637_ = lean_uint64_to_usize(v___x_4636_);
                v___x_4638_ = lean_usize_of_nat(v___x_4629_);
                v___x_4639_ = 1usize;
                v___x_4640_ = lean_usize_sub(v___x_4638_, v___x_4639_);
                v___x_4641_ = lean_usize_land(v___x_4637_, v___x_4640_);
                v_bkt_4642_ = lean_array_uget_borrowed(v_buckets_4628_, v___x_4641_);
                v___x_4643_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_4625_, v_bkt_4642_);
                if v___x_4643_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_4628_);
                    crate::leanh::lean_inc(v_size_4627_);
                    v_isSharedCheck_4664_ = (!crate::leanh::lean_is_exclusive(v_m_4624_)) as u8;
                    if v_isSharedCheck_4664_ == 0 {
                        v_unused_4665_ = crate::leanh::lean_ctor_get(v_m_4624_, 1);
                        crate::leanh::lean_dec(v_unused_4665_);
                        v_unused_4666_ = crate::leanh::lean_ctor_get(v_m_4624_, 0);
                        crate::leanh::lean_dec(v_unused_4666_);
                        v___x_4645_ = v_m_4624_;
                        v_isShared_4646_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4624_);
                        v___x_4645_ = crate::leanh::lean_box(0);
                        v_isShared_4646_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_4626_);
                    crate::leanh::lean_dec(v_a_4625_);
                    return v_m_4624_;
                }
            }
            1 => {
                v___x_4647_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_4648_ = lean_nat_add(v_size_4627_, v___x_4647_);
                crate::leanh::lean_dec(v_size_4627_);
                crate::leanh::lean_inc(v_bkt_4642_);
                v___x_4649_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4649_, 0, v_a_4625_);
                crate::leanh::lean_ctor_set(v___x_4649_, 1, v_b_4626_);
                crate::leanh::lean_ctor_set(v___x_4649_, 2, v_bkt_4642_);
                v_buckets_x27_4650_ = lean_array_uset(v_buckets_4628_, v___x_4641_, v___x_4649_);
                v___x_4651_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4652_ = lean_nat_mul(v_size_x27_4648_, v___x_4651_);
                v___x_4653_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4654_ = lean_nat_div(v___x_4652_, v___x_4653_);
                crate::leanh::lean_dec(v___x_4652_);
                v___x_4655_ = lean_array_get_size(v_buckets_x27_4650_);
                v___x_4656_ = lean_nat_dec_le(v___x_4654_, v___x_4655_);
                crate::leanh::lean_dec(v___x_4654_);
                if v___x_4656_ == 0 {
                    v_val_4657_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(v_buckets_x27_4650_);
                    if v_isShared_4646_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4645_, 1, v_val_4657_);
                        crate::leanh::lean_ctor_set(v___x_4645_, 0, v_size_x27_4648_);
                        v___x_4659_ = v___x_4645_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4660_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_size_x27_4648_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_val_4657_);
                        v___x_4659_ = v_reuseFailAlloc_4660_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4646_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4645_, 1, v_buckets_x27_4650_);
                        crate::leanh::lean_ctor_set(v___x_4645_, 0, v_size_x27_4648_);
                        v___x_4662_ = v___x_4645_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_size_x27_4648_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_buckets_x27_4650_);
                        v___x_4662_ = v_reuseFailAlloc_4663_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4659_;
            }
            3 => {
                return v___x_4662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(
    mut v_m_4667_: *mut crate::leanh::LeanObject,
    mut v_a_4668_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: u64 = 0;
    let mut v___x_4672_: u64 = 0;
    let mut v___x_4673_: u64 = 0;
    let mut v_fold_4674_: u64 = 0;
    let mut v___x_4675_: u64 = 0;
    let mut v___x_4676_: u64 = 0;
    let mut v___x_4677_: u64 = 0;
    let mut v___x_4678_: usize = 0;
    let mut v___x_4679_: usize = 0;
    let mut v___x_4680_: usize = 0;
    let mut v___x_4681_: usize = 0;
    let mut v___x_4682_: usize = 0;
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    v_buckets_4669_ = crate::leanh::lean_ctor_get(v_m_4667_, 1);
    v___x_4670_ = lean_array_get_size(v_buckets_4669_);
    v___x_4671_ = l_Lean_instHashableFVarId_hash(v_a_4668_);
    v___x_4672_ = 32u64;
    v___x_4673_ = lean_uint64_shift_right(v___x_4671_, v___x_4672_);
    v_fold_4674_ = lean_uint64_xor(v___x_4671_, v___x_4673_);
    v___x_4675_ = 16u64;
    v___x_4676_ = lean_uint64_shift_right(v_fold_4674_, v___x_4675_);
    v___x_4677_ = lean_uint64_xor(v_fold_4674_, v___x_4676_);
    v___x_4678_ = lean_uint64_to_usize(v___x_4677_);
    v___x_4679_ = lean_usize_of_nat(v___x_4670_);
    v___x_4680_ = 1usize;
    v___x_4681_ = lean_usize_sub(v___x_4679_, v___x_4680_);
    v___x_4682_ = lean_usize_land(v___x_4678_, v___x_4681_);
    v___x_4683_ = lean_array_uget_borrowed(v_buckets_4669_, v___x_4682_);
    v___x_4684_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_4668_, v___x_4683_);
    return v___x_4684_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg___boxed(
    mut v_m_4685_: *mut crate::leanh::LeanObject,
    mut v_a_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4687_: u8 = 0;
    let mut v_r_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4687_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v_m_4685_, v_a_4686_);
    crate::leanh::lean_dec(v_a_4686_);
    crate::leanh::lean_dec_ref(v_m_4685_);
    v_r_4688_ = crate::leanh::lean_box((v_res_4687_) as usize);
    return v_r_4688_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4690_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0;
    v___x_4691_ = l_Lean_stringToMessageData(v___x_4690_);
    return v___x_4691_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
    mut v_fvarId_4692_: *mut crate::leanh::LeanObject,
    mut v_a_4693_: *mut crate::leanh::LeanObject,
    mut v_a_4694_: *mut crate::leanh::LeanObject,
    mut v_a_4695_: *mut crate::leanh::LeanObject,
    mut v_a_4696_: *mut crate::leanh::LeanObject,
    mut v_a_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: u8 = 0;
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4706_ = lean_st_ref_get(v_a_4693_);
                v___x_4707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v___x_4706_, v_fvarId_4692_);
                crate::leanh::lean_dec(v___x_4706_);
                if v___x_4707_ == 0 {
                    v___y_4700_ = v_a_4693_;
                    state = 1;
                    continue;
                } else {
                    v___x_4708_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1,
                    );
                    v___x_4709_ = l_Lean_MessageData_ofName(v_fvarId_4692_);
                    v___x_4710_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4710_, 0, v___x_4708_);
                    crate::leanh::lean_ctor_set(v___x_4710_, 1, v___x_4709_);
                    v___x_4711_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                    v___x_4712_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4712_, 0, v___x_4710_);
                    crate::leanh::lean_ctor_set(v___x_4712_, 1, v___x_4711_);
                    v___x_4713_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4712_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
                    return v___x_4713_;
                }
            }
            1 => {
                v___x_4701_ = lean_st_ref_take(v___y_4700_);
                v___x_4702_ = crate::leanh::lean_box(0);
                v___x_4703_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(v___x_4701_, v_fvarId_4692_, v___x_4702_);
                v___x_4704_ = lean_st_ref_set(v___y_4700_, v___x_4703_);
                v___x_4705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4705_, 0, v___x_4702_);
                return v___x_4705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___boxed(
    mut v_fvarId_4714_: *mut crate::leanh::LeanObject,
    mut v_a_4715_: *mut crate::leanh::LeanObject,
    mut v_a_4716_: *mut crate::leanh::LeanObject,
    mut v_a_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
    mut v_a_4719_: *mut crate::leanh::LeanObject,
    mut v_a_4720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4721_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
        v_fvarId_4714_,
        v_a_4715_,
        v_a_4716_,
        v_a_4717_,
        v_a_4718_,
        v_a_4719_,
    );
    crate::leanh::lean_dec(v_a_4719_);
    crate::leanh::lean_dec_ref(v_a_4718_);
    crate::leanh::lean_dec(v_a_4717_);
    crate::leanh::lean_dec_ref(v_a_4716_);
    crate::leanh::lean_dec(v_a_4715_);
    return v_res_4721_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId(
    mut v_fvarId_4722_: *mut crate::leanh::LeanObject,
    mut v_a_4723_: *mut crate::leanh::LeanObject,
    mut v_a_4724_: *mut crate::leanh::LeanObject,
    mut v_a_4725_: *mut crate::leanh::LeanObject,
    mut v_a_4726_: *mut crate::leanh::LeanObject,
    mut v_a_4727_: *mut crate::leanh::LeanObject,
    mut v_a_4728_: *mut crate::leanh::LeanObject,
    mut v_a_4729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4731_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
        v_fvarId_4722_,
        v_a_4724_,
        v_a_4726_,
        v_a_4727_,
        v_a_4728_,
        v_a_4729_,
    );
    return v___x_4731_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId___boxed(
    mut v_fvarId_4732_: *mut crate::leanh::LeanObject,
    mut v_a_4733_: *mut crate::leanh::LeanObject,
    mut v_a_4734_: *mut crate::leanh::LeanObject,
    mut v_a_4735_: *mut crate::leanh::LeanObject,
    mut v_a_4736_: *mut crate::leanh::LeanObject,
    mut v_a_4737_: *mut crate::leanh::LeanObject,
    mut v_a_4738_: *mut crate::leanh::LeanObject,
    mut v_a_4739_: *mut crate::leanh::LeanObject,
    mut v_a_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4741_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId(
        v_fvarId_4732_,
        v_a_4733_,
        v_a_4734_,
        v_a_4735_,
        v_a_4736_,
        v_a_4737_,
        v_a_4738_,
        v_a_4739_,
    );
    crate::leanh::lean_dec(v_a_4739_);
    crate::leanh::lean_dec_ref(v_a_4738_);
    crate::leanh::lean_dec(v_a_4737_);
    crate::leanh::lean_dec_ref(v_a_4736_);
    crate::leanh::lean_dec_ref(v_a_4735_);
    crate::leanh::lean_dec(v_a_4734_);
    crate::leanh::lean_dec_ref(v_a_4733_);
    return v_res_4741_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0(
    mut v_00_u03b2_4742_: *mut crate::leanh::LeanObject,
    mut v_m_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
    mut v_b_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4746_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(v_m_4743_, v_a_4744_, v_b_4745_);
    return v___x_4746_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(
    mut v_00_u03b2_4747_: *mut crate::leanh::LeanObject,
    mut v_m_4748_: *mut crate::leanh::LeanObject,
    mut v_a_4749_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4750_: u8 = 0;
    v___x_4750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v_m_4748_, v_a_4749_);
    return v___x_4750_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___boxed(
    mut v_00_u03b2_4751_: *mut crate::leanh::LeanObject,
    mut v_m_4752_: *mut crate::leanh::LeanObject,
    mut v_a_4753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4754_: u8 = 0;
    let mut v_r_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4754_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(v_00_u03b2_4751_, v_m_4752_, v_a_4753_);
    crate::leanh::lean_dec(v_a_4753_);
    crate::leanh::lean_dec_ref(v_m_4752_);
    v_r_4755_ = crate::leanh::lean_box((v_res_4754_) as usize);
    return v_r_4755_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(
    mut v_00_u03b2_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_x_4758_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4759_: u8 = 0;
    v___x_4759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_4757_, v_x_4758_);
    return v___x_4759_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___boxed(
    mut v_00_u03b2_4760_: *mut crate::leanh::LeanObject,
    mut v_a_4761_: *mut crate::leanh::LeanObject,
    mut v_x_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4763_: u8 = 0;
    let mut v_r_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(v_00_u03b2_4760_, v_a_4761_, v_x_4762_);
    crate::leanh::lean_dec(v_x_4762_);
    crate::leanh::lean_dec(v_a_4761_);
    v_r_4764_ = crate::leanh::lean_box((v_res_4763_) as usize);
    return v_r_4764_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1(
    mut v_00_u03b2_4765_: *mut crate::leanh::LeanObject,
    mut v_data_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(v_data_4766_);
    return v___x_4767_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4768_: *mut crate::leanh::LeanObject,
    mut v_i_4769_: *mut crate::leanh::LeanObject,
    mut v_source_4770_: *mut crate::leanh::LeanObject,
    mut v_target_4771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4772_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(v_i_4769_, v_source_4770_, v_target_4771_);
    return v___x_4772_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4773_: *mut crate::leanh::LeanObject,
    mut v_x_4774_: *mut crate::leanh::LeanObject,
    mut v_x_4775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4776_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4774_, v_x_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg(
    mut v_fvarId_4777_: *mut crate::leanh::LeanObject,
    mut v_x_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
    mut v_a_4782_: *mut crate::leanh::LeanObject,
    mut v_a_4783_: *mut crate::leanh::LeanObject,
    mut v_a_4784_: *mut crate::leanh::LeanObject,
    mut v_a_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_4777_);
                v___x_4787_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4777_,
                    v_a_4780_,
                    v_a_4782_,
                    v_a_4783_,
                    v_a_4784_,
                    v_a_4785_,
                );
                if crate::leanh::lean_obj_tag(v___x_4787_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4787_, 1);
                    v_jps_4788_ = crate::leanh::lean_ctor_get(v_a_4779_, 0);
                    v_vars_4789_ = crate::leanh::lean_ctor_get(v_a_4779_, 1);
                    crate::leanh::lean_inc(v_vars_4789_);
                    v___x_4790_ = l_Lean_FVarIdSet_insert(v_vars_4789_, v_fvarId_4777_);
                    crate::leanh::lean_inc(v_jps_4788_);
                    v___x_4791_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4791_, 0, v_jps_4788_);
                    crate::leanh::lean_ctor_set(v___x_4791_, 1, v___x_4790_);
                    crate::leanh::lean_inc(v_a_4785_);
                    crate::leanh::lean_inc_ref(v_a_4784_);
                    crate::leanh::lean_inc(v_a_4783_);
                    crate::leanh::lean_inc_ref(v_a_4782_);
                    crate::leanh::lean_inc_ref(v_a_4781_);
                    crate::leanh::lean_inc(v_a_4780_);
                    v___x_4792_ = crate::leanh::lean_apply_8(
                        v_x_4778_,
                        v___x_4791_,
                        v_a_4780_,
                        v_a_4781_,
                        v_a_4782_,
                        v_a_4783_,
                        v_a_4784_,
                        v_a_4785_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4792_;
                } else {
                    crate::leanh::lean_dec_ref(v_x_4778_);
                    crate::leanh::lean_dec(v_fvarId_4777_);
                    v_a_4793_ = crate::leanh::lean_ctor_get(v___x_4787_, 0);
                    v_isSharedCheck_4800_ = (!crate::leanh::lean_is_exclusive(v___x_4787_)) as u8;
                    if v_isSharedCheck_4800_ == 0 {
                        v___x_4795_ = v___x_4787_;
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4793_);
                        crate::leanh::lean_dec(v___x_4787_);
                        v___x_4795_ = crate::leanh::lean_box(0);
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4796_ == 0 {
                    v___x_4798_ = v___x_4795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4799_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
                    v___x_4798_ = v_reuseFailAlloc_4799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg___boxed(
    mut v_fvarId_4801_: *mut crate::leanh::LeanObject,
    mut v_x_4802_: *mut crate::leanh::LeanObject,
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
    mut v_a_4807_: *mut crate::leanh::LeanObject,
    mut v_a_4808_: *mut crate::leanh::LeanObject,
    mut v_a_4809_: *mut crate::leanh::LeanObject,
    mut v_a_4810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4811_ = l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg(
        v_fvarId_4801_,
        v_x_4802_,
        v_a_4803_,
        v_a_4804_,
        v_a_4805_,
        v_a_4806_,
        v_a_4807_,
        v_a_4808_,
        v_a_4809_,
    );
    crate::leanh::lean_dec(v_a_4809_);
    crate::leanh::lean_dec_ref(v_a_4808_);
    crate::leanh::lean_dec(v_a_4807_);
    crate::leanh::lean_dec_ref(v_a_4806_);
    crate::leanh::lean_dec_ref(v_a_4805_);
    crate::leanh::lean_dec(v_a_4804_);
    crate::leanh::lean_dec_ref(v_a_4803_);
    return v_res_4811_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withFVarId(
    mut v_00_u03b1_4812_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4813_: *mut crate::leanh::LeanObject,
    mut v_x_4814_: *mut crate::leanh::LeanObject,
    mut v_a_4815_: *mut crate::leanh::LeanObject,
    mut v_a_4816_: *mut crate::leanh::LeanObject,
    mut v_a_4817_: *mut crate::leanh::LeanObject,
    mut v_a_4818_: *mut crate::leanh::LeanObject,
    mut v_a_4819_: *mut crate::leanh::LeanObject,
    mut v_a_4820_: *mut crate::leanh::LeanObject,
    mut v_a_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4832_: u8 = 0;
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_4813_);
                v___x_4823_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4813_,
                    v_a_4816_,
                    v_a_4818_,
                    v_a_4819_,
                    v_a_4820_,
                    v_a_4821_,
                );
                if crate::leanh::lean_obj_tag(v___x_4823_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4823_, 1);
                    v_jps_4824_ = crate::leanh::lean_ctor_get(v_a_4815_, 0);
                    v_vars_4825_ = crate::leanh::lean_ctor_get(v_a_4815_, 1);
                    crate::leanh::lean_inc(v_vars_4825_);
                    v___x_4826_ = l_Lean_FVarIdSet_insert(v_vars_4825_, v_fvarId_4813_);
                    crate::leanh::lean_inc(v_jps_4824_);
                    v___x_4827_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4827_, 0, v_jps_4824_);
                    crate::leanh::lean_ctor_set(v___x_4827_, 1, v___x_4826_);
                    crate::leanh::lean_inc(v_a_4821_);
                    crate::leanh::lean_inc_ref(v_a_4820_);
                    crate::leanh::lean_inc(v_a_4819_);
                    crate::leanh::lean_inc_ref(v_a_4818_);
                    crate::leanh::lean_inc_ref(v_a_4817_);
                    crate::leanh::lean_inc(v_a_4816_);
                    v___x_4828_ = crate::leanh::lean_apply_8(
                        v_x_4814_,
                        v___x_4827_,
                        v_a_4816_,
                        v_a_4817_,
                        v_a_4818_,
                        v_a_4819_,
                        v_a_4820_,
                        v_a_4821_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4828_;
                } else {
                    crate::leanh::lean_dec_ref(v_x_4814_);
                    crate::leanh::lean_dec(v_fvarId_4813_);
                    v_a_4829_ = crate::leanh::lean_ctor_get(v___x_4823_, 0);
                    v_isSharedCheck_4836_ = (!crate::leanh::lean_is_exclusive(v___x_4823_)) as u8;
                    if v_isSharedCheck_4836_ == 0 {
                        v___x_4831_ = v___x_4823_;
                        v_isShared_4832_ = v_isSharedCheck_4836_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4829_);
                        crate::leanh::lean_dec(v___x_4823_);
                        v___x_4831_ = crate::leanh::lean_box(0);
                        v_isShared_4832_ = v_isSharedCheck_4836_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4832_ == 0 {
                    v___x_4834_ = v___x_4831_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
                    v___x_4834_ = v_reuseFailAlloc_4835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withFVarId___boxed(
    mut v_00_u03b1_4837_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4838_: *mut crate::leanh::LeanObject,
    mut v_x_4839_: *mut crate::leanh::LeanObject,
    mut v_a_4840_: *mut crate::leanh::LeanObject,
    mut v_a_4841_: *mut crate::leanh::LeanObject,
    mut v_a_4842_: *mut crate::leanh::LeanObject,
    mut v_a_4843_: *mut crate::leanh::LeanObject,
    mut v_a_4844_: *mut crate::leanh::LeanObject,
    mut v_a_4845_: *mut crate::leanh::LeanObject,
    mut v_a_4846_: *mut crate::leanh::LeanObject,
    mut v_a_4847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4848_ = l_Lean_Compiler_LCNF_Check_Pure_withFVarId(
        v_00_u03b1_4837_,
        v_fvarId_4838_,
        v_x_4839_,
        v_a_4840_,
        v_a_4841_,
        v_a_4842_,
        v_a_4843_,
        v_a_4844_,
        v_a_4845_,
        v_a_4846_,
    );
    crate::leanh::lean_dec(v_a_4846_);
    crate::leanh::lean_dec_ref(v_a_4845_);
    crate::leanh::lean_dec(v_a_4844_);
    crate::leanh::lean_dec_ref(v_a_4843_);
    crate::leanh::lean_dec_ref(v_a_4842_);
    crate::leanh::lean_dec(v_a_4841_);
    crate::leanh::lean_dec_ref(v_a_4840_);
    return v_res_4848_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg(
    mut v_fvarId_4849_: *mut crate::leanh::LeanObject,
    mut v_x_4850_: *mut crate::leanh::LeanObject,
    mut v_a_4851_: *mut crate::leanh::LeanObject,
    mut v_a_4852_: *mut crate::leanh::LeanObject,
    mut v_a_4853_: *mut crate::leanh::LeanObject,
    mut v_a_4854_: *mut crate::leanh::LeanObject,
    mut v_a_4855_: *mut crate::leanh::LeanObject,
    mut v_a_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_4849_);
                v___x_4859_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4849_,
                    v_a_4852_,
                    v_a_4854_,
                    v_a_4855_,
                    v_a_4856_,
                    v_a_4857_,
                );
                if crate::leanh::lean_obj_tag(v___x_4859_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4859_, 1);
                    v_jps_4860_ = crate::leanh::lean_ctor_get(v_a_4851_, 0);
                    v_vars_4861_ = crate::leanh::lean_ctor_get(v_a_4851_, 1);
                    crate::leanh::lean_inc(v_jps_4860_);
                    v___x_4862_ = l_Lean_FVarIdSet_insert(v_jps_4860_, v_fvarId_4849_);
                    crate::leanh::lean_inc(v_vars_4861_);
                    v___x_4863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4863_, 0, v___x_4862_);
                    crate::leanh::lean_ctor_set(v___x_4863_, 1, v_vars_4861_);
                    crate::leanh::lean_inc(v_a_4857_);
                    crate::leanh::lean_inc_ref(v_a_4856_);
                    crate::leanh::lean_inc(v_a_4855_);
                    crate::leanh::lean_inc_ref(v_a_4854_);
                    crate::leanh::lean_inc_ref(v_a_4853_);
                    crate::leanh::lean_inc(v_a_4852_);
                    v___x_4864_ = crate::leanh::lean_apply_8(
                        v_x_4850_,
                        v___x_4863_,
                        v_a_4852_,
                        v_a_4853_,
                        v_a_4854_,
                        v_a_4855_,
                        v_a_4856_,
                        v_a_4857_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4864_;
                } else {
                    crate::leanh::lean_dec_ref(v_x_4850_);
                    crate::leanh::lean_dec(v_fvarId_4849_);
                    v_a_4865_ = crate::leanh::lean_ctor_get(v___x_4859_, 0);
                    v_isSharedCheck_4872_ = (!crate::leanh::lean_is_exclusive(v___x_4859_)) as u8;
                    if v_isSharedCheck_4872_ == 0 {
                        v___x_4867_ = v___x_4859_;
                        v_isShared_4868_ = v_isSharedCheck_4872_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4865_);
                        crate::leanh::lean_dec(v___x_4859_);
                        v___x_4867_ = crate::leanh::lean_box(0);
                        v_isShared_4868_ = v_isSharedCheck_4872_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4868_ == 0 {
                    v___x_4870_ = v___x_4867_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
                    v___x_4870_ = v_reuseFailAlloc_4871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg___boxed(
    mut v_fvarId_4873_: *mut crate::leanh::LeanObject,
    mut v_x_4874_: *mut crate::leanh::LeanObject,
    mut v_a_4875_: *mut crate::leanh::LeanObject,
    mut v_a_4876_: *mut crate::leanh::LeanObject,
    mut v_a_4877_: *mut crate::leanh::LeanObject,
    mut v_a_4878_: *mut crate::leanh::LeanObject,
    mut v_a_4879_: *mut crate::leanh::LeanObject,
    mut v_a_4880_: *mut crate::leanh::LeanObject,
    mut v_a_4881_: *mut crate::leanh::LeanObject,
    mut v_a_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4883_ = l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg(
        v_fvarId_4873_,
        v_x_4874_,
        v_a_4875_,
        v_a_4876_,
        v_a_4877_,
        v_a_4878_,
        v_a_4879_,
        v_a_4880_,
        v_a_4881_,
    );
    crate::leanh::lean_dec(v_a_4881_);
    crate::leanh::lean_dec_ref(v_a_4880_);
    crate::leanh::lean_dec(v_a_4879_);
    crate::leanh::lean_dec_ref(v_a_4878_);
    crate::leanh::lean_dec_ref(v_a_4877_);
    crate::leanh::lean_dec(v_a_4876_);
    crate::leanh::lean_dec_ref(v_a_4875_);
    return v_res_4883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withJp(
    mut v_00_u03b1_4884_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4885_: *mut crate::leanh::LeanObject,
    mut v_x_4886_: *mut crate::leanh::LeanObject,
    mut v_a_4887_: *mut crate::leanh::LeanObject,
    mut v_a_4888_: *mut crate::leanh::LeanObject,
    mut v_a_4889_: *mut crate::leanh::LeanObject,
    mut v_a_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
    mut v_a_4892_: *mut crate::leanh::LeanObject,
    mut v_a_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4904_: u8 = 0;
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_4885_);
                v___x_4895_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4885_,
                    v_a_4888_,
                    v_a_4890_,
                    v_a_4891_,
                    v_a_4892_,
                    v_a_4893_,
                );
                if crate::leanh::lean_obj_tag(v___x_4895_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4895_, 1);
                    v_jps_4896_ = crate::leanh::lean_ctor_get(v_a_4887_, 0);
                    v_vars_4897_ = crate::leanh::lean_ctor_get(v_a_4887_, 1);
                    crate::leanh::lean_inc(v_jps_4896_);
                    v___x_4898_ = l_Lean_FVarIdSet_insert(v_jps_4896_, v_fvarId_4885_);
                    crate::leanh::lean_inc(v_vars_4897_);
                    v___x_4899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4899_, 0, v___x_4898_);
                    crate::leanh::lean_ctor_set(v___x_4899_, 1, v_vars_4897_);
                    crate::leanh::lean_inc(v_a_4893_);
                    crate::leanh::lean_inc_ref(v_a_4892_);
                    crate::leanh::lean_inc(v_a_4891_);
                    crate::leanh::lean_inc_ref(v_a_4890_);
                    crate::leanh::lean_inc_ref(v_a_4889_);
                    crate::leanh::lean_inc(v_a_4888_);
                    v___x_4900_ = crate::leanh::lean_apply_8(
                        v_x_4886_,
                        v___x_4899_,
                        v_a_4888_,
                        v_a_4889_,
                        v_a_4890_,
                        v_a_4891_,
                        v_a_4892_,
                        v_a_4893_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4900_;
                } else {
                    crate::leanh::lean_dec_ref(v_x_4886_);
                    crate::leanh::lean_dec(v_fvarId_4885_);
                    v_a_4901_ = crate::leanh::lean_ctor_get(v___x_4895_, 0);
                    v_isSharedCheck_4908_ = (!crate::leanh::lean_is_exclusive(v___x_4895_)) as u8;
                    if v_isSharedCheck_4908_ == 0 {
                        v___x_4903_ = v___x_4895_;
                        v_isShared_4904_ = v_isSharedCheck_4908_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4901_);
                        crate::leanh::lean_dec(v___x_4895_);
                        v___x_4903_ = crate::leanh::lean_box(0);
                        v_isShared_4904_ = v_isSharedCheck_4908_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4904_ == 0 {
                    v___x_4906_ = v___x_4903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
                    v___x_4906_ = v_reuseFailAlloc_4907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withJp___boxed(
    mut v_00_u03b1_4909_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4910_: *mut crate::leanh::LeanObject,
    mut v_x_4911_: *mut crate::leanh::LeanObject,
    mut v_a_4912_: *mut crate::leanh::LeanObject,
    mut v_a_4913_: *mut crate::leanh::LeanObject,
    mut v_a_4914_: *mut crate::leanh::LeanObject,
    mut v_a_4915_: *mut crate::leanh::LeanObject,
    mut v_a_4916_: *mut crate::leanh::LeanObject,
    mut v_a_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4920_ = l_Lean_Compiler_LCNF_Check_Pure_withJp(
        v_00_u03b1_4909_,
        v_fvarId_4910_,
        v_x_4911_,
        v_a_4912_,
        v_a_4913_,
        v_a_4914_,
        v_a_4915_,
        v_a_4916_,
        v_a_4917_,
        v_a_4918_,
    );
    crate::leanh::lean_dec(v_a_4918_);
    crate::leanh::lean_dec_ref(v_a_4917_);
    crate::leanh::lean_dec(v_a_4916_);
    crate::leanh::lean_dec_ref(v_a_4915_);
    crate::leanh::lean_dec_ref(v_a_4914_);
    crate::leanh::lean_dec(v_a_4913_);
    crate::leanh::lean_dec_ref(v_a_4912_);
    return v_res_4920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0(
    mut v_x1_4921_: *mut crate::leanh::LeanObject,
    mut v_x2_4922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fvarId_4923_ = crate::leanh::lean_ctor_get(v_x2_4922_, 0);
    crate::leanh::lean_inc(v_fvarId_4923_);
    crate::leanh::lean_dec_ref(v_x2_4922_);
    v___x_4924_ = l_Lean_FVarIdSet_insert(v_x1_4921_, v_fvarId_4923_);
    return v___x_4924_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1(
    mut v_x_4925_: *mut crate::leanh::LeanObject,
    mut v___y_4926_: *mut crate::leanh::LeanObject,
    mut v___y_4927_: *mut crate::leanh::LeanObject,
    mut v___y_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fvarId_4935_ = crate::leanh::lean_ctor_get(v___y_4926_, 0);
    crate::leanh::lean_inc(v_fvarId_4935_);
    crate::leanh::lean_dec_ref(v___y_4926_);
    v___x_4936_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
        v_fvarId_4935_,
        v___y_4928_,
        v___y_4930_,
        v___y_4931_,
        v___y_4932_,
        v___y_4933_,
    );
    return v___x_4936_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1___boxed(
    mut v_x_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
    mut v___y_4943_: *mut crate::leanh::LeanObject,
    mut v___y_4944_: *mut crate::leanh::LeanObject,
    mut v___y_4945_: *mut crate::leanh::LeanObject,
    mut v___y_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1(
        v_x_4937_,
        v___y_4938_,
        v___y_4939_,
        v___y_4940_,
        v___y_4941_,
        v___y_4942_,
        v___y_4943_,
        v___y_4944_,
        v___y_4945_,
    );
    crate::leanh::lean_dec(v___y_4945_);
    crate::leanh::lean_dec_ref(v___y_4944_);
    crate::leanh::lean_dec(v___y_4943_);
    crate::leanh::lean_dec_ref(v___y_4942_);
    crate::leanh::lean_dec_ref(v___y_4941_);
    crate::leanh::lean_dec(v___y_4940_);
    crate::leanh::lean_dec_ref(v___y_4939_);
    return v_res_4947_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4948_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_4948_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4949_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0,
    );
    v___x_4950_ = l_StateRefT_x27_instMonad___redArg(v___x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg(
    mut v_params_4976_: *mut crate::leanh::LeanObject,
    mut v_x_4977_: *mut crate::leanh::LeanObject,
    mut v_a_4978_: *mut crate::leanh::LeanObject,
    mut v_a_4979_: *mut crate::leanh::LeanObject,
    mut v_a_4980_: *mut crate::leanh::LeanObject,
    mut v_a_4981_: *mut crate::leanh::LeanObject,
    mut v_a_4982_: *mut crate::leanh::LeanObject,
    mut v_a_4983_: *mut crate::leanh::LeanObject,
    mut v_a_4984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v_toFunctor_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v___f_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: u8 = 0;
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: usize = 0;
    let mut v___x_5041_: usize = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: usize = 0;
    let mut v___x_5046_: usize = 0;
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v___x_5060_: u8 = 0;
    let mut v___f_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5064_: usize = 0;
    let mut v___x_5065_: usize = 0;
    let mut v___x_1277__overap_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: usize = 0;
    let mut v___x_5069_: usize = 0;
    let mut v___x_1281__overap_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5074_: u8 = 0;
    let mut v_unused_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5076_: u8 = 0;
    let mut v_unused_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4986_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1,
                );
                v_toApplicative_4987_ = crate::leanh::lean_ctor_get(v___x_4986_, 0);
                v_toFunctor_4988_ = crate::leanh::lean_ctor_get(v_toApplicative_4987_, 0);
                v_toSeq_4989_ = crate::leanh::lean_ctor_get(v_toApplicative_4987_, 2);
                v_toSeqLeft_4990_ = crate::leanh::lean_ctor_get(v_toApplicative_4987_, 3);
                v_toSeqRight_4991_ = crate::leanh::lean_ctor_get(v_toApplicative_4987_, 4);
                v___f_4992_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2;
                v___f_4993_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_4988_, 2);
                v___f_4994_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4994_, 0, v_toFunctor_4988_);
                v___f_4995_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4995_, 0, v_toFunctor_4988_);
                v___x_4996_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4996_, 0, v___f_4994_);
                crate::leanh::lean_ctor_set(v___x_4996_, 1, v___f_4995_);
                crate::leanh::lean_inc(v_toSeqRight_4991_);
                v___f_4997_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4997_, 0, v_toSeqRight_4991_);
                crate::leanh::lean_inc(v_toSeqLeft_4990_);
                v___f_4998_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4998_, 0, v_toSeqLeft_4990_);
                crate::leanh::lean_inc(v_toSeq_4989_);
                v___f_4999_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4999_, 0, v_toSeq_4989_);
                v___x_5000_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5000_, 0, v___x_4996_);
                crate::leanh::lean_ctor_set(v___x_5000_, 1, v___f_4992_);
                crate::leanh::lean_ctor_set(v___x_5000_, 2, v___f_4999_);
                crate::leanh::lean_ctor_set(v___x_5000_, 3, v___f_4998_);
                crate::leanh::lean_ctor_set(v___x_5000_, 4, v___f_4997_);
                v___x_5001_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5001_, 0, v___x_5000_);
                crate::leanh::lean_ctor_set(v___x_5001_, 1, v___f_4993_);
                v___x_5002_ = l_StateRefT_x27_instMonad___redArg(v___x_5001_);
                v_toApplicative_5003_ = crate::leanh::lean_ctor_get(v___x_5002_, 0);
                v_isSharedCheck_5076_ = (!crate::leanh::lean_is_exclusive(v___x_5002_)) as u8;
                if v_isSharedCheck_5076_ == 0 {
                    v_unused_5077_ = crate::leanh::lean_ctor_get(v___x_5002_, 1);
                    crate::leanh::lean_dec(v_unused_5077_);
                    v___x_5005_ = v___x_5002_;
                    v_isShared_5006_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5003_);
                    crate::leanh::lean_dec(v___x_5002_);
                    v___x_5005_ = crate::leanh::lean_box(0);
                    v_isShared_5006_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5007_ = crate::leanh::lean_ctor_get(v_toApplicative_5003_, 0);
                v_toSeq_5008_ = crate::leanh::lean_ctor_get(v_toApplicative_5003_, 2);
                v_toSeqLeft_5009_ = crate::leanh::lean_ctor_get(v_toApplicative_5003_, 3);
                v_toSeqRight_5010_ = crate::leanh::lean_ctor_get(v_toApplicative_5003_, 4);
                v_isSharedCheck_5074_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5003_)) as u8;
                if v_isSharedCheck_5074_ == 0 {
                    v_unused_5075_ = crate::leanh::lean_ctor_get(v_toApplicative_5003_, 1);
                    crate::leanh::lean_dec(v_unused_5075_);
                    v___x_5012_ = v_toApplicative_5003_;
                    v_isShared_5013_ = v_isSharedCheck_5074_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5010_);
                    crate::leanh::lean_inc(v_toSeqLeft_5009_);
                    crate::leanh::lean_inc(v_toSeq_5008_);
                    crate::leanh::lean_inc(v_toFunctor_5007_);
                    crate::leanh::lean_dec(v_toApplicative_5003_);
                    v___x_5012_ = crate::leanh::lean_box(0);
                    v_isShared_5013_ = v_isSharedCheck_5074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5014_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4;
                v___f_5015_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5;
                v___f_5016_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6;
                crate::leanh::lean_inc_ref(v_toFunctor_5007_);
                v___f_5017_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5017_, 0, v_toFunctor_5007_);
                v___f_5018_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5018_, 0, v_toFunctor_5007_);
                v___x_5019_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5019_, 0, v___f_5017_);
                crate::leanh::lean_ctor_set(v___x_5019_, 1, v___f_5018_);
                v___f_5020_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5020_, 0, v_toSeqRight_5010_);
                v___f_5021_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5021_, 0, v_toSeqLeft_5009_);
                v___f_5022_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5022_, 0, v_toSeq_5008_);
                if v_isShared_5013_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5012_, 4, v___f_5020_);
                    crate::leanh::lean_ctor_set(v___x_5012_, 3, v___f_5021_);
                    crate::leanh::lean_ctor_set(v___x_5012_, 2, v___f_5022_);
                    crate::leanh::lean_ctor_set(v___x_5012_, 1, v___f_5015_);
                    crate::leanh::lean_ctor_set(v___x_5012_, 0, v___x_5019_);
                    v___x_5024_ = v___x_5012_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5073_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5019_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 1, v___f_5015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 2, v___f_5022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 3, v___f_5021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 4, v___f_5020_);
                    v___x_5024_ = v_reuseFailAlloc_5073_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5006_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5005_, 1, v___f_5016_);
                    crate::leanh::lean_ctor_set(v___x_5005_, 0, v___x_5024_);
                    v___x_5026_ = v___x_5005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___f_5016_);
                    v___x_5026_ = v_reuseFailAlloc_5072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5027_ = l_ReaderT_instMonad___redArg(v___x_5026_);
                v___x_5028_ = l_StateRefT_x27_instMonad___redArg(v___x_5027_);
                v___x_5029_ = l_ReaderT_instMonad___redArg(v___x_5028_);
                v___x_5030_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5031_ = lean_array_get_size(v_params_4976_);
                v___x_5060_ = lean_nat_dec_lt(v___x_5030_, v___x_5031_);
                if v___x_5060_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5029_);
                    state = 5;
                    continue;
                } else {
                    v___f_5061_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17;
                    v___x_5062_ = crate::leanh::lean_box(0);
                    v___x_5063_ = lean_nat_dec_le(v___x_5031_, v___x_5031_);
                    if v___x_5063_ == 0 {
                        if v___x_5060_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5029_);
                            state = 5;
                            continue;
                        } else {
                            v___x_5064_ = 0usize;
                            v___x_5065_ = lean_usize_of_nat(v___x_5031_);
                            crate::leanh::lean_inc_ref(v_params_4976_);
                            v___x_1277__overap_5066_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_5029_,
                                    v___f_5061_,
                                    v_params_4976_,
                                    v___x_5064_,
                                    v___x_5065_,
                                    v___x_5062_,
                                );
                            crate::leanh::lean_inc(v_a_4984_);
                            crate::leanh::lean_inc_ref(v_a_4983_);
                            crate::leanh::lean_inc(v_a_4982_);
                            crate::leanh::lean_inc_ref(v_a_4981_);
                            crate::leanh::lean_inc_ref(v_a_4980_);
                            crate::leanh::lean_inc(v_a_4979_);
                            crate::leanh::lean_inc_ref(v_a_4978_);
                            v___x_5067_ = crate::leanh::lean_apply_8(
                                v___x_1277__overap_5066_,
                                v_a_4978_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_5051_ = v___x_5067_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_5068_ = 0usize;
                        v___x_5069_ = lean_usize_of_nat(v___x_5031_);
                        crate::leanh::lean_inc_ref(v_params_4976_);
                        v___x_1281__overap_5070_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_5029_,
                                v___f_5061_,
                                v_params_4976_,
                                v___x_5068_,
                                v___x_5069_,
                                v___x_5062_,
                            );
                        crate::leanh::lean_inc(v_a_4984_);
                        crate::leanh::lean_inc_ref(v_a_4983_);
                        crate::leanh::lean_inc(v_a_4982_);
                        crate::leanh::lean_inc_ref(v_a_4981_);
                        crate::leanh::lean_inc_ref(v_a_4980_);
                        crate::leanh::lean_inc(v_a_4979_);
                        crate::leanh::lean_inc_ref(v_a_4978_);
                        v___x_5071_ = crate::leanh::lean_apply_8(
                            v___x_1281__overap_5070_,
                            v_a_4978_,
                            v_a_4979_,
                            v_a_4980_,
                            v_a_4981_,
                            v_a_4982_,
                            v_a_4983_,
                            v_a_4984_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_5051_ = v___x_5071_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_jps_5033_ = crate::leanh::lean_ctor_get(v_a_4978_, 0);
                v_vars_5034_ = crate::leanh::lean_ctor_get(v_a_4978_, 1);
                v___x_5035_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16;
                v___x_5036_ = lean_nat_dec_lt(v___x_5030_, v___x_5031_);
                if v___x_5036_ == 0 {
                    crate::leanh::lean_dec_ref(v_params_4976_);
                    crate::leanh::lean_inc(v_a_4984_);
                    crate::leanh::lean_inc_ref(v_a_4983_);
                    crate::leanh::lean_inc(v_a_4982_);
                    crate::leanh::lean_inc_ref(v_a_4981_);
                    crate::leanh::lean_inc_ref(v_a_4980_);
                    crate::leanh::lean_inc(v_a_4979_);
                    crate::leanh::lean_inc_ref(v_a_4978_);
                    v___x_5037_ = crate::leanh::lean_apply_8(
                        v_x_4977_,
                        v_a_4978_,
                        v_a_4979_,
                        v_a_4980_,
                        v_a_4981_,
                        v_a_4982_,
                        v_a_4983_,
                        v_a_4984_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5037_;
                } else {
                    v___x_5038_ = lean_nat_dec_le(v___x_5031_, v___x_5031_);
                    if v___x_5038_ == 0 {
                        if v___x_5036_ == 0 {
                            crate::leanh::lean_dec_ref(v_params_4976_);
                            crate::leanh::lean_inc(v_a_4984_);
                            crate::leanh::lean_inc_ref(v_a_4983_);
                            crate::leanh::lean_inc(v_a_4982_);
                            crate::leanh::lean_inc_ref(v_a_4981_);
                            crate::leanh::lean_inc_ref(v_a_4980_);
                            crate::leanh::lean_inc(v_a_4979_);
                            crate::leanh::lean_inc_ref(v_a_4978_);
                            v___x_5039_ = crate::leanh::lean_apply_8(
                                v_x_4977_,
                                v_a_4978_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5039_;
                        } else {
                            v___x_5040_ = 0usize;
                            v___x_5041_ = lean_usize_of_nat(v___x_5031_);
                            crate::leanh::lean_inc(v_vars_5034_);
                            v___x_5042_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_5035_,
                                    v___f_5014_,
                                    v_params_4976_,
                                    v___x_5040_,
                                    v___x_5041_,
                                    v_vars_5034_,
                                );
                            crate::leanh::lean_inc(v_jps_5033_);
                            v___x_5043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5043_, 0, v_jps_5033_);
                            crate::leanh::lean_ctor_set(v___x_5043_, 1, v___x_5042_);
                            crate::leanh::lean_inc(v_a_4984_);
                            crate::leanh::lean_inc_ref(v_a_4983_);
                            crate::leanh::lean_inc(v_a_4982_);
                            crate::leanh::lean_inc_ref(v_a_4981_);
                            crate::leanh::lean_inc_ref(v_a_4980_);
                            crate::leanh::lean_inc(v_a_4979_);
                            v___x_5044_ = crate::leanh::lean_apply_8(
                                v_x_4977_,
                                v___x_5043_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5044_;
                        }
                    } else {
                        v___x_5045_ = 0usize;
                        v___x_5046_ = lean_usize_of_nat(v___x_5031_);
                        crate::leanh::lean_inc(v_vars_5034_);
                        v___x_5047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_5035_,
                            v___f_5014_,
                            v_params_4976_,
                            v___x_5045_,
                            v___x_5046_,
                            v_vars_5034_,
                        );
                        crate::leanh::lean_inc(v_jps_5033_);
                        v___x_5048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5048_, 0, v_jps_5033_);
                        crate::leanh::lean_ctor_set(v___x_5048_, 1, v___x_5047_);
                        crate::leanh::lean_inc(v_a_4984_);
                        crate::leanh::lean_inc_ref(v_a_4983_);
                        crate::leanh::lean_inc(v_a_4982_);
                        crate::leanh::lean_inc_ref(v_a_4981_);
                        crate::leanh::lean_inc_ref(v_a_4980_);
                        crate::leanh::lean_inc(v_a_4979_);
                        v___x_5049_ = crate::leanh::lean_apply_8(
                            v_x_4977_,
                            v___x_5048_,
                            v_a_4979_,
                            v_a_4980_,
                            v_a_4981_,
                            v_a_4982_,
                            v_a_4983_,
                            v_a_4984_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_5049_;
                    }
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_5051_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_5051_, 1);
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_x_4977_);
                    crate::leanh::lean_dec_ref(v_params_4976_);
                    v_a_5052_ = crate::leanh::lean_ctor_get(v___y_5051_, 0);
                    v_isSharedCheck_5059_ = (!crate::leanh::lean_is_exclusive(v___y_5051_)) as u8;
                    if v_isSharedCheck_5059_ == 0 {
                        v___x_5054_ = v___y_5051_;
                        v_isShared_5055_ = v_isSharedCheck_5059_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5052_);
                        crate::leanh::lean_dec(v___y_5051_);
                        v___x_5054_ = crate::leanh::lean_box(0);
                        v_isShared_5055_ = v_isSharedCheck_5059_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5055_ == 0 {
                    v___x_5057_ = v___x_5054_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
                    v___x_5057_ = v_reuseFailAlloc_5058_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___boxed(
    mut v_params_5078_: *mut crate::leanh::LeanObject,
    mut v_x_5079_: *mut crate::leanh::LeanObject,
    mut v_a_5080_: *mut crate::leanh::LeanObject,
    mut v_a_5081_: *mut crate::leanh::LeanObject,
    mut v_a_5082_: *mut crate::leanh::LeanObject,
    mut v_a_5083_: *mut crate::leanh::LeanObject,
    mut v_a_5084_: *mut crate::leanh::LeanObject,
    mut v_a_5085_: *mut crate::leanh::LeanObject,
    mut v_a_5086_: *mut crate::leanh::LeanObject,
    mut v_a_5087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5088_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg(
        v_params_5078_,
        v_x_5079_,
        v_a_5080_,
        v_a_5081_,
        v_a_5082_,
        v_a_5083_,
        v_a_5084_,
        v_a_5085_,
        v_a_5086_,
    );
    crate::leanh::lean_dec(v_a_5086_);
    crate::leanh::lean_dec_ref(v_a_5085_);
    crate::leanh::lean_dec(v_a_5084_);
    crate::leanh::lean_dec_ref(v_a_5083_);
    crate::leanh::lean_dec_ref(v_a_5082_);
    crate::leanh::lean_dec(v_a_5081_);
    crate::leanh::lean_dec_ref(v_a_5080_);
    return v_res_5088_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams(
    mut v_00_u03b1_5089_: *mut crate::leanh::LeanObject,
    mut v_params_5090_: *mut crate::leanh::LeanObject,
    mut v_x_5091_: *mut crate::leanh::LeanObject,
    mut v_a_5092_: *mut crate::leanh::LeanObject,
    mut v_a_5093_: *mut crate::leanh::LeanObject,
    mut v_a_5094_: *mut crate::leanh::LeanObject,
    mut v_a_5095_: *mut crate::leanh::LeanObject,
    mut v_a_5096_: *mut crate::leanh::LeanObject,
    mut v_a_5097_: *mut crate::leanh::LeanObject,
    mut v_a_5098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v_toFunctor_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v___f_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: u8 = 0;
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: usize = 0;
    let mut v___x_5155_: usize = 0;
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: usize = 0;
    let mut v___x_5160_: usize = 0;
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5169_: u8 = 0;
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v___x_5174_: u8 = 0;
    let mut v___f_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: u8 = 0;
    let mut v___x_5178_: usize = 0;
    let mut v___x_5179_: usize = 0;
    let mut v___x_1403__overap_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: usize = 0;
    let mut v___x_5183_: usize = 0;
    let mut v___x_1406__overap_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v_unused_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5190_: u8 = 0;
    let mut v_unused_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5100_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1,
                );
                v_toApplicative_5101_ = crate::leanh::lean_ctor_get(v___x_5100_, 0);
                v_toFunctor_5102_ = crate::leanh::lean_ctor_get(v_toApplicative_5101_, 0);
                v_toSeq_5103_ = crate::leanh::lean_ctor_get(v_toApplicative_5101_, 2);
                v_toSeqLeft_5104_ = crate::leanh::lean_ctor_get(v_toApplicative_5101_, 3);
                v_toSeqRight_5105_ = crate::leanh::lean_ctor_get(v_toApplicative_5101_, 4);
                v___f_5106_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2;
                v___f_5107_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_5102_, 2);
                v___f_5108_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5108_, 0, v_toFunctor_5102_);
                v___f_5109_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5109_, 0, v_toFunctor_5102_);
                v___x_5110_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5110_, 0, v___f_5108_);
                crate::leanh::lean_ctor_set(v___x_5110_, 1, v___f_5109_);
                crate::leanh::lean_inc(v_toSeqRight_5105_);
                v___f_5111_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5111_, 0, v_toSeqRight_5105_);
                crate::leanh::lean_inc(v_toSeqLeft_5104_);
                v___f_5112_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5112_, 0, v_toSeqLeft_5104_);
                crate::leanh::lean_inc(v_toSeq_5103_);
                v___f_5113_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5113_, 0, v_toSeq_5103_);
                v___x_5114_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5114_, 0, v___x_5110_);
                crate::leanh::lean_ctor_set(v___x_5114_, 1, v___f_5106_);
                crate::leanh::lean_ctor_set(v___x_5114_, 2, v___f_5113_);
                crate::leanh::lean_ctor_set(v___x_5114_, 3, v___f_5112_);
                crate::leanh::lean_ctor_set(v___x_5114_, 4, v___f_5111_);
                v___x_5115_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5115_, 0, v___x_5114_);
                crate::leanh::lean_ctor_set(v___x_5115_, 1, v___f_5107_);
                v___x_5116_ = l_StateRefT_x27_instMonad___redArg(v___x_5115_);
                v_toApplicative_5117_ = crate::leanh::lean_ctor_get(v___x_5116_, 0);
                v_isSharedCheck_5190_ = (!crate::leanh::lean_is_exclusive(v___x_5116_)) as u8;
                if v_isSharedCheck_5190_ == 0 {
                    v_unused_5191_ = crate::leanh::lean_ctor_get(v___x_5116_, 1);
                    crate::leanh::lean_dec(v_unused_5191_);
                    v___x_5119_ = v___x_5116_;
                    v_isShared_5120_ = v_isSharedCheck_5190_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5117_);
                    crate::leanh::lean_dec(v___x_5116_);
                    v___x_5119_ = crate::leanh::lean_box(0);
                    v_isShared_5120_ = v_isSharedCheck_5190_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5121_ = crate::leanh::lean_ctor_get(v_toApplicative_5117_, 0);
                v_toSeq_5122_ = crate::leanh::lean_ctor_get(v_toApplicative_5117_, 2);
                v_toSeqLeft_5123_ = crate::leanh::lean_ctor_get(v_toApplicative_5117_, 3);
                v_toSeqRight_5124_ = crate::leanh::lean_ctor_get(v_toApplicative_5117_, 4);
                v_isSharedCheck_5188_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5117_)) as u8;
                if v_isSharedCheck_5188_ == 0 {
                    v_unused_5189_ = crate::leanh::lean_ctor_get(v_toApplicative_5117_, 1);
                    crate::leanh::lean_dec(v_unused_5189_);
                    v___x_5126_ = v_toApplicative_5117_;
                    v_isShared_5127_ = v_isSharedCheck_5188_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5124_);
                    crate::leanh::lean_inc(v_toSeqLeft_5123_);
                    crate::leanh::lean_inc(v_toSeq_5122_);
                    crate::leanh::lean_inc(v_toFunctor_5121_);
                    crate::leanh::lean_dec(v_toApplicative_5117_);
                    v___x_5126_ = crate::leanh::lean_box(0);
                    v_isShared_5127_ = v_isSharedCheck_5188_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5128_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4;
                v___f_5129_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5;
                v___f_5130_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6;
                crate::leanh::lean_inc_ref(v_toFunctor_5121_);
                v___f_5131_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5131_, 0, v_toFunctor_5121_);
                v___f_5132_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5132_, 0, v_toFunctor_5121_);
                v___x_5133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5133_, 0, v___f_5131_);
                crate::leanh::lean_ctor_set(v___x_5133_, 1, v___f_5132_);
                v___f_5134_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5134_, 0, v_toSeqRight_5124_);
                v___f_5135_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5135_, 0, v_toSeqLeft_5123_);
                v___f_5136_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5136_, 0, v_toSeq_5122_);
                if v_isShared_5127_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5126_, 4, v___f_5134_);
                    crate::leanh::lean_ctor_set(v___x_5126_, 3, v___f_5135_);
                    crate::leanh::lean_ctor_set(v___x_5126_, 2, v___f_5136_);
                    crate::leanh::lean_ctor_set(v___x_5126_, 1, v___f_5129_);
                    crate::leanh::lean_ctor_set(v___x_5126_, 0, v___x_5133_);
                    v___x_5138_ = v___x_5126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 1, v___f_5129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 2, v___f_5136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 3, v___f_5135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 4, v___f_5134_);
                    v___x_5138_ = v_reuseFailAlloc_5187_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5120_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5119_, 1, v___f_5130_);
                    crate::leanh::lean_ctor_set(v___x_5119_, 0, v___x_5138_);
                    v___x_5140_ = v___x_5119_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5186_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5186_, 1, v___f_5130_);
                    v___x_5140_ = v_reuseFailAlloc_5186_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5141_ = l_ReaderT_instMonad___redArg(v___x_5140_);
                v___x_5142_ = l_StateRefT_x27_instMonad___redArg(v___x_5141_);
                v___x_5143_ = l_ReaderT_instMonad___redArg(v___x_5142_);
                v___x_5144_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5145_ = lean_array_get_size(v_params_5090_);
                v___x_5174_ = lean_nat_dec_lt(v___x_5144_, v___x_5145_);
                if v___x_5174_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5143_);
                    state = 5;
                    continue;
                } else {
                    v___f_5175_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17;
                    v___x_5176_ = crate::leanh::lean_box(0);
                    v___x_5177_ = lean_nat_dec_le(v___x_5145_, v___x_5145_);
                    if v___x_5177_ == 0 {
                        if v___x_5174_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5143_);
                            state = 5;
                            continue;
                        } else {
                            v___x_5178_ = 0usize;
                            v___x_5179_ = lean_usize_of_nat(v___x_5145_);
                            crate::leanh::lean_inc_ref(v_params_5090_);
                            v___x_1403__overap_5180_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_5143_,
                                    v___f_5175_,
                                    v_params_5090_,
                                    v___x_5178_,
                                    v___x_5179_,
                                    v___x_5176_,
                                );
                            crate::leanh::lean_inc(v_a_5098_);
                            crate::leanh::lean_inc_ref(v_a_5097_);
                            crate::leanh::lean_inc(v_a_5096_);
                            crate::leanh::lean_inc_ref(v_a_5095_);
                            crate::leanh::lean_inc_ref(v_a_5094_);
                            crate::leanh::lean_inc(v_a_5093_);
                            crate::leanh::lean_inc_ref(v_a_5092_);
                            v___x_5181_ = crate::leanh::lean_apply_8(
                                v___x_1403__overap_5180_,
                                v_a_5092_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_5165_ = v___x_5181_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_5182_ = 0usize;
                        v___x_5183_ = lean_usize_of_nat(v___x_5145_);
                        crate::leanh::lean_inc_ref(v_params_5090_);
                        v___x_1406__overap_5184_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_5143_,
                                v___f_5175_,
                                v_params_5090_,
                                v___x_5182_,
                                v___x_5183_,
                                v___x_5176_,
                            );
                        crate::leanh::lean_inc(v_a_5098_);
                        crate::leanh::lean_inc_ref(v_a_5097_);
                        crate::leanh::lean_inc(v_a_5096_);
                        crate::leanh::lean_inc_ref(v_a_5095_);
                        crate::leanh::lean_inc_ref(v_a_5094_);
                        crate::leanh::lean_inc(v_a_5093_);
                        crate::leanh::lean_inc_ref(v_a_5092_);
                        v___x_5185_ = crate::leanh::lean_apply_8(
                            v___x_1406__overap_5184_,
                            v_a_5092_,
                            v_a_5093_,
                            v_a_5094_,
                            v_a_5095_,
                            v_a_5096_,
                            v_a_5097_,
                            v_a_5098_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_5165_ = v___x_5185_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_jps_5147_ = crate::leanh::lean_ctor_get(v_a_5092_, 0);
                v_vars_5148_ = crate::leanh::lean_ctor_get(v_a_5092_, 1);
                v___x_5149_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16;
                v___x_5150_ = lean_nat_dec_lt(v___x_5144_, v___x_5145_);
                if v___x_5150_ == 0 {
                    crate::leanh::lean_dec_ref(v_params_5090_);
                    crate::leanh::lean_inc(v_a_5098_);
                    crate::leanh::lean_inc_ref(v_a_5097_);
                    crate::leanh::lean_inc(v_a_5096_);
                    crate::leanh::lean_inc_ref(v_a_5095_);
                    crate::leanh::lean_inc_ref(v_a_5094_);
                    crate::leanh::lean_inc(v_a_5093_);
                    crate::leanh::lean_inc_ref(v_a_5092_);
                    v___x_5151_ = crate::leanh::lean_apply_8(
                        v_x_5091_,
                        v_a_5092_,
                        v_a_5093_,
                        v_a_5094_,
                        v_a_5095_,
                        v_a_5096_,
                        v_a_5097_,
                        v_a_5098_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5151_;
                } else {
                    v___x_5152_ = lean_nat_dec_le(v___x_5145_, v___x_5145_);
                    if v___x_5152_ == 0 {
                        if v___x_5150_ == 0 {
                            crate::leanh::lean_dec_ref(v_params_5090_);
                            crate::leanh::lean_inc(v_a_5098_);
                            crate::leanh::lean_inc_ref(v_a_5097_);
                            crate::leanh::lean_inc(v_a_5096_);
                            crate::leanh::lean_inc_ref(v_a_5095_);
                            crate::leanh::lean_inc_ref(v_a_5094_);
                            crate::leanh::lean_inc(v_a_5093_);
                            crate::leanh::lean_inc_ref(v_a_5092_);
                            v___x_5153_ = crate::leanh::lean_apply_8(
                                v_x_5091_,
                                v_a_5092_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5153_;
                        } else {
                            v___x_5154_ = 0usize;
                            v___x_5155_ = lean_usize_of_nat(v___x_5145_);
                            crate::leanh::lean_inc(v_vars_5148_);
                            v___x_5156_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_5149_,
                                    v___f_5128_,
                                    v_params_5090_,
                                    v___x_5154_,
                                    v___x_5155_,
                                    v_vars_5148_,
                                );
                            crate::leanh::lean_inc(v_jps_5147_);
                            v___x_5157_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5157_, 0, v_jps_5147_);
                            crate::leanh::lean_ctor_set(v___x_5157_, 1, v___x_5156_);
                            crate::leanh::lean_inc(v_a_5098_);
                            crate::leanh::lean_inc_ref(v_a_5097_);
                            crate::leanh::lean_inc(v_a_5096_);
                            crate::leanh::lean_inc_ref(v_a_5095_);
                            crate::leanh::lean_inc_ref(v_a_5094_);
                            crate::leanh::lean_inc(v_a_5093_);
                            v___x_5158_ = crate::leanh::lean_apply_8(
                                v_x_5091_,
                                v___x_5157_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5158_;
                        }
                    } else {
                        v___x_5159_ = 0usize;
                        v___x_5160_ = lean_usize_of_nat(v___x_5145_);
                        crate::leanh::lean_inc(v_vars_5148_);
                        v___x_5161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_5149_,
                            v___f_5128_,
                            v_params_5090_,
                            v___x_5159_,
                            v___x_5160_,
                            v_vars_5148_,
                        );
                        crate::leanh::lean_inc(v_jps_5147_);
                        v___x_5162_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5162_, 0, v_jps_5147_);
                        crate::leanh::lean_ctor_set(v___x_5162_, 1, v___x_5161_);
                        crate::leanh::lean_inc(v_a_5098_);
                        crate::leanh::lean_inc_ref(v_a_5097_);
                        crate::leanh::lean_inc(v_a_5096_);
                        crate::leanh::lean_inc_ref(v_a_5095_);
                        crate::leanh::lean_inc_ref(v_a_5094_);
                        crate::leanh::lean_inc(v_a_5093_);
                        v___x_5163_ = crate::leanh::lean_apply_8(
                            v_x_5091_,
                            v___x_5162_,
                            v_a_5093_,
                            v_a_5094_,
                            v_a_5095_,
                            v_a_5096_,
                            v_a_5097_,
                            v_a_5098_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_5163_;
                    }
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_5165_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_5165_, 1);
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_x_5091_);
                    crate::leanh::lean_dec_ref(v_params_5090_);
                    v_a_5166_ = crate::leanh::lean_ctor_get(v___y_5165_, 0);
                    v_isSharedCheck_5173_ = (!crate::leanh::lean_is_exclusive(v___y_5165_)) as u8;
                    if v_isSharedCheck_5173_ == 0 {
                        v___x_5168_ = v___y_5165_;
                        v_isShared_5169_ = v_isSharedCheck_5173_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5166_);
                        crate::leanh::lean_dec(v___y_5165_);
                        v___x_5168_ = crate::leanh::lean_box(0);
                        v_isShared_5169_ = v_isSharedCheck_5173_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5169_ == 0 {
                    v___x_5171_ = v___x_5168_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
                    v___x_5171_ = v_reuseFailAlloc_5172_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___boxed(
    mut v_00_u03b1_5192_: *mut crate::leanh::LeanObject,
    mut v_params_5193_: *mut crate::leanh::LeanObject,
    mut v_x_5194_: *mut crate::leanh::LeanObject,
    mut v_a_5195_: *mut crate::leanh::LeanObject,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
    mut v_a_5197_: *mut crate::leanh::LeanObject,
    mut v_a_5198_: *mut crate::leanh::LeanObject,
    mut v_a_5199_: *mut crate::leanh::LeanObject,
    mut v_a_5200_: *mut crate::leanh::LeanObject,
    mut v_a_5201_: *mut crate::leanh::LeanObject,
    mut v_a_5202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5203_ = l_Lean_Compiler_LCNF_Check_Pure_withParams(
        v_00_u03b1_5192_,
        v_params_5193_,
        v_x_5194_,
        v_a_5195_,
        v_a_5196_,
        v_a_5197_,
        v_a_5198_,
        v_a_5199_,
        v_a_5200_,
        v_a_5201_,
    );
    crate::leanh::lean_dec(v_a_5201_);
    crate::leanh::lean_dec_ref(v_a_5200_);
    crate::leanh::lean_dec(v_a_5199_);
    crate::leanh::lean_dec_ref(v_a_5198_);
    crate::leanh::lean_dec_ref(v_a_5197_);
    crate::leanh::lean_dec(v_a_5196_);
    crate::leanh::lean_dec_ref(v_a_5195_);
    return v_res_5203_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(
    mut v_ref_5204_: *mut crate::leanh::LeanObject,
    mut v_msg_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5223_: u8 = 0;
    let mut v_cancelTk_x3f_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5225_: u8 = 0;
    let mut v_inheritedTraceOptions_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5211_ = crate::leanh::lean_ctor_get(v___y_5208_, 0);
    v_fileMap_5212_ = crate::leanh::lean_ctor_get(v___y_5208_, 1);
    v_options_5213_ = crate::leanh::lean_ctor_get(v___y_5208_, 2);
    v_currRecDepth_5214_ = crate::leanh::lean_ctor_get(v___y_5208_, 3);
    v_maxRecDepth_5215_ = crate::leanh::lean_ctor_get(v___y_5208_, 4);
    v_ref_5216_ = crate::leanh::lean_ctor_get(v___y_5208_, 5);
    v_currNamespace_5217_ = crate::leanh::lean_ctor_get(v___y_5208_, 6);
    v_openDecls_5218_ = crate::leanh::lean_ctor_get(v___y_5208_, 7);
    v_initHeartbeats_5219_ = crate::leanh::lean_ctor_get(v___y_5208_, 8);
    v_maxHeartbeats_5220_ = crate::leanh::lean_ctor_get(v___y_5208_, 9);
    v_quotContext_5221_ = crate::leanh::lean_ctor_get(v___y_5208_, 10);
    v_currMacroScope_5222_ = crate::leanh::lean_ctor_get(v___y_5208_, 11);
    v_diag_5223_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5208_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5224_ = crate::leanh::lean_ctor_get(v___y_5208_, 12);
    v_suppressElabErrors_5225_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5208_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5226_ = crate::leanh::lean_ctor_get(v___y_5208_, 13);
    v_ref_5227_ = l_Lean_replaceRef(v_ref_5204_, v_ref_5216_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5226_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5224_);
    crate::leanh::lean_inc(v_currMacroScope_5222_);
    crate::leanh::lean_inc(v_quotContext_5221_);
    crate::leanh::lean_inc(v_maxHeartbeats_5220_);
    crate::leanh::lean_inc(v_initHeartbeats_5219_);
    crate::leanh::lean_inc(v_openDecls_5218_);
    crate::leanh::lean_inc(v_currNamespace_5217_);
    crate::leanh::lean_inc(v_maxRecDepth_5215_);
    crate::leanh::lean_inc(v_currRecDepth_5214_);
    crate::leanh::lean_inc_ref(v_options_5213_);
    crate::leanh::lean_inc_ref(v_fileMap_5212_);
    crate::leanh::lean_inc_ref(v_fileName_5211_);
    v___x_5228_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5228_, 0, v_fileName_5211_);
    crate::leanh::lean_ctor_set(v___x_5228_, 1, v_fileMap_5212_);
    crate::leanh::lean_ctor_set(v___x_5228_, 2, v_options_5213_);
    crate::leanh::lean_ctor_set(v___x_5228_, 3, v_currRecDepth_5214_);
    crate::leanh::lean_ctor_set(v___x_5228_, 4, v_maxRecDepth_5215_);
    crate::leanh::lean_ctor_set(v___x_5228_, 5, v_ref_5227_);
    crate::leanh::lean_ctor_set(v___x_5228_, 6, v_currNamespace_5217_);
    crate::leanh::lean_ctor_set(v___x_5228_, 7, v_openDecls_5218_);
    crate::leanh::lean_ctor_set(v___x_5228_, 8, v_initHeartbeats_5219_);
    crate::leanh::lean_ctor_set(v___x_5228_, 9, v_maxHeartbeats_5220_);
    crate::leanh::lean_ctor_set(v___x_5228_, 10, v_quotContext_5221_);
    crate::leanh::lean_ctor_set(v___x_5228_, 11, v_currMacroScope_5222_);
    crate::leanh::lean_ctor_set(v___x_5228_, 12, v_cancelTk_x3f_5224_);
    crate::leanh::lean_ctor_set(v___x_5228_, 13, v_inheritedTraceOptions_5226_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5228_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5223_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5228_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5225_,
    );
    v___x_5229_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
            v_msg_5205_,
            v___y_5206_,
            v___y_5207_,
            v___x_5228_,
            v___y_5209_,
        );
    crate::leanh::lean_dec_ref_known(v___x_5228_, 14);
    return v___x_5229_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg___boxed(
    mut v_ref_5230_: *mut crate::leanh::LeanObject,
    mut v_msg_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
    mut v___y_5233_: *mut crate::leanh::LeanObject,
    mut v___y_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
    mut v___y_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5237_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_5230_, v_msg_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
    crate::leanh::lean_dec(v___y_5235_);
    crate::leanh::lean_dec_ref(v___y_5234_);
    crate::leanh::lean_dec(v___y_5233_);
    crate::leanh::lean_dec_ref(v___y_5232_);
    crate::leanh::lean_dec(v_ref_5230_);
    return v_res_5237_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(
    mut v_msg_5238_: *mut crate::leanh::LeanObject,
    mut v_declHint_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: u8 = 0;
    let mut v_isExporting_5245_: u8 = 0;
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u8 = 0;
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: u8 = 0;
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5242_ = lean_st_ref_get(v___y_5240_);
                v_env_5243_ = crate::leanh::lean_ctor_get(v___x_5242_, 0);
                crate::leanh::lean_inc_ref(v_env_5243_);
                crate::leanh::lean_dec(v___x_5242_);
                v___x_5244_ = l_Lean_Name_isAnonymous(v_declHint_5239_);
                if v___x_5244_ == 0 {
                    v_isExporting_5245_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_5243_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5245_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_5243_);
                        crate::leanh::lean_dec(v_declHint_5239_);
                        v___x_5246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5246_, 0, v_msg_5238_);
                        return v___x_5246_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_5243_);
                        v___x_5247_ = l_Lean_Environment_setExporting(v_env_5243_, v___x_5244_);
                        crate::leanh::lean_inc(v_declHint_5239_);
                        crate::leanh::lean_inc_ref(v___x_5247_);
                        v___x_5248_ = l_Lean_Environment_contains(
                            v___x_5247_,
                            v_declHint_5239_,
                            v_isExporting_5245_,
                        );
                        if v___x_5248_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5247_);
                            crate::leanh::lean_dec_ref(v_env_5243_);
                            crate::leanh::lean_dec(v_declHint_5239_);
                            v___x_5249_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5249_, 0, v_msg_5238_);
                            return v___x_5249_;
                        } else {
                            v___x_5250_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                            v___x_5251_ = crate::leanh::lean_unsigned_to_nat(32);
                            v___x_5252_ = lean_mk_empty_array_with_capacity(v___x_5251_);
                            crate::leanh::lean_dec_ref(v___x_5252_);
                            v___x_5253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_5254_ = l_Lean_Options_empty;
                            v___x_5255_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5255_, 0, v___x_5247_);
                            crate::leanh::lean_ctor_set(v___x_5255_, 1, v___x_5250_);
                            crate::leanh::lean_ctor_set(v___x_5255_, 2, v___x_5253_);
                            crate::leanh::lean_ctor_set(v___x_5255_, 3, v___x_5254_);
                            crate::leanh::lean_inc(v_declHint_5239_);
                            v___x_5256_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5239_, v___x_5244_);
                            v_c_5257_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_5257_, 0, v___x_5255_);
                            crate::leanh::lean_ctor_set(v_c_5257_, 1, v___x_5256_);
                            v___x_5258_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5243_,
                                v_declHint_5239_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5258_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_5243_);
                                crate::leanh::lean_dec(v_declHint_5239_);
                                v___x_5259_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_5260_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5260_, 0, v___x_5259_);
                                crate::leanh::lean_ctor_set(v___x_5260_, 1, v_c_5257_);
                                v___x_5261_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_5262_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5262_, 0, v___x_5260_);
                                crate::leanh::lean_ctor_set(v___x_5262_, 1, v___x_5261_);
                                v___x_5263_ = l_Lean_MessageData_note(v___x_5262_);
                                v___x_5264_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5264_, 0, v_msg_5238_);
                                crate::leanh::lean_ctor_set(v___x_5264_, 1, v___x_5263_);
                                v___x_5265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5265_, 0, v___x_5264_);
                                return v___x_5265_;
                            } else {
                                v_val_5266_ = crate::leanh::lean_ctor_get(v___x_5258_, 0);
                                v_isSharedCheck_5301_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5258_)) as u8;
                                if v_isSharedCheck_5301_ == 0 {
                                    v___x_5268_ = v___x_5258_;
                                    v_isShared_5269_ = v_isSharedCheck_5301_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_5266_);
                                    crate::leanh::lean_dec(v___x_5258_);
                                    v___x_5268_ = crate::leanh::lean_box(0);
                                    v_isShared_5269_ = v_isSharedCheck_5301_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_5243_);
                    crate::leanh::lean_dec(v_declHint_5239_);
                    v___x_5302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5302_, 0, v_msg_5238_);
                    return v___x_5302_;
                }
            }
            1 => {
                v___x_5270_ = crate::leanh::lean_box(0);
                v___x_5271_ = l_Lean_Environment_header(v_env_5243_);
                crate::leanh::lean_dec_ref(v_env_5243_);
                v___x_5272_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5271_);
                v_mod_5273_ = lean_array_get(v___x_5270_, v___x_5272_, v_val_5266_);
                crate::leanh::lean_dec(v_val_5266_);
                crate::leanh::lean_dec_ref(v___x_5272_);
                v___x_5274_ = l_Lean_isPrivateName(v_declHint_5239_);
                crate::leanh::lean_dec(v_declHint_5239_);
                if v___x_5274_ == 0 {
                    v___x_5275_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_5276_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5276_, 0, v___x_5275_);
                    crate::leanh::lean_ctor_set(v___x_5276_, 1, v_c_5257_);
                    v___x_5277_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_5278_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5278_, 0, v___x_5276_);
                    crate::leanh::lean_ctor_set(v___x_5278_, 1, v___x_5277_);
                    v___x_5279_ = l_Lean_MessageData_ofName(v_mod_5273_);
                    v___x_5280_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5280_, 0, v___x_5278_);
                    crate::leanh::lean_ctor_set(v___x_5280_, 1, v___x_5279_);
                    v___x_5281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_5282_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5282_, 0, v___x_5280_);
                    crate::leanh::lean_ctor_set(v___x_5282_, 1, v___x_5281_);
                    v___x_5283_ = l_Lean_MessageData_note(v___x_5282_);
                    v___x_5284_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5284_, 0, v_msg_5238_);
                    crate::leanh::lean_ctor_set(v___x_5284_, 1, v___x_5283_);
                    if v_isShared_5269_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5268_, 0);
                        crate::leanh::lean_ctor_set(v___x_5268_, 0, v___x_5284_);
                        v___x_5286_ = v___x_5268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5284_);
                        v___x_5286_ = v_reuseFailAlloc_5287_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5288_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_5289_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5289_, 0, v___x_5288_);
                    crate::leanh::lean_ctor_set(v___x_5289_, 1, v_c_5257_);
                    v___x_5290_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_5291_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5291_, 0, v___x_5289_);
                    crate::leanh::lean_ctor_set(v___x_5291_, 1, v___x_5290_);
                    v___x_5292_ = l_Lean_MessageData_ofName(v_mod_5273_);
                    v___x_5293_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5293_, 0, v___x_5291_);
                    crate::leanh::lean_ctor_set(v___x_5293_, 1, v___x_5292_);
                    v___x_5294_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_5295_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5295_, 0, v___x_5293_);
                    crate::leanh::lean_ctor_set(v___x_5295_, 1, v___x_5294_);
                    v___x_5296_ = l_Lean_MessageData_note(v___x_5295_);
                    v___x_5297_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5297_, 0, v_msg_5238_);
                    crate::leanh::lean_ctor_set(v___x_5297_, 1, v___x_5296_);
                    if v_isShared_5269_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5268_, 0);
                        crate::leanh::lean_ctor_set(v___x_5268_, 0, v___x_5297_);
                        v___x_5299_ = v___x_5268_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5300_, 0, v___x_5297_);
                        v___x_5299_ = v_reuseFailAlloc_5300_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5286_;
            }
            3 => {
                return v___x_5299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg___boxed(
    mut v_msg_5303_: *mut crate::leanh::LeanObject,
    mut v_declHint_5304_: *mut crate::leanh::LeanObject,
    mut v___y_5305_: *mut crate::leanh::LeanObject,
    mut v___y_5306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_5303_, v_declHint_5304_, v___y_5305_);
    crate::leanh::lean_dec(v___y_5305_);
    return v_res_5307_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(
    mut v_msg_5308_: *mut crate::leanh::LeanObject,
    mut v_declHint_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5318_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_5308_, v_declHint_5309_, v___y_5316_);
                v_a_5319_ = crate::leanh::lean_ctor_get(v___x_5318_, 0);
                v_isSharedCheck_5328_ = (!crate::leanh::lean_is_exclusive(v___x_5318_)) as u8;
                if v_isSharedCheck_5328_ == 0 {
                    v___x_5321_ = v___x_5318_;
                    v_isShared_5322_ = v_isSharedCheck_5328_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5319_);
                    crate::leanh::lean_dec(v___x_5318_);
                    v___x_5321_ = crate::leanh::lean_box(0);
                    v_isShared_5322_ = v_isSharedCheck_5328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5323_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5324_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5324_, 0, v___x_5323_);
                crate::leanh::lean_ctor_set(v___x_5324_, 1, v_a_5319_);
                if v_isShared_5322_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5321_, 0, v___x_5324_);
                    v___x_5326_ = v___x_5321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
                    v___x_5326_ = v_reuseFailAlloc_5327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9___boxed(
    mut v_msg_5329_: *mut crate::leanh::LeanObject,
    mut v_declHint_5330_: *mut crate::leanh::LeanObject,
    mut v___y_5331_: *mut crate::leanh::LeanObject,
    mut v___y_5332_: *mut crate::leanh::LeanObject,
    mut v___y_5333_: *mut crate::leanh::LeanObject,
    mut v___y_5334_: *mut crate::leanh::LeanObject,
    mut v___y_5335_: *mut crate::leanh::LeanObject,
    mut v___y_5336_: *mut crate::leanh::LeanObject,
    mut v___y_5337_: *mut crate::leanh::LeanObject,
    mut v___y_5338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5339_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(v_msg_5329_, v_declHint_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
    crate::leanh::lean_dec(v___y_5337_);
    crate::leanh::lean_dec_ref(v___y_5336_);
    crate::leanh::lean_dec(v___y_5335_);
    crate::leanh::lean_dec_ref(v___y_5334_);
    crate::leanh::lean_dec_ref(v___y_5333_);
    crate::leanh::lean_dec(v___y_5332_);
    crate::leanh::lean_dec_ref(v___y_5331_);
    return v_res_5339_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(
    mut v_ref_5340_: *mut crate::leanh::LeanObject,
    mut v_msg_5341_: *mut crate::leanh::LeanObject,
    mut v_declHint_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5351_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(v_msg_5341_, v_declHint_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
    v_a_5352_ = crate::leanh::lean_ctor_get(v___x_5351_, 0);
    crate::leanh::lean_inc(v_a_5352_);
    crate::leanh::lean_dec_ref(v___x_5351_);
    v___x_5353_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_5340_, v_a_5352_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
    return v___x_5353_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_ref_5354_: *mut crate::leanh::LeanObject,
    mut v_msg_5355_: *mut crate::leanh::LeanObject,
    mut v_declHint_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
    mut v___y_5364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5365_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_5354_, v_msg_5355_, v_declHint_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
    crate::leanh::lean_dec(v___y_5363_);
    crate::leanh::lean_dec_ref(v___y_5362_);
    crate::leanh::lean_dec(v___y_5361_);
    crate::leanh::lean_dec_ref(v___y_5360_);
    crate::leanh::lean_dec_ref(v___y_5359_);
    crate::leanh::lean_dec(v___y_5358_);
    crate::leanh::lean_dec_ref(v___y_5357_);
    crate::leanh::lean_dec(v_ref_5354_);
    return v_res_5365_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(
    mut v_ref_5366_: *mut crate::leanh::LeanObject,
    mut v_constName_5367_: *mut crate::leanh::LeanObject,
    mut v___y_5368_: *mut crate::leanh::LeanObject,
    mut v___y_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5376_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_5377_ = 0;
    crate::leanh::lean_inc(v_constName_5367_);
    v___x_5378_ = l_Lean_MessageData_ofConstName(v_constName_5367_, v___x_5377_);
    v___x_5379_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5379_, 0, v___x_5376_);
    crate::leanh::lean_ctor_set(v___x_5379_, 1, v___x_5378_);
    v___x_5380_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_5381_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5381_, 0, v___x_5379_);
    crate::leanh::lean_ctor_set(v___x_5381_, 1, v___x_5380_);
    v___x_5382_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_5366_, v___x_5381_, v_constName_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
    return v___x_5382_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg___boxed(
    mut v_ref_5383_: *mut crate::leanh::LeanObject,
    mut v_constName_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
    mut v___y_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
    mut v___y_5389_: *mut crate::leanh::LeanObject,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v___y_5392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5393_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_5383_, v_constName_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
    crate::leanh::lean_dec(v___y_5391_);
    crate::leanh::lean_dec_ref(v___y_5390_);
    crate::leanh::lean_dec(v___y_5389_);
    crate::leanh::lean_dec_ref(v___y_5388_);
    crate::leanh::lean_dec_ref(v___y_5387_);
    crate::leanh::lean_dec(v___y_5386_);
    crate::leanh::lean_dec_ref(v___y_5385_);
    crate::leanh::lean_dec(v_ref_5383_);
    return v_res_5393_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(
    mut v_constName_5394_: *mut crate::leanh::LeanObject,
    mut v___y_5395_: *mut crate::leanh::LeanObject,
    mut v___y_5396_: *mut crate::leanh::LeanObject,
    mut v___y_5397_: *mut crate::leanh::LeanObject,
    mut v___y_5398_: *mut crate::leanh::LeanObject,
    mut v___y_5399_: *mut crate::leanh::LeanObject,
    mut v___y_5400_: *mut crate::leanh::LeanObject,
    mut v___y_5401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5403_ = crate::leanh::lean_ctor_get(v___y_5400_, 5);
    v___x_5404_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_5403_, v_constName_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
    return v___x_5404_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg___boxed(
    mut v_constName_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
    mut v___y_5408_: *mut crate::leanh::LeanObject,
    mut v___y_5409_: *mut crate::leanh::LeanObject,
    mut v___y_5410_: *mut crate::leanh::LeanObject,
    mut v___y_5411_: *mut crate::leanh::LeanObject,
    mut v___y_5412_: *mut crate::leanh::LeanObject,
    mut v___y_5413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_);
    crate::leanh::lean_dec(v___y_5412_);
    crate::leanh::lean_dec_ref(v___y_5411_);
    crate::leanh::lean_dec(v___y_5410_);
    crate::leanh::lean_dec_ref(v___y_5409_);
    crate::leanh::lean_dec_ref(v___y_5408_);
    crate::leanh::lean_dec(v___y_5407_);
    crate::leanh::lean_dec_ref(v___y_5406_);
    return v_res_5414_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(
    mut v_constName_5415_: *mut crate::leanh::LeanObject,
    mut v___y_5416_: *mut crate::leanh::LeanObject,
    mut v___y_5417_: *mut crate::leanh::LeanObject,
    mut v___y_5418_: *mut crate::leanh::LeanObject,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
    mut v___y_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: u8 = 0;
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5424_ = lean_st_ref_get(v___y_5422_);
                v_env_5425_ = crate::leanh::lean_ctor_get(v___x_5424_, 0);
                crate::leanh::lean_inc_ref(v_env_5425_);
                crate::leanh::lean_dec(v___x_5424_);
                v___x_5426_ = 0;
                crate::leanh::lean_inc(v_constName_5415_);
                v___x_5427_ =
                    l_Lean_Environment_find_x3f(v_env_5425_, v_constName_5415_, v___x_5426_);
                if crate::leanh::lean_obj_tag(v___x_5427_) == 0 {
                    v___x_5428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
                    return v___x_5428_;
                } else {
                    crate::leanh::lean_dec(v_constName_5415_);
                    v_val_5429_ = crate::leanh::lean_ctor_get(v___x_5427_, 0);
                    v_isSharedCheck_5436_ = (!crate::leanh::lean_is_exclusive(v___x_5427_)) as u8;
                    if v_isSharedCheck_5436_ == 0 {
                        v___x_5431_ = v___x_5427_;
                        v_isShared_5432_ = v_isSharedCheck_5436_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5429_);
                        crate::leanh::lean_dec(v___x_5427_);
                        v___x_5431_ = crate::leanh::lean_box(0);
                        v_isShared_5432_ = v_isSharedCheck_5436_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5432_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5431_, 0);
                    v___x_5434_ = v___x_5431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_val_5429_);
                    v___x_5434_ = v_reuseFailAlloc_5435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4___boxed(
    mut v_constName_5437_: *mut crate::leanh::LeanObject,
    mut v___y_5438_: *mut crate::leanh::LeanObject,
    mut v___y_5439_: *mut crate::leanh::LeanObject,
    mut v___y_5440_: *mut crate::leanh::LeanObject,
    mut v___y_5441_: *mut crate::leanh::LeanObject,
    mut v___y_5442_: *mut crate::leanh::LeanObject,
    mut v___y_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
    mut v___y_5445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5446_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(
        v_constName_5437_,
        v___y_5438_,
        v___y_5439_,
        v___y_5440_,
        v___y_5441_,
        v___y_5442_,
        v___y_5443_,
        v___y_5444_,
    );
    crate::leanh::lean_dec(v___y_5444_);
    crate::leanh::lean_dec_ref(v___y_5443_);
    crate::leanh::lean_dec(v___y_5442_);
    crate::leanh::lean_dec_ref(v___y_5441_);
    crate::leanh::lean_dec_ref(v___y_5440_);
    crate::leanh::lean_dec(v___y_5439_);
    crate::leanh::lean_dec_ref(v___y_5438_);
    return v_res_5446_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(
    mut v_as_5447_: *mut crate::leanh::LeanObject,
    mut v_i_5448_: usize,
    mut v_stop_5449_: usize,
    mut v_b_5450_: *mut crate::leanh::LeanObject,
    mut v___y_5451_: *mut crate::leanh::LeanObject,
    mut v___y_5452_: *mut crate::leanh::LeanObject,
    mut v___y_5453_: *mut crate::leanh::LeanObject,
    mut v___y_5454_: *mut crate::leanh::LeanObject,
    mut v___y_5455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5457_: u8 = 0;
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: usize = 0;
    let mut v___x_5463_: usize = 0;
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5457_ = lean_usize_dec_eq(v_i_5448_, v_stop_5449_);
                if v___x_5457_ == 0 {
                    v___x_5458_ = lean_array_uget_borrowed(v_as_5447_, v_i_5448_);
                    v_fvarId_5459_ = crate::leanh::lean_ctor_get(v___x_5458_, 0);
                    crate::leanh::lean_inc(v_fvarId_5459_);
                    v___x_5460_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_5459_,
                        v___y_5451_,
                        v___y_5452_,
                        v___y_5453_,
                        v___y_5454_,
                        v___y_5455_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5460_) == 0 {
                        v_a_5461_ = crate::leanh::lean_ctor_get(v___x_5460_, 0);
                        crate::leanh::lean_inc(v_a_5461_);
                        crate::leanh::lean_dec_ref_known(v___x_5460_, 1);
                        v___x_5462_ = 1usize;
                        v___x_5463_ = lean_usize_add(v_i_5448_, v___x_5462_);
                        v_i_5448_ = v___x_5463_;
                        v_b_5450_ = v_a_5461_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5460_;
                    }
                } else {
                    v___x_5465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5465_, 0, v_b_5450_);
                    return v___x_5465_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg___boxed(
    mut v_as_5466_: *mut crate::leanh::LeanObject,
    mut v_i_5467_: *mut crate::leanh::LeanObject,
    mut v_stop_5468_: *mut crate::leanh::LeanObject,
    mut v_b_5469_: *mut crate::leanh::LeanObject,
    mut v___y_5470_: *mut crate::leanh::LeanObject,
    mut v___y_5471_: *mut crate::leanh::LeanObject,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
    mut v___y_5473_: *mut crate::leanh::LeanObject,
    mut v___y_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5476_: usize = 0;
    let mut v_stop_boxed_5477_: usize = 0;
    let mut v_res_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5476_ = crate::leanh::lean_unbox_usize(v_i_5467_);
    crate::leanh::lean_dec(v_i_5467_);
    v_stop_boxed_5477_ = crate::leanh::lean_unbox_usize(v_stop_5468_);
    crate::leanh::lean_dec(v_stop_5468_);
    v_res_5478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_as_5466_, v_i_boxed_5476_, v_stop_boxed_5477_, v_b_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_);
    crate::leanh::lean_dec(v___y_5474_);
    crate::leanh::lean_dec_ref(v___y_5473_);
    crate::leanh::lean_dec(v___y_5472_);
    crate::leanh::lean_dec_ref(v___y_5471_);
    crate::leanh::lean_dec(v___y_5470_);
    crate::leanh::lean_dec_ref(v_as_5466_);
    return v_res_5478_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(
    mut v_as_5479_: *mut crate::leanh::LeanObject,
    mut v_i_5480_: usize,
    mut v_stop_5481_: usize,
    mut v_b_5482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: usize = 0;
    let mut v___x_5488_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5483_ = lean_usize_dec_eq(v_i_5480_, v_stop_5481_);
                if v___x_5483_ == 0 {
                    v___x_5484_ = lean_array_uget_borrowed(v_as_5479_, v_i_5480_);
                    v_fvarId_5485_ = crate::leanh::lean_ctor_get(v___x_5484_, 0);
                    crate::leanh::lean_inc(v_fvarId_5485_);
                    v___x_5486_ = l_Lean_FVarIdSet_insert(v_b_5482_, v_fvarId_5485_);
                    v___x_5487_ = 1usize;
                    v___x_5488_ = lean_usize_add(v_i_5480_, v___x_5487_);
                    v_i_5480_ = v___x_5488_;
                    v_b_5482_ = v___x_5486_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5482_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0___boxed(
    mut v_as_5490_: *mut crate::leanh::LeanObject,
    mut v_i_5491_: *mut crate::leanh::LeanObject,
    mut v_stop_5492_: *mut crate::leanh::LeanObject,
    mut v_b_5493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5494_: usize = 0;
    let mut v_stop_boxed_5495_: usize = 0;
    let mut v_res_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5494_ = crate::leanh::lean_unbox_usize(v_i_5491_);
    crate::leanh::lean_dec(v_i_5491_);
    v_stop_boxed_5495_ = crate::leanh::lean_unbox_usize(v_stop_5492_);
    crate::leanh::lean_dec(v_stop_5492_);
    v_res_5496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_as_5490_, v_i_boxed_5494_, v_stop_boxed_5495_, v_b_5493_);
    crate::leanh::lean_dec_ref(v_as_5490_);
    return v_res_5496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(
    mut v_declName_5498_: *mut crate::leanh::LeanObject,
    mut v_params_5499_: *mut crate::leanh::LeanObject,
    mut v_type_5500_: *mut crate::leanh::LeanObject,
    mut v_value_5501_: *mut crate::leanh::LeanObject,
    mut v_a_5502_: *mut crate::leanh::LeanObject,
    mut v_a_5503_: *mut crate::leanh::LeanObject,
    mut v_a_5504_: *mut crate::leanh::LeanObject,
    mut v_a_5505_: *mut crate::leanh::LeanObject,
    mut v_a_5506_: *mut crate::leanh::LeanObject,
    mut v_a_5507_: *mut crate::leanh::LeanObject,
    mut v_a_5508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5520_: u8 = 0;
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: u8 = 0;
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5536_: u8 = 0;
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5554_: u8 = 0;
    let mut v_a_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5558_: u8 = 0;
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5562_: u8 = 0;
    let mut v_a_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5570_: u8 = 0;
    let mut v_a_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_a_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: u8 = 0;
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5610_: u8 = 0;
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: u8 = 0;
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5627_: u8 = 0;
    let mut v_a_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5643_: u8 = 0;
    let mut v_a_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5647_: u8 = 0;
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_a_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5656_: u8 = 0;
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: usize = 0;
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: usize = 0;
    let mut v___x_5676_: usize = 0;
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: u8 = 0;
    let mut v___x_5683_: u8 = 0;
    let mut v___x_5684_: usize = 0;
    let mut v___x_5685_: usize = 0;
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: usize = 0;
    let mut v___x_5688_: usize = 0;
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5588_ = l_Lean_Compiler_LCNF_Check_Pure_checkParams(
                    v_params_5499_,
                    v_a_5502_,
                    v_a_5503_,
                    v_a_5504_,
                    v_a_5505_,
                    v_a_5506_,
                    v_a_5507_,
                    v_a_5508_,
                );
                if crate::leanh::lean_obj_tag(v___x_5588_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5588_, 1);
                    v___x_5589_ = crate::leanh::lean_box(0);
                    v___x_5661_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5662_ = lean_array_get_size(v_params_5499_);
                    v___x_5682_ = lean_nat_dec_lt(v___x_5661_, v___x_5662_);
                    if v___x_5682_ == 0 {
                        state = 27;
                        continue;
                    } else {
                        v___x_5683_ = lean_nat_dec_le(v___x_5662_, v___x_5662_);
                        if v___x_5683_ == 0 {
                            if v___x_5682_ == 0 {
                                state = 27;
                                continue;
                            } else {
                                v___x_5684_ = 0usize;
                                v___x_5685_ = lean_usize_of_nat(v___x_5662_);
                                v___x_5686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_params_5499_, v___x_5684_, v___x_5685_, v___x_5589_, v_a_5503_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
                                v___y_5681_ = v___x_5686_;
                                state = 28;
                                continue;
                            }
                        } else {
                            v___x_5687_ = 0usize;
                            v___x_5688_ = lean_usize_of_nat(v___x_5662_);
                            v___x_5689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_params_5499_, v___x_5687_, v___x_5688_, v___x_5589_, v_a_5503_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
                            v___y_5681_ = v___x_5689_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_5501_);
                    crate::leanh::lean_dec_ref(v_type_5500_);
                    crate::leanh::lean_dec_ref(v_params_5499_);
                    crate::leanh::lean_dec(v_declName_5498_);
                    return v___x_5588_;
                }
            }
            1 => {
                v___x_5516_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v___y_5512_);
                if crate::leanh::lean_obj_tag(v___x_5516_) == 0 {
                    v_a_5517_ = crate::leanh::lean_ctor_get(v___x_5516_, 0);
                    v_isSharedCheck_5579_ = (!crate::leanh::lean_is_exclusive(v___x_5516_)) as u8;
                    if v_isSharedCheck_5579_ == 0 {
                        v___x_5519_ = v___x_5516_;
                        v_isShared_5520_ = v_isSharedCheck_5579_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5517_);
                        crate::leanh::lean_dec(v___x_5516_);
                        v___x_5519_ = crate::leanh::lean_box(0);
                        v_isShared_5520_ = v_isSharedCheck_5579_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_5501_);
                    crate::leanh::lean_dec_ref(v_type_5500_);
                    crate::leanh::lean_dec_ref(v_params_5499_);
                    crate::leanh::lean_dec(v_declName_5498_);
                    v_a_5580_ = crate::leanh::lean_ctor_get(v___x_5516_, 0);
                    v_isSharedCheck_5587_ = (!crate::leanh::lean_is_exclusive(v___x_5516_)) as u8;
                    if v_isSharedCheck_5587_ == 0 {
                        v___x_5582_ = v___x_5516_;
                        v_isShared_5583_ = v_isSharedCheck_5587_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5580_);
                        crate::leanh::lean_dec(v___x_5516_);
                        v___x_5582_ = crate::leanh::lean_box(0);
                        v_isShared_5583_ = v_isSharedCheck_5587_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5521_ = (crate::leanh::lean_unbox(v_a_5517_) as u8);
                crate::leanh::lean_dec(v_a_5517_);
                if v___x_5521_ == 0 {
                    crate::leanh::lean_dec_ref(v_value_5501_);
                    crate::leanh::lean_dec_ref(v_type_5500_);
                    crate::leanh::lean_dec_ref(v_params_5499_);
                    crate::leanh::lean_dec(v_declName_5498_);
                    v___x_5522_ = crate::leanh::lean_box(0);
                    if v_isShared_5520_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5519_, 0, v___x_5522_);
                        v___x_5524_ = v___x_5519_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5525_, 0, v___x_5522_);
                        v___x_5524_ = v_reuseFailAlloc_5525_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5519_);
                    v___x_5526_ = 0;
                    v___x_5527_ = l_Lean_Compiler_LCNF_Code_inferType(
                        v___x_5526_,
                        v_value_5501_,
                        v___y_5512_,
                        v___y_5513_,
                        v___y_5514_,
                        v___y_5515_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5527_) == 0 {
                        v_a_5528_ = crate::leanh::lean_ctor_get(v___x_5527_, 0);
                        crate::leanh::lean_inc(v_a_5528_);
                        crate::leanh::lean_dec_ref_known(v___x_5527_, 1);
                        v___x_5529_ = l_Lean_Compiler_LCNF_mkForallParams(
                            v___x_5526_,
                            v_params_5499_,
                            v_a_5528_,
                            v___y_5512_,
                            v___y_5513_,
                            v___y_5514_,
                            v___y_5515_,
                        );
                        crate::leanh::lean_dec(v_a_5528_);
                        if crate::leanh::lean_obj_tag(v___x_5529_) == 0 {
                            v_a_5530_ = crate::leanh::lean_ctor_get(v___x_5529_, 0);
                            crate::leanh::lean_inc_n(v_a_5530_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_5529_, 1);
                            crate::leanh::lean_inc_ref(v_type_5500_);
                            v___x_5531_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_type_5500_,
                                v_a_5530_,
                                v___y_5511_,
                                v___y_5512_,
                                v___y_5513_,
                                v___y_5514_,
                                v___y_5515_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5531_) == 0 {
                                v_a_5532_ = crate::leanh::lean_ctor_get(v___x_5531_, 0);
                                v_isSharedCheck_5554_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5531_)) as u8;
                                if v_isSharedCheck_5554_ == 0 {
                                    v___x_5534_ = v___x_5531_;
                                    v_isShared_5535_ = v_isSharedCheck_5554_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5532_);
                                    crate::leanh::lean_dec(v___x_5531_);
                                    v___x_5534_ = crate::leanh::lean_box(0);
                                    v_isShared_5535_ = v_isSharedCheck_5554_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5530_);
                                crate::leanh::lean_dec_ref(v_type_5500_);
                                crate::leanh::lean_dec(v_declName_5498_);
                                v_a_5555_ = crate::leanh::lean_ctor_get(v___x_5531_, 0);
                                v_isSharedCheck_5562_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5531_)) as u8;
                                if v_isSharedCheck_5562_ == 0 {
                                    v___x_5557_ = v___x_5531_;
                                    v_isShared_5558_ = v_isSharedCheck_5562_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5555_);
                                    crate::leanh::lean_dec(v___x_5531_);
                                    v___x_5557_ = crate::leanh::lean_box(0);
                                    v_isShared_5558_ = v_isSharedCheck_5562_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_type_5500_);
                            crate::leanh::lean_dec(v_declName_5498_);
                            v_a_5563_ = crate::leanh::lean_ctor_get(v___x_5529_, 0);
                            v_isSharedCheck_5570_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5529_)) as u8;
                            if v_isSharedCheck_5570_ == 0 {
                                v___x_5565_ = v___x_5529_;
                                v_isShared_5566_ = v_isSharedCheck_5570_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5563_);
                                crate::leanh::lean_dec(v___x_5529_);
                                v___x_5565_ = crate::leanh::lean_box(0);
                                v_isShared_5566_ = v_isSharedCheck_5570_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_5500_);
                        crate::leanh::lean_dec_ref(v_params_5499_);
                        crate::leanh::lean_dec(v_declName_5498_);
                        v_a_5571_ = crate::leanh::lean_ctor_get(v___x_5527_, 0);
                        v_isSharedCheck_5578_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5527_)) as u8;
                        if v_isSharedCheck_5578_ == 0 {
                            v___x_5573_ = v___x_5527_;
                            v_isShared_5574_ = v_isSharedCheck_5578_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5571_);
                            crate::leanh::lean_dec(v___x_5527_);
                            v___x_5573_ = crate::leanh::lean_box(0);
                            v_isShared_5574_ = v_isSharedCheck_5578_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_5524_;
            }
            4 => {
                v___x_5536_ = (crate::leanh::lean_unbox(v_a_5532_) as u8);
                if v___x_5536_ == 0 {
                    crate::leanh::lean_del_object(v___x_5534_);
                    v___x_5537_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5,
                    );
                    v___x_5538_ = (crate::leanh::lean_unbox(v_a_5532_) as u8);
                    crate::leanh::lean_dec(v_a_5532_);
                    v___x_5539_ = l_Lean_MessageData_ofConstName(v_declName_5498_, v___x_5538_);
                    v___x_5540_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5540_, 0, v___x_5537_);
                    crate::leanh::lean_ctor_set(v___x_5540_, 1, v___x_5539_);
                    v___x_5541_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7,
                    );
                    v___x_5542_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5542_, 0, v___x_5540_);
                    crate::leanh::lean_ctor_set(v___x_5542_, 1, v___x_5541_);
                    v___x_5543_ = l_Lean_indentExpr(v_a_5530_);
                    v___x_5544_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5544_, 0, v___x_5542_);
                    crate::leanh::lean_ctor_set(v___x_5544_, 1, v___x_5543_);
                    v___x_5545_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                    v___x_5546_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5546_, 0, v___x_5544_);
                    crate::leanh::lean_ctor_set(v___x_5546_, 1, v___x_5545_);
                    v___x_5547_ = l_Lean_indentExpr(v_type_5500_);
                    v___x_5548_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5548_, 0, v___x_5546_);
                    crate::leanh::lean_ctor_set(v___x_5548_, 1, v___x_5547_);
                    v___x_5549_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5548_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_);
                    return v___x_5549_;
                } else {
                    crate::leanh::lean_dec(v_a_5532_);
                    crate::leanh::lean_dec(v_a_5530_);
                    crate::leanh::lean_dec_ref(v_type_5500_);
                    crate::leanh::lean_dec(v_declName_5498_);
                    v___x_5550_ = crate::leanh::lean_box(0);
                    if v_isShared_5535_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5534_, 0, v___x_5550_);
                        v___x_5552_ = v___x_5534_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5553_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5550_);
                        v___x_5552_ = v_reuseFailAlloc_5553_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5552_;
            }
            6 => {
                if v_isShared_5558_ == 0 {
                    v___x_5560_ = v___x_5557_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
                    v___x_5560_ = v_reuseFailAlloc_5561_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5560_;
            }
            8 => {
                if v_isShared_5566_ == 0 {
                    v___x_5568_ = v___x_5565_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5563_);
                    v___x_5568_ = v_reuseFailAlloc_5569_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5568_;
            }
            10 => {
                if v_isShared_5574_ == 0 {
                    v___x_5576_ = v___x_5573_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5571_);
                    v___x_5576_ = v_reuseFailAlloc_5577_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5576_;
            }
            12 => {
                if v_isShared_5583_ == 0 {
                    v___x_5585_ = v___x_5582_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_a_5580_);
                    v___x_5585_ = v_reuseFailAlloc_5586_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5585_;
            }
            14 => {
                v___x_5591_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_5505_);
                if crate::leanh::lean_obj_tag(v___x_5591_) == 0 {
                    v_a_5592_ = crate::leanh::lean_ctor_get(v___x_5591_, 0);
                    v_isSharedCheck_5652_ = (!crate::leanh::lean_is_exclusive(v___x_5591_)) as u8;
                    if v_isSharedCheck_5652_ == 0 {
                        v___x_5594_ = v___x_5591_;
                        v_isShared_5595_ = v_isSharedCheck_5652_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5592_);
                        crate::leanh::lean_dec(v___x_5591_);
                        v___x_5594_ = crate::leanh::lean_box(0);
                        v_isShared_5595_ = v_isSharedCheck_5652_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_5501_);
                    crate::leanh::lean_dec_ref(v_type_5500_);
                    crate::leanh::lean_dec_ref(v_params_5499_);
                    crate::leanh::lean_dec(v_declName_5498_);
                    v_a_5653_ = crate::leanh::lean_ctor_get(v___x_5591_, 0);
                    v_isSharedCheck_5660_ = (!crate::leanh::lean_is_exclusive(v___x_5591_)) as u8;
                    if v_isSharedCheck_5660_ == 0 {
                        v___x_5655_ = v___x_5591_;
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5653_);
                        crate::leanh::lean_dec(v___x_5591_);
                        v___x_5655_ = crate::leanh::lean_box(0);
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 25;
                        continue;
                    }
                }
            }
            15 => {
                v___x_5596_ = (crate::leanh::lean_unbox(v_a_5592_) as u8);
                crate::leanh::lean_dec(v_a_5592_);
                if v___x_5596_ == 0 {
                    crate::leanh::lean_dec_ref(v_value_5501_);
                    crate::leanh::lean_dec_ref(v_type_5500_);
                    crate::leanh::lean_dec_ref(v_params_5499_);
                    crate::leanh::lean_dec(v_declName_5498_);
                    if v_isShared_5595_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5594_, 0, v___x_5589_);
                        v___x_5598_ = v___x_5594_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5599_, 0, v___x_5589_);
                        v___x_5598_ = v_reuseFailAlloc_5599_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5594_);
                    v___x_5600_ = 0;
                    v___x_5601_ = l_Lean_Compiler_LCNF_Code_inferType(
                        v___x_5600_,
                        v_value_5501_,
                        v_a_5505_,
                        v_a_5506_,
                        v_a_5507_,
                        v_a_5508_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5601_) == 0 {
                        v_a_5602_ = crate::leanh::lean_ctor_get(v___x_5601_, 0);
                        crate::leanh::lean_inc(v_a_5602_);
                        crate::leanh::lean_dec_ref_known(v___x_5601_, 1);
                        v___x_5603_ = l_Lean_Compiler_LCNF_mkForallParams(
                            v___x_5600_,
                            v_params_5499_,
                            v_a_5602_,
                            v_a_5505_,
                            v_a_5506_,
                            v_a_5507_,
                            v_a_5508_,
                        );
                        crate::leanh::lean_dec(v_a_5602_);
                        if crate::leanh::lean_obj_tag(v___x_5603_) == 0 {
                            v_a_5604_ = crate::leanh::lean_ctor_get(v___x_5603_, 0);
                            crate::leanh::lean_inc_n(v_a_5604_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_5603_, 1);
                            crate::leanh::lean_inc_ref(v_type_5500_);
                            v___x_5605_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_type_5500_,
                                v_a_5604_,
                                v_a_5504_,
                                v_a_5505_,
                                v_a_5506_,
                                v_a_5507_,
                                v_a_5508_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5605_) == 0 {
                                v_a_5606_ = crate::leanh::lean_ctor_get(v___x_5605_, 0);
                                v_isSharedCheck_5627_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5605_)) as u8;
                                if v_isSharedCheck_5627_ == 0 {
                                    v___x_5608_ = v___x_5605_;
                                    v_isShared_5609_ = v_isSharedCheck_5627_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5606_);
                                    crate::leanh::lean_dec(v___x_5605_);
                                    v___x_5608_ = crate::leanh::lean_box(0);
                                    v_isShared_5609_ = v_isSharedCheck_5627_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5604_);
                                crate::leanh::lean_dec_ref(v_type_5500_);
                                crate::leanh::lean_dec(v_declName_5498_);
                                v_a_5628_ = crate::leanh::lean_ctor_get(v___x_5605_, 0);
                                v_isSharedCheck_5635_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5605_)) as u8;
                                if v_isSharedCheck_5635_ == 0 {
                                    v___x_5630_ = v___x_5605_;
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5628_);
                                    crate::leanh::lean_dec(v___x_5605_);
                                    v___x_5630_ = crate::leanh::lean_box(0);
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_type_5500_);
                            crate::leanh::lean_dec(v_declName_5498_);
                            v_a_5636_ = crate::leanh::lean_ctor_get(v___x_5603_, 0);
                            v_isSharedCheck_5643_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5603_)) as u8;
                            if v_isSharedCheck_5643_ == 0 {
                                v___x_5638_ = v___x_5603_;
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5636_);
                                crate::leanh::lean_dec(v___x_5603_);
                                v___x_5638_ = crate::leanh::lean_box(0);
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_5500_);
                        crate::leanh::lean_dec_ref(v_params_5499_);
                        crate::leanh::lean_dec(v_declName_5498_);
                        v_a_5644_ = crate::leanh::lean_ctor_get(v___x_5601_, 0);
                        v_isSharedCheck_5651_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5601_)) as u8;
                        if v_isSharedCheck_5651_ == 0 {
                            v___x_5646_ = v___x_5601_;
                            v_isShared_5647_ = v_isSharedCheck_5651_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5644_);
                            crate::leanh::lean_dec(v___x_5601_);
                            v___x_5646_ = crate::leanh::lean_box(0);
                            v_isShared_5647_ = v_isSharedCheck_5651_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            16 => {
                return v___x_5598_;
            }
            17 => {
                v___x_5610_ = (crate::leanh::lean_unbox(v_a_5606_) as u8);
                if v___x_5610_ == 0 {
                    crate::leanh::lean_del_object(v___x_5608_);
                    v___x_5611_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5,
                    );
                    v___x_5612_ = (crate::leanh::lean_unbox(v_a_5606_) as u8);
                    crate::leanh::lean_dec(v_a_5606_);
                    v___x_5613_ = l_Lean_MessageData_ofConstName(v_declName_5498_, v___x_5612_);
                    v___x_5614_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5614_, 0, v___x_5611_);
                    crate::leanh::lean_ctor_set(v___x_5614_, 1, v___x_5613_);
                    v___x_5615_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7,
                    );
                    v___x_5616_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5616_, 0, v___x_5614_);
                    crate::leanh::lean_ctor_set(v___x_5616_, 1, v___x_5615_);
                    v___x_5617_ = l_Lean_indentExpr(v_a_5604_);
                    v___x_5618_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5618_, 0, v___x_5616_);
                    crate::leanh::lean_ctor_set(v___x_5618_, 1, v___x_5617_);
                    v___x_5619_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                    v___x_5620_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5620_, 0, v___x_5618_);
                    crate::leanh::lean_ctor_set(v___x_5620_, 1, v___x_5619_);
                    v___x_5621_ = l_Lean_indentExpr(v_type_5500_);
                    v___x_5622_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5622_, 0, v___x_5620_);
                    crate::leanh::lean_ctor_set(v___x_5622_, 1, v___x_5621_);
                    v___x_5623_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5622_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
                    return v___x_5623_;
                } else {
                    crate::leanh::lean_dec(v_a_5606_);
                    crate::leanh::lean_dec(v_a_5604_);
                    crate::leanh::lean_dec_ref(v_type_5500_);
                    crate::leanh::lean_dec(v_declName_5498_);
                    if v_isShared_5609_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5608_, 0, v___x_5589_);
                        v___x_5625_ = v___x_5608_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_5626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5626_, 0, v___x_5589_);
                        v___x_5625_ = v_reuseFailAlloc_5626_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                return v___x_5625_;
            }
            19 => {
                if v_isShared_5631_ == 0 {
                    v___x_5633_ = v___x_5630_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
                    v___x_5633_ = v_reuseFailAlloc_5634_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5633_;
            }
            21 => {
                if v_isShared_5639_ == 0 {
                    v___x_5641_ = v___x_5638_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_a_5636_);
                    v___x_5641_ = v_reuseFailAlloc_5642_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5641_;
            }
            23 => {
                if v_isShared_5647_ == 0 {
                    v___x_5649_ = v___x_5646_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_a_5644_);
                    v___x_5649_ = v_reuseFailAlloc_5650_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5649_;
            }
            25 => {
                if v_isShared_5656_ == 0 {
                    v___x_5658_ = v___x_5655_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
                    v___x_5658_ = v_reuseFailAlloc_5659_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5658_;
            }
            27 => {
                v_jps_5664_ = crate::leanh::lean_ctor_get(v_a_5502_, 0);
                v_vars_5665_ = crate::leanh::lean_ctor_get(v_a_5502_, 1);
                v___x_5666_ = lean_nat_dec_lt(v___x_5661_, v___x_5662_);
                if v___x_5666_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_5502_);
                    crate::leanh::lean_inc_ref(v_value_5501_);
                    v___x_5667_ = l_Lean_Compiler_LCNF_Check_Pure_check(
                        v_value_5501_,
                        v_a_5502_,
                        v_a_5503_,
                        v_a_5504_,
                        v_a_5505_,
                        v_a_5506_,
                        v_a_5507_,
                        v_a_5508_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5667_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5667_, 1);
                        state = 14;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_5667_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5667_, 1);
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_value_5501_);
                            crate::leanh::lean_dec_ref(v_type_5500_);
                            crate::leanh::lean_dec_ref(v_params_5499_);
                            crate::leanh::lean_dec(v_declName_5498_);
                            return v___x_5667_;
                        }
                    }
                } else {
                    v___x_5668_ = lean_nat_dec_le(v___x_5662_, v___x_5662_);
                    if v___x_5668_ == 0 {
                        if v___x_5666_ == 0 {
                            crate::leanh::lean_inc_ref(v_a_5502_);
                            crate::leanh::lean_inc_ref(v_value_5501_);
                            v___x_5669_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(
                                v_value_5501_,
                                v___x_5589_,
                                v_a_5502_,
                                v_a_5503_,
                                v_a_5504_,
                                v_a_5505_,
                                v_a_5506_,
                                v_a_5507_,
                                v_a_5508_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5669_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5669_, 1);
                                v___y_5511_ = v_a_5504_;
                                v___y_5512_ = v_a_5505_;
                                v___y_5513_ = v_a_5506_;
                                v___y_5514_ = v_a_5507_;
                                v___y_5515_ = v_a_5508_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_value_5501_);
                                crate::leanh::lean_dec_ref(v_type_5500_);
                                crate::leanh::lean_dec_ref(v_params_5499_);
                                crate::leanh::lean_dec(v_declName_5498_);
                                return v___x_5669_;
                            }
                        } else {
                            v___x_5670_ = 0usize;
                            v___x_5671_ = lean_usize_of_nat(v___x_5662_);
                            crate::leanh::lean_inc(v_vars_5665_);
                            v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5499_, v___x_5670_, v___x_5671_, v_vars_5665_);
                            crate::leanh::lean_inc(v_jps_5664_);
                            v___x_5673_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5673_, 0, v_jps_5664_);
                            crate::leanh::lean_ctor_set(v___x_5673_, 1, v___x_5672_);
                            crate::leanh::lean_inc_ref(v_value_5501_);
                            v___x_5674_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(
                                v_value_5501_,
                                v___x_5589_,
                                v___x_5673_,
                                v_a_5503_,
                                v_a_5504_,
                                v_a_5505_,
                                v_a_5506_,
                                v_a_5507_,
                                v_a_5508_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5674_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5674_, 1);
                                v___y_5511_ = v_a_5504_;
                                v___y_5512_ = v_a_5505_;
                                v___y_5513_ = v_a_5506_;
                                v___y_5514_ = v_a_5507_;
                                v___y_5515_ = v_a_5508_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_value_5501_);
                                crate::leanh::lean_dec_ref(v_type_5500_);
                                crate::leanh::lean_dec_ref(v_params_5499_);
                                crate::leanh::lean_dec(v_declName_5498_);
                                return v___x_5674_;
                            }
                        }
                    } else {
                        v___x_5675_ = 0usize;
                        v___x_5676_ = lean_usize_of_nat(v___x_5662_);
                        crate::leanh::lean_inc(v_vars_5665_);
                        v___x_5677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5499_, v___x_5675_, v___x_5676_, v_vars_5665_);
                        crate::leanh::lean_inc(v_jps_5664_);
                        v___x_5678_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5678_, 0, v_jps_5664_);
                        crate::leanh::lean_ctor_set(v___x_5678_, 1, v___x_5677_);
                        crate::leanh::lean_inc_ref(v_value_5501_);
                        v___x_5679_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(
                            v_value_5501_,
                            v___x_5589_,
                            v___x_5678_,
                            v_a_5503_,
                            v_a_5504_,
                            v_a_5505_,
                            v_a_5506_,
                            v_a_5507_,
                            v_a_5508_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5679_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5679_, 1);
                            v___y_5511_ = v_a_5504_;
                            v___y_5512_ = v_a_5505_;
                            v___y_5513_ = v_a_5506_;
                            v___y_5514_ = v_a_5507_;
                            v___y_5515_ = v_a_5508_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_value_5501_);
                            crate::leanh::lean_dec_ref(v_type_5500_);
                            crate::leanh::lean_dec_ref(v_params_5499_);
                            crate::leanh::lean_dec(v_declName_5498_);
                            return v___x_5679_;
                        }
                    }
                }
            }
            28 => {
                if crate::leanh::lean_obj_tag(v___y_5681_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_5681_, 1);
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_value_5501_);
                    crate::leanh::lean_dec_ref(v_type_5500_);
                    crate::leanh::lean_dec_ref(v_params_5499_);
                    crate::leanh::lean_dec(v_declName_5498_);
                    return v___y_5681_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5691_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0;
    v___x_5692_ = l_Lean_stringToMessageData(v___x_5691_);
    return v___x_5692_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5694_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2;
    v___x_5695_ = l_Lean_stringToMessageData(v___x_5694_);
    return v___x_5695_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5697_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4;
    v___x_5698_ = l_Lean_stringToMessageData(v___x_5697_);
    return v___x_5698_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5700_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6;
    v___x_5701_ = l_Lean_stringToMessageData(v___x_5700_);
    return v___x_5701_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5703_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8;
    v___x_5704_ = l_Lean_stringToMessageData(v___x_5703_);
    return v___x_5704_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(
    mut v_funDecl_5705_: *mut crate::leanh::LeanObject,
    mut v_a_5706_: *mut crate::leanh::LeanObject,
    mut v_a_5707_: *mut crate::leanh::LeanObject,
    mut v_a_5708_: *mut crate::leanh::LeanObject,
    mut v_a_5709_: *mut crate::leanh::LeanObject,
    mut v_a_5710_: *mut crate::leanh::LeanObject,
    mut v_a_5711_: *mut crate::leanh::LeanObject,
    mut v_a_5712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: u8 = 0;
    let mut v___y_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5730_: u8 = 0;
    let mut v___x_5731_: u8 = 0;
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5742_: u8 = 0;
    let mut v_a_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5746_: u8 = 0;
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5750_: u8 = 0;
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: u8 = 0;
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_5714_ = crate::leanh::lean_ctor_get(v_funDecl_5705_, 0);
                v_binderName_5715_ = crate::leanh::lean_ctor_get(v_funDecl_5705_, 1);
                crate::leanh::lean_inc_n(v_binderName_5715_, 2);
                v_params_5716_ = crate::leanh::lean_ctor_get(v_funDecl_5705_, 2);
                v_type_5717_ = crate::leanh::lean_ctor_get(v_funDecl_5705_, 3);
                v_value_5718_ = crate::leanh::lean_ctor_get(v_funDecl_5705_, 4);
                crate::leanh::lean_inc_ref(v_value_5718_);
                crate::leanh::lean_inc_ref(v_type_5717_);
                crate::leanh::lean_inc_ref(v_params_5716_);
                v___x_5719_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(
                    v_binderName_5715_,
                    v_params_5716_,
                    v_type_5717_,
                    v_value_5718_,
                    v_a_5706_,
                    v_a_5707_,
                    v_a_5708_,
                    v_a_5709_,
                    v_a_5710_,
                    v_a_5711_,
                    v_a_5712_,
                );
                if crate::leanh::lean_obj_tag(v___x_5719_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5719_, 1);
                    v___x_5720_ = 0;
                    crate::leanh::lean_inc(v_fvarId_5714_);
                    v___x_5751_ = l_Lean_Compiler_LCNF_getFunDecl(
                        v___x_5720_,
                        v_fvarId_5714_,
                        v_a_5709_,
                        v_a_5710_,
                        v_a_5711_,
                        v_a_5712_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5751_) == 0 {
                        v_a_5752_ = crate::leanh::lean_ctor_get(v___x_5751_, 0);
                        crate::leanh::lean_inc(v_a_5752_);
                        crate::leanh::lean_dec_ref_known(v___x_5751_, 1);
                        v_binderName_5753_ = crate::leanh::lean_ctor_get(v_a_5752_, 1);
                        crate::leanh::lean_inc(v_binderName_5753_);
                        v_type_5754_ = crate::leanh::lean_ctor_get(v_a_5752_, 3);
                        crate::leanh::lean_inc_ref(v_type_5754_);
                        crate::leanh::lean_dec(v_a_5752_);
                        v___x_5773_ = lean_name_eq(v_binderName_5753_, v_binderName_5715_);
                        if v___x_5773_ == 0 {
                            v___x_5774_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                            );
                            crate::leanh::lean_inc(v_binderName_5715_);
                            v___x_5775_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                            v___x_5776_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5776_, 0, v___x_5774_);
                            crate::leanh::lean_ctor_set(v___x_5776_, 1, v___x_5775_);
                            v___x_5777_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9,
                            );
                            v___x_5778_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5778_, 0, v___x_5776_);
                            crate::leanh::lean_ctor_set(v___x_5778_, 1, v___x_5777_);
                            v___x_5779_ = l_Lean_MessageData_ofName(v_binderName_5753_);
                            v___x_5780_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5780_, 0, v___x_5778_);
                            crate::leanh::lean_ctor_set(v___x_5780_, 1, v___x_5779_);
                            v___x_5781_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                            v___x_5782_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5782_, 0, v___x_5780_);
                            crate::leanh::lean_ctor_set(v___x_5782_, 1, v___x_5781_);
                            v___x_5783_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5782_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_);
                            if crate::leanh::lean_obj_tag(v___x_5783_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5783_, 1);
                                v___y_5756_ = v_a_5709_;
                                v___y_5757_ = v_a_5710_;
                                v___y_5758_ = v_a_5711_;
                                v___y_5759_ = v_a_5712_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_type_5754_);
                                crate::leanh::lean_dec(v_binderName_5715_);
                                crate::leanh::lean_dec_ref(v_funDecl_5705_);
                                return v___x_5783_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_binderName_5753_);
                            v___y_5756_ = v_a_5709_;
                            v___y_5757_ = v_a_5710_;
                            v___y_5758_ = v_a_5711_;
                            v___y_5759_ = v_a_5712_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_5715_);
                        crate::leanh::lean_dec_ref(v_funDecl_5705_);
                        v_a_5784_ = crate::leanh::lean_ctor_get(v___x_5751_, 0);
                        v_isSharedCheck_5791_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5751_)) as u8;
                        if v_isSharedCheck_5791_ == 0 {
                            v___x_5786_ = v___x_5751_;
                            v_isShared_5787_ = v_isSharedCheck_5791_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5784_);
                            crate::leanh::lean_dec(v___x_5751_);
                            v___x_5786_ = crate::leanh::lean_box(0);
                            v_isShared_5787_ = v_isSharedCheck_5791_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_binderName_5715_);
                    crate::leanh::lean_dec_ref(v_funDecl_5705_);
                    return v___x_5719_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fvarId_5714_);
                v___x_5726_ = l_Lean_Compiler_LCNF_getFunDecl(
                    v___x_5720_,
                    v_fvarId_5714_,
                    v___y_5722_,
                    v___y_5723_,
                    v___y_5724_,
                    v___y_5725_,
                );
                if crate::leanh::lean_obj_tag(v___x_5726_) == 0 {
                    v_a_5727_ = crate::leanh::lean_ctor_get(v___x_5726_, 0);
                    v_isSharedCheck_5742_ = (!crate::leanh::lean_is_exclusive(v___x_5726_)) as u8;
                    if v_isSharedCheck_5742_ == 0 {
                        v___x_5729_ = v___x_5726_;
                        v_isShared_5730_ = v_isSharedCheck_5742_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5727_);
                        crate::leanh::lean_dec(v___x_5726_);
                        v___x_5729_ = crate::leanh::lean_box(0);
                        v_isShared_5730_ = v_isSharedCheck_5742_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_binderName_5715_);
                    crate::leanh::lean_dec_ref(v_funDecl_5705_);
                    v_a_5743_ = crate::leanh::lean_ctor_get(v___x_5726_, 0);
                    v_isSharedCheck_5750_ = (!crate::leanh::lean_is_exclusive(v___x_5726_)) as u8;
                    if v_isSharedCheck_5750_ == 0 {
                        v___x_5745_ = v___x_5726_;
                        v_isShared_5746_ = v_isSharedCheck_5750_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5743_);
                        crate::leanh::lean_dec(v___x_5726_);
                        v___x_5745_ = crate::leanh::lean_box(0);
                        v_isShared_5746_ = v_isSharedCheck_5750_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5731_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(
                    v___x_5720_,
                    v_a_5727_,
                    v_funDecl_5705_,
                );
                crate::leanh::lean_dec_ref(v_funDecl_5705_);
                crate::leanh::lean_dec(v_a_5727_);
                if v___x_5731_ == 0 {
                    crate::leanh::lean_del_object(v___x_5729_);
                    v___x_5732_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                    );
                    v___x_5733_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                    v___x_5734_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5734_, 0, v___x_5732_);
                    crate::leanh::lean_ctor_set(v___x_5734_, 1, v___x_5733_);
                    v___x_5735_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3,
                    );
                    v___x_5736_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5736_, 0, v___x_5734_);
                    crate::leanh::lean_ctor_set(v___x_5736_, 1, v___x_5735_);
                    v___x_5737_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5736_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
                    return v___x_5737_;
                } else {
                    crate::leanh::lean_dec(v_binderName_5715_);
                    v___x_5738_ = crate::leanh::lean_box(0);
                    if v_isShared_5730_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5729_, 0, v___x_5738_);
                        v___x_5740_ = v___x_5729_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5738_);
                        v___x_5740_ = v_reuseFailAlloc_5741_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5740_;
            }
            4 => {
                if v_isShared_5746_ == 0 {
                    v___x_5748_ = v___x_5745_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_a_5743_);
                    v___x_5748_ = v_reuseFailAlloc_5749_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5748_;
            }
            6 => {
                v___x_5760_ = lean_expr_eqv(v_type_5754_, v_type_5717_);
                if v___x_5760_ == 0 {
                    v___x_5761_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                    );
                    crate::leanh::lean_inc(v_binderName_5715_);
                    v___x_5762_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                    v___x_5763_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5763_, 0, v___x_5761_);
                    crate::leanh::lean_ctor_set(v___x_5763_, 1, v___x_5762_);
                    v___x_5764_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5,
                    );
                    v___x_5765_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5765_, 0, v___x_5763_);
                    crate::leanh::lean_ctor_set(v___x_5765_, 1, v___x_5764_);
                    v___x_5766_ = l_Lean_indentExpr(v_type_5754_);
                    v___x_5767_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5767_, 0, v___x_5765_);
                    crate::leanh::lean_ctor_set(v___x_5767_, 1, v___x_5766_);
                    v___x_5768_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7,
                    );
                    v___x_5769_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5769_, 0, v___x_5767_);
                    crate::leanh::lean_ctor_set(v___x_5769_, 1, v___x_5768_);
                    crate::leanh::lean_inc_ref(v_type_5717_);
                    v___x_5770_ = l_Lean_indentExpr(v_type_5717_);
                    v___x_5771_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5771_, 0, v___x_5769_);
                    crate::leanh::lean_ctor_set(v___x_5771_, 1, v___x_5770_);
                    v___x_5772_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5771_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_);
                    if crate::leanh::lean_obj_tag(v___x_5772_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5772_, 1);
                        v___y_5722_ = v___y_5756_;
                        v___y_5723_ = v___y_5757_;
                        v___y_5724_ = v___y_5758_;
                        v___y_5725_ = v___y_5759_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_binderName_5715_);
                        crate::leanh::lean_dec_ref(v_funDecl_5705_);
                        return v___x_5772_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_5754_);
                    v___y_5722_ = v___y_5756_;
                    v___y_5723_ = v___y_5757_;
                    v___y_5724_ = v___y_5758_;
                    v___y_5725_ = v___y_5759_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                if v_isShared_5787_ == 0 {
                    v___x_5789_ = v___x_5786_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
                    v___x_5789_ = v_reuseFailAlloc_5790_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5793_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__1;
    v___x_5794_ = l_Lean_stringToMessageData(v___x_5793_);
    return v___x_5794_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5796_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__3;
    v___x_5797_ = l_Lean_stringToMessageData(v___x_5796_);
    return v___x_5797_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5799_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__5;
    v___x_5800_ = l_Lean_stringToMessageData(v___x_5799_);
    return v___x_5800_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5802_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__7;
    v___x_5803_ = l_Lean_stringToMessageData(v___x_5802_);
    return v___x_5803_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_hasDefault_5804_: u8 = 0;
    let mut v_ctorNames_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hasDefault_5804_ = 0;
    v_ctorNames_5805_ = l_Lean_NameSet_empty;
    v___x_5806_ = crate::leanh::lean_box((v_hasDefault_5804_) as usize);
    v___x_5807_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5807_, 0, v_ctorNames_5805_);
    crate::leanh::lean_ctor_set(v___x_5807_, 1, v___x_5806_);
    return v___x_5807_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0;
    v___x_5810_ = l_Lean_stringToMessageData(v___x_5809_);
    return v___x_5810_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2;
    v___x_5813_ = l_Lean_stringToMessageData(v___x_5812_);
    return v___x_5813_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4;
    v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6;
    v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
    return v___x_5819_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8;
    v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10;
    v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
    return v___x_5825_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12;
    v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14;
    v___x_5831_ = l_Lean_stringToMessageData(v___x_5830_);
    return v___x_5831_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5(
    mut v_typeName_5832_: *mut crate::leanh::LeanObject,
    mut v_as_5833_: *mut crate::leanh::LeanObject,
    mut v_sz_5834_: usize,
    mut v_i_5835_: usize,
    mut v_b_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
    mut v___y_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
    mut v___y_5840_: *mut crate::leanh::LeanObject,
    mut v___y_5841_: *mut crate::leanh::LeanObject,
    mut v___y_5842_: *mut crate::leanh::LeanObject,
    mut v___y_5843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: usize = 0;
    let mut v___x_5848_: usize = 0;
    let mut v___x_5850_: u8 = 0;
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___y_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5866_: u8 = 0;
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_a_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: u8 = 0;
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: u8 = 0;
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: usize = 0;
    let mut v___x_5895_: usize = 0;
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: usize = 0;
    let mut v___x_5900_: usize = 0;
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5919_: u8 = 0;
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5923_: u8 = 0;
    let mut v___y_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: u8 = 0;
    let mut v___x_5938_: usize = 0;
    let mut v___x_5939_: usize = 0;
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: usize = 0;
    let mut v___x_5942_: usize = 0;
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u8 = 0;
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5977_: u8 = 0;
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v___y_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: u8 = 0;
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6010_: u8 = 0;
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6014_: u8 = 0;
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6025_: u8 = 0;
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6029_: u8 = 0;
    let mut v_a_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6033_: u8 = 0;
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6037_: u8 = 0;
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: u8 = 0;
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6049_: u8 = 0;
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6053_: u8 = 0;
    let mut v_a_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6057_: u8 = 0;
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6061_: u8 = 0;
    let mut v_code_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_isSharedCheck_6074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5850_ = lean_usize_dec_lt(v_i_5835_, v_sz_5834_);
                if v___x_5850_ == 0 {
                    crate::leanh::lean_dec(v_typeName_5832_);
                    v___x_5851_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5851_, 0, v_b_5836_);
                    return v___x_5851_;
                } else {
                    v_fst_5852_ = crate::leanh::lean_ctor_get(v_b_5836_, 0);
                    v_snd_5853_ = crate::leanh::lean_ctor_get(v_b_5836_, 1);
                    v_isSharedCheck_6074_ = (!crate::leanh::lean_is_exclusive(v_b_5836_)) as u8;
                    if v_isSharedCheck_6074_ == 0 {
                        v___x_5855_ = v_b_5836_;
                        v_isShared_5856_ = v_isSharedCheck_6074_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5853_);
                        crate::leanh::lean_inc(v_fst_5852_);
                        crate::leanh::lean_dec(v_b_5836_);
                        v___x_5855_ = crate::leanh::lean_box(0);
                        v_isShared_5856_ = v_isSharedCheck_6074_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5847_ = 1usize;
                v___x_5848_ = lean_usize_add(v_i_5835_, v___x_5847_);
                v_i_5835_ = v___x_5848_;
                v_b_5836_ = v_a_5846_;
                state = 0;
                continue;
            }
            2 => {
                v_a_5871_ = lean_array_uget_borrowed(v_as_5833_, v_i_5835_);
                if crate::leanh::lean_obj_tag(v_a_5871_) == 0 {
                    v_ctorName_5872_ = crate::leanh::lean_ctor_get(v_a_5871_, 0);
                    v_params_5873_ = crate::leanh::lean_ctor_get(v_a_5871_, 1);
                    v_code_5874_ = crate::leanh::lean_ctor_get(v_a_5871_, 2);
                    v___x_6038_ = l_Lean_Compiler_LCNF_Check_Pure_checkParams(
                        v_params_5873_,
                        v___y_5837_,
                        v___y_5838_,
                        v___y_5839_,
                        v___y_5840_,
                        v___y_5841_,
                        v___y_5842_,
                        v___y_5843_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6038_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6038_, 1);
                        v___x_6039_ = l_Lean_NameSet_contains(v_fst_5852_, v_ctorName_5872_);
                        if v___x_6039_ == 0 {
                            v___y_5983_ = v___y_5837_;
                            v___y_5984_ = v___y_5838_;
                            v___y_5985_ = v___y_5839_;
                            v___y_5986_ = v___y_5840_;
                            v___y_5987_ = v___y_5841_;
                            v___y_5988_ = v___y_5842_;
                            v___y_5989_ = v___y_5843_;
                            state = 15;
                            continue;
                        } else {
                            v___x_6040_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13);
                            crate::leanh::lean_inc(v_ctorName_5872_);
                            v___x_6041_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                            v___x_6042_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6042_, 0, v___x_6040_);
                            crate::leanh::lean_ctor_set(v___x_6042_, 1, v___x_6041_);
                            v___x_6043_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15);
                            v___x_6044_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6044_, 0, v___x_6042_);
                            crate::leanh::lean_ctor_set(v___x_6044_, 1, v___x_6043_);
                            v___x_6045_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6044_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
                            if crate::leanh::lean_obj_tag(v___x_6045_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6045_, 1);
                                v___y_5983_ = v___y_5837_;
                                v___y_5984_ = v___y_5838_;
                                v___y_5985_ = v___y_5839_;
                                v___y_5986_ = v___y_5840_;
                                v___y_5987_ = v___y_5841_;
                                v___y_5988_ = v___y_5842_;
                                v___y_5989_ = v___y_5843_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_5855_);
                                crate::leanh::lean_dec(v_snd_5853_);
                                crate::leanh::lean_dec(v_fst_5852_);
                                crate::leanh::lean_dec(v_typeName_5832_);
                                v_a_6046_ = crate::leanh::lean_ctor_get(v___x_6045_, 0);
                                v_isSharedCheck_6053_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6045_)) as u8;
                                if v_isSharedCheck_6053_ == 0 {
                                    v___x_6048_ = v___x_6045_;
                                    v_isShared_6049_ = v_isSharedCheck_6053_;
                                    state = 22;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6046_);
                                    crate::leanh::lean_dec(v___x_6045_);
                                    v___x_6048_ = crate::leanh::lean_box(0);
                                    v_isShared_6049_ = v_isSharedCheck_6053_;
                                    state = 22;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5855_);
                        crate::leanh::lean_dec(v_snd_5853_);
                        crate::leanh::lean_dec(v_fst_5852_);
                        crate::leanh::lean_dec(v_typeName_5832_);
                        v_a_6054_ = crate::leanh::lean_ctor_get(v___x_6038_, 0);
                        v_isSharedCheck_6061_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6038_)) as u8;
                        if v_isSharedCheck_6061_ == 0 {
                            v___x_6056_ = v___x_6038_;
                            v_isShared_6057_ = v_isSharedCheck_6061_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6054_);
                            crate::leanh::lean_dec(v___x_6038_);
                            v___x_6056_ = crate::leanh::lean_box(0);
                            v_isShared_6057_ = v_isSharedCheck_6061_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5855_);
                    crate::leanh::lean_dec(v_snd_5853_);
                    v_code_6062_ = crate::leanh::lean_ctor_get(v_a_5871_, 0);
                    crate::leanh::lean_inc_ref(v___y_5837_);
                    crate::leanh::lean_inc_ref(v_code_6062_);
                    v___x_6063_ = l_Lean_Compiler_LCNF_Check_Pure_check(
                        v_code_6062_,
                        v___y_5837_,
                        v___y_5838_,
                        v___y_5839_,
                        v___y_5840_,
                        v___y_5841_,
                        v___y_5842_,
                        v___y_5843_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6063_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6063_, 1);
                        v___x_6064_ = crate::leanh::lean_box((v___x_5850_) as usize);
                        v___x_6065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6065_, 0, v_fst_5852_);
                        crate::leanh::lean_ctor_set(v___x_6065_, 1, v___x_6064_);
                        v_a_5846_ = v___x_6065_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_5852_);
                        crate::leanh::lean_dec(v_typeName_5832_);
                        v_a_6066_ = crate::leanh::lean_ctor_get(v___x_6063_, 0);
                        v_isSharedCheck_6073_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6063_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6063_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6066_);
                            crate::leanh::lean_dec(v___x_6063_);
                            v___x_6068_ = crate::leanh::lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_5859_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_5859_, 1);
                    if v_isShared_5856_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5855_, 0, v___y_5858_);
                        v___x_5861_ = v___x_5855_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5862_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___y_5858_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5862_, 1, v_snd_5853_);
                        v___x_5861_ = v_reuseFailAlloc_5862_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5858_);
                    crate::leanh::lean_del_object(v___x_5855_);
                    crate::leanh::lean_dec(v_snd_5853_);
                    crate::leanh::lean_dec(v_typeName_5832_);
                    v_a_5863_ = crate::leanh::lean_ctor_get(v___y_5859_, 0);
                    v_isSharedCheck_5870_ = (!crate::leanh::lean_is_exclusive(v___y_5859_)) as u8;
                    if v_isSharedCheck_5870_ == 0 {
                        v___x_5865_ = v___y_5859_;
                        v_isShared_5866_ = v_isSharedCheck_5870_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5863_);
                        crate::leanh::lean_dec(v___y_5859_);
                        v___x_5865_ = crate::leanh::lean_box(0);
                        v_isShared_5866_ = v_isSharedCheck_5870_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_a_5846_ = v___x_5861_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_5866_ == 0 {
                    v___x_5868_ = v___x_5865_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
                    v___x_5868_ = v_reuseFailAlloc_5869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5868_;
            }
            7 => {
                v_jps_5886_ = crate::leanh::lean_ctor_get(v___y_5880_, 0);
                v_vars_5887_ = crate::leanh::lean_ctor_get(v___y_5880_, 1);
                v___x_5888_ = lean_nat_dec_lt(v___y_5876_, v___y_5885_);
                if v___x_5888_ == 0 {
                    crate::leanh::lean_dec(v___y_5885_);
                    crate::leanh::lean_inc(v_vars_5887_);
                    crate::leanh::lean_inc(v_jps_5886_);
                    v___x_5889_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5889_, 0, v_jps_5886_);
                    crate::leanh::lean_ctor_set(v___x_5889_, 1, v_vars_5887_);
                    crate::leanh::lean_inc_ref(v_code_5874_);
                    v___x_5890_ = l_Lean_Compiler_LCNF_Check_Pure_check(
                        v_code_5874_,
                        v___x_5889_,
                        v___y_5878_,
                        v___y_5883_,
                        v___y_5882_,
                        v___y_5879_,
                        v___y_5877_,
                        v___y_5884_,
                    );
                    v___y_5858_ = v___y_5881_;
                    v___y_5859_ = v___x_5890_;
                    state = 3;
                    continue;
                } else {
                    v___x_5891_ = lean_nat_dec_le(v___y_5885_, v___y_5885_);
                    if v___x_5891_ == 0 {
                        if v___x_5888_ == 0 {
                            crate::leanh::lean_dec(v___y_5885_);
                            crate::leanh::lean_inc(v_vars_5887_);
                            crate::leanh::lean_inc(v_jps_5886_);
                            v___x_5892_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5892_, 0, v_jps_5886_);
                            crate::leanh::lean_ctor_set(v___x_5892_, 1, v_vars_5887_);
                            crate::leanh::lean_inc_ref(v_code_5874_);
                            v___x_5893_ = l_Lean_Compiler_LCNF_Check_Pure_check(
                                v_code_5874_,
                                v___x_5892_,
                                v___y_5878_,
                                v___y_5883_,
                                v___y_5882_,
                                v___y_5879_,
                                v___y_5877_,
                                v___y_5884_,
                            );
                            v___y_5858_ = v___y_5881_;
                            v___y_5859_ = v___x_5893_;
                            state = 3;
                            continue;
                        } else {
                            v___x_5894_ = 0usize;
                            v___x_5895_ = lean_usize_of_nat(v___y_5885_);
                            crate::leanh::lean_dec(v___y_5885_);
                            crate::leanh::lean_inc(v_vars_5887_);
                            v___x_5896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5873_, v___x_5894_, v___x_5895_, v_vars_5887_);
                            crate::leanh::lean_inc(v_jps_5886_);
                            v___x_5897_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5897_, 0, v_jps_5886_);
                            crate::leanh::lean_ctor_set(v___x_5897_, 1, v___x_5896_);
                            crate::leanh::lean_inc_ref(v_code_5874_);
                            v___x_5898_ = l_Lean_Compiler_LCNF_Check_Pure_check(
                                v_code_5874_,
                                v___x_5897_,
                                v___y_5878_,
                                v___y_5883_,
                                v___y_5882_,
                                v___y_5879_,
                                v___y_5877_,
                                v___y_5884_,
                            );
                            v___y_5858_ = v___y_5881_;
                            v___y_5859_ = v___x_5898_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5899_ = 0usize;
                        v___x_5900_ = lean_usize_of_nat(v___y_5885_);
                        crate::leanh::lean_dec(v___y_5885_);
                        crate::leanh::lean_inc(v_vars_5887_);
                        v___x_5901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5873_, v___x_5899_, v___x_5900_, v_vars_5887_);
                        crate::leanh::lean_inc(v_jps_5886_);
                        v___x_5902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5902_, 0, v_jps_5886_);
                        crate::leanh::lean_ctor_set(v___x_5902_, 1, v___x_5901_);
                        crate::leanh::lean_inc_ref(v_code_5874_);
                        v___x_5903_ = l_Lean_Compiler_LCNF_Check_Pure_check(
                            v_code_5874_,
                            v___x_5902_,
                            v___y_5878_,
                            v___y_5883_,
                            v___y_5882_,
                            v___y_5879_,
                            v___y_5877_,
                            v___y_5884_,
                        );
                        v___y_5858_ = v___y_5881_;
                        v___y_5859_ = v___x_5903_;
                        state = 3;
                        continue;
                    }
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_5915_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_5915_, 1);
                    v___y_5876_ = v___y_5905_;
                    v___y_5877_ = v___y_5907_;
                    v___y_5878_ = v___y_5906_;
                    v___y_5879_ = v___y_5908_;
                    v___y_5880_ = v___y_5909_;
                    v___y_5881_ = v___y_5911_;
                    v___y_5882_ = v___y_5910_;
                    v___y_5883_ = v___y_5912_;
                    v___y_5884_ = v___y_5913_;
                    v___y_5885_ = v___y_5914_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_5914_);
                    crate::leanh::lean_dec(v___y_5911_);
                    crate::leanh::lean_del_object(v___x_5855_);
                    crate::leanh::lean_dec(v_snd_5853_);
                    crate::leanh::lean_dec(v_typeName_5832_);
                    v_a_5916_ = crate::leanh::lean_ctor_get(v___y_5915_, 0);
                    v_isSharedCheck_5923_ = (!crate::leanh::lean_is_exclusive(v___y_5915_)) as u8;
                    if v_isSharedCheck_5923_ == 0 {
                        v___x_5918_ = v___y_5915_;
                        v_isShared_5919_ = v_isSharedCheck_5923_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5916_);
                        crate::leanh::lean_dec(v___y_5915_);
                        v___x_5918_ = crate::leanh::lean_box(0);
                        v_isShared_5919_ = v_isSharedCheck_5923_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_5919_ == 0 {
                    v___x_5921_ = v___x_5918_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5922_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_a_5916_);
                    v___x_5921_ = v_reuseFailAlloc_5922_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5921_;
            }
            11 => {
                v___x_5933_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5934_ = lean_array_get_size(v_params_5873_);
                v___x_5935_ = lean_nat_dec_lt(v___x_5933_, v___x_5934_);
                if v___x_5935_ == 0 {
                    v___y_5876_ = v___x_5933_;
                    v___y_5877_ = v___y_5931_;
                    v___y_5878_ = v___y_5927_;
                    v___y_5879_ = v___y_5930_;
                    v___y_5880_ = v___y_5926_;
                    v___y_5881_ = v___y_5925_;
                    v___y_5882_ = v___y_5929_;
                    v___y_5883_ = v___y_5928_;
                    v___y_5884_ = v___y_5932_;
                    v___y_5885_ = v___x_5934_;
                    state = 7;
                    continue;
                } else {
                    v___x_5936_ = crate::leanh::lean_box(0);
                    v___x_5937_ = lean_nat_dec_le(v___x_5934_, v___x_5934_);
                    if v___x_5937_ == 0 {
                        if v___x_5935_ == 0 {
                            v___y_5876_ = v___x_5933_;
                            v___y_5877_ = v___y_5931_;
                            v___y_5878_ = v___y_5927_;
                            v___y_5879_ = v___y_5930_;
                            v___y_5880_ = v___y_5926_;
                            v___y_5881_ = v___y_5925_;
                            v___y_5882_ = v___y_5929_;
                            v___y_5883_ = v___y_5928_;
                            v___y_5884_ = v___y_5932_;
                            v___y_5885_ = v___x_5934_;
                            state = 7;
                            continue;
                        } else {
                            v___x_5938_ = 0usize;
                            v___x_5939_ = lean_usize_of_nat(v___x_5934_);
                            v___x_5940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_params_5873_, v___x_5938_, v___x_5939_, v___x_5936_, v___y_5927_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
                            v___y_5905_ = v___x_5933_;
                            v___y_5906_ = v___y_5927_;
                            v___y_5907_ = v___y_5931_;
                            v___y_5908_ = v___y_5930_;
                            v___y_5909_ = v___y_5926_;
                            v___y_5910_ = v___y_5929_;
                            v___y_5911_ = v___y_5925_;
                            v___y_5912_ = v___y_5928_;
                            v___y_5913_ = v___y_5932_;
                            v___y_5914_ = v___x_5934_;
                            v___y_5915_ = v___x_5940_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_5941_ = 0usize;
                        v___x_5942_ = lean_usize_of_nat(v___x_5934_);
                        v___x_5943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_params_5873_, v___x_5941_, v___x_5942_, v___x_5936_, v___y_5927_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
                        v___y_5905_ = v___x_5933_;
                        v___y_5906_ = v___y_5927_;
                        v___y_5907_ = v___y_5931_;
                        v___y_5908_ = v___y_5930_;
                        v___y_5909_ = v___y_5926_;
                        v___y_5910_ = v___y_5929_;
                        v___y_5911_ = v___y_5925_;
                        v___y_5912_ = v___y_5928_;
                        v___y_5913_ = v___y_5932_;
                        v___y_5914_ = v___x_5934_;
                        v___y_5915_ = v___x_5943_;
                        state = 8;
                        continue;
                    }
                }
            }
            12 => {
                v___x_5954_ = lean_array_get_size(v_params_5873_);
                v___x_5955_ = lean_nat_dec_eq(v___x_5954_, v_numFields_5945_);
                if v___x_5955_ == 0 {
                    v___x_5956_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                    crate::leanh::lean_inc(v_ctorName_5872_);
                    v___x_5957_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                    v___x_5958_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5958_, 0, v___x_5956_);
                    crate::leanh::lean_ctor_set(v___x_5958_, 1, v___x_5957_);
                    v___x_5959_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3);
                    v___x_5960_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5960_, 0, v___x_5958_);
                    crate::leanh::lean_ctor_set(v___x_5960_, 1, v___x_5959_);
                    v___x_5961_ = l_Nat_reprFast(v_numFields_5945_);
                    v___x_5962_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5962_, 0, v___x_5961_);
                    v___x_5963_ = l_Lean_MessageData_ofFormat(v___x_5962_);
                    v___x_5964_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5964_, 0, v___x_5960_);
                    crate::leanh::lean_ctor_set(v___x_5964_, 1, v___x_5963_);
                    v___x_5965_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5);
                    v___x_5966_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5966_, 0, v___x_5964_);
                    crate::leanh::lean_ctor_set(v___x_5966_, 1, v___x_5965_);
                    v___x_5967_ = l_Nat_reprFast(v___x_5954_);
                    v___x_5968_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5968_, 0, v___x_5967_);
                    v___x_5969_ = l_Lean_MessageData_ofFormat(v___x_5968_);
                    v___x_5970_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5970_, 0, v___x_5966_);
                    crate::leanh::lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                    v___x_5971_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7);
                    v___x_5972_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5972_, 0, v___x_5970_);
                    crate::leanh::lean_ctor_set(v___x_5972_, 1, v___x_5971_);
                    v___x_5973_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5972_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_);
                    if crate::leanh::lean_obj_tag(v___x_5973_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5973_, 1);
                        v___y_5925_ = v___y_5946_;
                        v___y_5926_ = v___y_5947_;
                        v___y_5927_ = v___y_5948_;
                        v___y_5928_ = v___y_5949_;
                        v___y_5929_ = v___y_5950_;
                        v___y_5930_ = v___y_5951_;
                        v___y_5931_ = v___y_5952_;
                        v___y_5932_ = v___y_5953_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_5946_);
                        crate::leanh::lean_del_object(v___x_5855_);
                        crate::leanh::lean_dec(v_snd_5853_);
                        crate::leanh::lean_dec(v_typeName_5832_);
                        v_a_5974_ = crate::leanh::lean_ctor_get(v___x_5973_, 0);
                        v_isSharedCheck_5981_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5973_)) as u8;
                        if v_isSharedCheck_5981_ == 0 {
                            v___x_5976_ = v___x_5973_;
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5974_);
                            crate::leanh::lean_dec(v___x_5973_);
                            v___x_5976_ = crate::leanh::lean_box(0);
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_numFields_5945_);
                    v___y_5925_ = v___y_5946_;
                    v___y_5926_ = v___y_5947_;
                    v___y_5927_ = v___y_5948_;
                    v___y_5928_ = v___y_5949_;
                    v___y_5929_ = v___y_5950_;
                    v___y_5930_ = v___y_5951_;
                    v___y_5931_ = v___y_5952_;
                    v___y_5932_ = v___y_5953_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                if v_isShared_5977_ == 0 {
                    v___x_5979_ = v___x_5976_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5980_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
                    v___x_5979_ = v_reuseFailAlloc_5980_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5979_;
            }
            15 => {
                crate::leanh::lean_inc_n(v_ctorName_5872_, 2);
                v___x_5990_ = l_Lean_NameSet_insert(v_fst_5852_, v_ctorName_5872_);
                v___x_5991_ =
                    l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(
                        v_ctorName_5872_,
                        v___y_5983_,
                        v___y_5984_,
                        v___y_5985_,
                        v___y_5986_,
                        v___y_5987_,
                        v___y_5988_,
                        v___y_5989_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5991_) == 0 {
                    v_a_5992_ = crate::leanh::lean_ctor_get(v___x_5991_, 0);
                    crate::leanh::lean_inc(v_a_5992_);
                    crate::leanh::lean_dec_ref_known(v___x_5991_, 1);
                    if crate::leanh::lean_obj_tag(v_a_5992_) == 6 {
                        v_val_5993_ = crate::leanh::lean_ctor_get(v_a_5992_, 0);
                        crate::leanh::lean_inc_ref(v_val_5993_);
                        crate::leanh::lean_dec_ref_known(v_a_5992_, 1);
                        v_induct_5994_ = crate::leanh::lean_ctor_get(v_val_5993_, 1);
                        crate::leanh::lean_inc(v_induct_5994_);
                        v_numFields_5995_ = crate::leanh::lean_ctor_get(v_val_5993_, 4);
                        crate::leanh::lean_inc(v_numFields_5995_);
                        crate::leanh::lean_dec_ref(v_val_5993_);
                        v___x_5996_ = lean_name_eq(v_induct_5994_, v_typeName_5832_);
                        crate::leanh::lean_dec(v_induct_5994_);
                        if v___x_5996_ == 0 {
                            v___x_5997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                            crate::leanh::lean_inc(v_ctorName_5872_);
                            v___x_5998_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                            v___x_5999_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5999_, 0, v___x_5997_);
                            crate::leanh::lean_ctor_set(v___x_5999_, 1, v___x_5998_);
                            v___x_6000_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9);
                            v___x_6001_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6001_, 0, v___x_5999_);
                            crate::leanh::lean_ctor_set(v___x_6001_, 1, v___x_6000_);
                            crate::leanh::lean_inc(v_typeName_5832_);
                            v___x_6002_ = l_Lean_MessageData_ofName(v_typeName_5832_);
                            v___x_6003_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6003_, 0, v___x_6001_);
                            crate::leanh::lean_ctor_set(v___x_6003_, 1, v___x_6002_);
                            v___x_6004_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                            v___x_6005_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6005_, 0, v___x_6003_);
                            crate::leanh::lean_ctor_set(v___x_6005_, 1, v___x_6004_);
                            v___x_6006_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6005_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
                            if crate::leanh::lean_obj_tag(v___x_6006_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6006_, 1);
                                v_numFields_5945_ = v_numFields_5995_;
                                v___y_5946_ = v___x_5990_;
                                v___y_5947_ = v___y_5983_;
                                v___y_5948_ = v___y_5984_;
                                v___y_5949_ = v___y_5985_;
                                v___y_5950_ = v___y_5986_;
                                v___y_5951_ = v___y_5987_;
                                v___y_5952_ = v___y_5988_;
                                v___y_5953_ = v___y_5989_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_numFields_5995_);
                                crate::leanh::lean_dec(v___x_5990_);
                                crate::leanh::lean_del_object(v___x_5855_);
                                crate::leanh::lean_dec(v_snd_5853_);
                                crate::leanh::lean_dec(v_typeName_5832_);
                                v_a_6007_ = crate::leanh::lean_ctor_get(v___x_6006_, 0);
                                v_isSharedCheck_6014_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6006_)) as u8;
                                if v_isSharedCheck_6014_ == 0 {
                                    v___x_6009_ = v___x_6006_;
                                    v_isShared_6010_ = v_isSharedCheck_6014_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6007_);
                                    crate::leanh::lean_dec(v___x_6006_);
                                    v___x_6009_ = crate::leanh::lean_box(0);
                                    v_isShared_6010_ = v_isSharedCheck_6014_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            v_numFields_5945_ = v_numFields_5995_;
                            v___y_5946_ = v___x_5990_;
                            v___y_5947_ = v___y_5983_;
                            v___y_5948_ = v___y_5984_;
                            v___y_5949_ = v___y_5985_;
                            v___y_5950_ = v___y_5986_;
                            v___y_5951_ = v___y_5987_;
                            v___y_5952_ = v___y_5988_;
                            v___y_5953_ = v___y_5989_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5992_);
                        crate::leanh::lean_del_object(v___x_5855_);
                        v___x_6015_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                        crate::leanh::lean_inc(v_ctorName_5872_);
                        v___x_6016_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                        v___x_6017_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6017_, 0, v___x_6015_);
                        crate::leanh::lean_ctor_set(v___x_6017_, 1, v___x_6016_);
                        v___x_6018_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11);
                        v___x_6019_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6019_, 0, v___x_6017_);
                        crate::leanh::lean_ctor_set(v___x_6019_, 1, v___x_6018_);
                        v___x_6020_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6019_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
                        if crate::leanh::lean_obj_tag(v___x_6020_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6020_, 1);
                            v___x_6021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6021_, 0, v___x_5990_);
                            crate::leanh::lean_ctor_set(v___x_6021_, 1, v_snd_5853_);
                            v_a_5846_ = v___x_6021_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5990_);
                            crate::leanh::lean_dec(v_snd_5853_);
                            crate::leanh::lean_dec(v_typeName_5832_);
                            v_a_6022_ = crate::leanh::lean_ctor_get(v___x_6020_, 0);
                            v_isSharedCheck_6029_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6020_)) as u8;
                            if v_isSharedCheck_6029_ == 0 {
                                v___x_6024_ = v___x_6020_;
                                v_isShared_6025_ = v_isSharedCheck_6029_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6022_);
                                crate::leanh::lean_dec(v___x_6020_);
                                v___x_6024_ = crate::leanh::lean_box(0);
                                v_isShared_6025_ = v_isSharedCheck_6029_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5990_);
                    crate::leanh::lean_del_object(v___x_5855_);
                    crate::leanh::lean_dec(v_snd_5853_);
                    crate::leanh::lean_dec(v_typeName_5832_);
                    v_a_6030_ = crate::leanh::lean_ctor_get(v___x_5991_, 0);
                    v_isSharedCheck_6037_ = (!crate::leanh::lean_is_exclusive(v___x_5991_)) as u8;
                    if v_isSharedCheck_6037_ == 0 {
                        v___x_6032_ = v___x_5991_;
                        v_isShared_6033_ = v_isSharedCheck_6037_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6030_);
                        crate::leanh::lean_dec(v___x_5991_);
                        v___x_6032_ = crate::leanh::lean_box(0);
                        v_isShared_6033_ = v_isSharedCheck_6037_;
                        state = 20;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_6010_ == 0 {
                    v___x_6012_ = v___x_6009_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_a_6007_);
                    v___x_6012_ = v_reuseFailAlloc_6013_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6012_;
            }
            18 => {
                if v_isShared_6025_ == 0 {
                    v___x_6027_ = v___x_6024_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6028_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
                    v___x_6027_ = v_reuseFailAlloc_6028_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6027_;
            }
            20 => {
                if v_isShared_6033_ == 0 {
                    v___x_6035_ = v___x_6032_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_a_6030_);
                    v___x_6035_ = v_reuseFailAlloc_6036_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6035_;
            }
            22 => {
                if v_isShared_6049_ == 0 {
                    v___x_6051_ = v___x_6048_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6052_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_a_6046_);
                    v___x_6051_ = v_reuseFailAlloc_6052_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6051_;
            }
            24 => {
                if v_isShared_6057_ == 0 {
                    v___x_6059_ = v___x_6056_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6060_, 0, v_a_6054_);
                    v___x_6059_ = v_reuseFailAlloc_6060_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6059_;
            }
            26 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkCases(
    mut v_c_6075_: *mut crate::leanh::LeanObject,
    mut v_a_6076_: *mut crate::leanh::LeanObject,
    mut v_a_6077_: *mut crate::leanh::LeanObject,
    mut v_a_6078_: *mut crate::leanh::LeanObject,
    mut v_a_6079_: *mut crate::leanh::LeanObject,
    mut v_a_6080_: *mut crate::leanh::LeanObject,
    mut v_a_6081_: *mut crate::leanh::LeanObject,
    mut v_a_6082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeName_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6089_: usize = 0;
    let mut v___x_6090_: usize = 0;
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6094_: u8 = 0;
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut v_unused_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6104_: u8 = 0;
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_6084_ = crate::leanh::lean_ctor_get(v_c_6075_, 0);
                crate::leanh::lean_inc(v_typeName_6084_);
                v_discr_6085_ = crate::leanh::lean_ctor_get(v_c_6075_, 2);
                crate::leanh::lean_inc(v_discr_6085_);
                v_alts_6086_ = crate::leanh::lean_ctor_get(v_c_6075_, 3);
                crate::leanh::lean_inc_ref(v_alts_6086_);
                crate::leanh::lean_dec_ref(v_c_6075_);
                v___x_6087_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(
                    v_discr_6085_,
                    v_a_6076_,
                    v_a_6077_,
                    v_a_6078_,
                    v_a_6079_,
                    v_a_6080_,
                    v_a_6081_,
                    v_a_6082_,
                );
                if crate::leanh::lean_obj_tag(v___x_6087_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6087_, 1);
                    v___x_6088_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0,
                    );
                    v_sz_6089_ = lean_array_size(v_alts_6086_);
                    v___x_6090_ = 0usize;
                    v___x_6091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5(v_typeName_6084_, v_alts_6086_, v_sz_6089_, v___x_6090_, v___x_6088_, v_a_6076_, v_a_6077_, v_a_6078_, v_a_6079_, v_a_6080_, v_a_6081_, v_a_6082_);
                    crate::leanh::lean_dec_ref(v_alts_6086_);
                    if crate::leanh::lean_obj_tag(v___x_6091_) == 0 {
                        v_isSharedCheck_6099_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6091_)) as u8;
                        if v_isSharedCheck_6099_ == 0 {
                            v_unused_6100_ = crate::leanh::lean_ctor_get(v___x_6091_, 0);
                            crate::leanh::lean_dec(v_unused_6100_);
                            v___x_6093_ = v___x_6091_;
                            v_isShared_6094_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6091_);
                            v___x_6093_ = crate::leanh::lean_box(0);
                            v_isShared_6094_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6101_ = crate::leanh::lean_ctor_get(v___x_6091_, 0);
                        v_isSharedCheck_6108_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6091_)) as u8;
                        if v_isSharedCheck_6108_ == 0 {
                            v___x_6103_ = v___x_6091_;
                            v_isShared_6104_ = v_isSharedCheck_6108_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6101_);
                            crate::leanh::lean_dec(v___x_6091_);
                            v___x_6103_ = crate::leanh::lean_box(0);
                            v_isShared_6104_ = v_isSharedCheck_6108_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_alts_6086_);
                    crate::leanh::lean_dec(v_typeName_6084_);
                    return v___x_6087_;
                }
            }
            1 => {
                v___x_6095_ = crate::leanh::lean_box(0);
                if v_isShared_6094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6093_, 0, v___x_6095_);
                    v___x_6097_ = v___x_6093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6098_, 0, v___x_6095_);
                    v___x_6097_ = v_reuseFailAlloc_6098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6097_;
            }
            3 => {
                if v_isShared_6104_ == 0 {
                    v___x_6106_ = v___x_6103_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6107_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6107_, 0, v_a_6101_);
                    v___x_6106_ = v_reuseFailAlloc_6107_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_check(
    mut v_code_6109_: *mut crate::leanh::LeanObject,
    mut v_a_6110_: *mut crate::leanh::LeanObject,
    mut v_a_6111_: *mut crate::leanh::LeanObject,
    mut v_a_6112_: *mut crate::leanh::LeanObject,
    mut v_a_6113_: *mut crate::leanh::LeanObject,
    mut v_a_6114_: *mut crate::leanh::LeanObject,
    mut v_a_6115_: *mut crate::leanh::LeanObject,
    mut v_a_6116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6122_: u8 = 0;
    let mut v_decl_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6127_: u8 = 0;
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v_decl_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6143_: u8 = 0;
    let mut v_jps_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6156_: u8 = 0;
    let mut v_decl_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6161_: u8 = 0;
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6172_: u8 = 0;
    let mut v_fvarId_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___y_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6191_: u8 = 0;
    let mut v___x_6192_: u8 = 0;
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: u8 = 0;
    let mut v_binderName_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6224_: u8 = 0;
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6228_: u8 = 0;
    let mut v_isSharedCheck_6229_: u8 = 0;
    let mut v_unused_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut v_cases_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6240_: u8 = 0;
    let mut v_unused_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6118_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__0;
                v___x_6119_ = l_Lean_Core_checkSystem(v___x_6118_, v_a_6115_, v_a_6116_);
                if crate::leanh::lean_obj_tag(v___x_6119_) == 0 {
                    v_isSharedCheck_6240_ = (!crate::leanh::lean_is_exclusive(v___x_6119_)) as u8;
                    if v_isSharedCheck_6240_ == 0 {
                        v_unused_6241_ = crate::leanh::lean_ctor_get(v___x_6119_, 0);
                        crate::leanh::lean_dec(v_unused_6241_);
                        v___x_6121_ = v___x_6119_;
                        v_isShared_6122_ = v_isSharedCheck_6240_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6119_);
                        v___x_6121_ = crate::leanh::lean_box(0);
                        v_isShared_6122_ = v_isSharedCheck_6240_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    crate::leanh::lean_dec_ref(v_code_6109_);
                    return v___x_6119_;
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_code_6109_) {
                0 => {
                    crate::leanh::lean_del_object(v___x_6121_);
                    v_decl_6123_ = crate::leanh::lean_ctor_get(v_code_6109_, 0);
                    v_k_6124_ = crate::leanh::lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6138_ = (!crate::leanh::lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6138_ == 0 {
                        v___x_6126_ = v_code_6109_;
                        v_isShared_6127_ = v_isSharedCheck_6138_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6124_);
                        crate::leanh::lean_inc(v_decl_6123_);
                        crate::leanh::lean_dec(v_code_6109_);
                        v___x_6126_ = crate::leanh::lean_box(0);
                        v_isShared_6127_ = v_isSharedCheck_6138_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_6121_);
                    v_decl_6139_ = crate::leanh::lean_ctor_get(v_code_6109_, 0);
                    v_k_6140_ = crate::leanh::lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6156_ = (!crate::leanh::lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6156_ == 0 {
                        v___x_6142_ = v_code_6109_;
                        v_isShared_6143_ = v_isSharedCheck_6156_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6140_);
                        crate::leanh::lean_inc(v_decl_6139_);
                        crate::leanh::lean_dec(v_code_6109_);
                        v___x_6142_ = crate::leanh::lean_box(0);
                        v_isShared_6143_ = v_isSharedCheck_6156_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    crate::leanh::lean_del_object(v___x_6121_);
                    v_decl_6157_ = crate::leanh::lean_ctor_get(v_code_6109_, 0);
                    v_k_6158_ = crate::leanh::lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6172_ = (!crate::leanh::lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6172_ == 0 {
                        v___x_6160_ = v_code_6109_;
                        v_isShared_6161_ = v_isSharedCheck_6172_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_6158_);
                        crate::leanh::lean_inc(v_decl_6157_);
                        crate::leanh::lean_dec(v_code_6109_);
                        v___x_6160_ = crate::leanh::lean_box(0);
                        v_isShared_6161_ = v_isSharedCheck_6172_;
                        state = 6;
                        continue;
                    }
                }
                3 => {
                    crate::leanh::lean_del_object(v___x_6121_);
                    v_fvarId_6173_ = crate::leanh::lean_ctor_get(v_code_6109_, 0);
                    v_args_6174_ = crate::leanh::lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6231_ = (!crate::leanh::lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6231_ == 0 {
                        v___x_6176_ = v_code_6109_;
                        v_isShared_6177_ = v_isSharedCheck_6231_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_6174_);
                        crate::leanh::lean_inc(v_fvarId_6173_);
                        crate::leanh::lean_dec(v_code_6109_);
                        v___x_6176_ = crate::leanh::lean_box(0);
                        v_isShared_6177_ = v_isSharedCheck_6231_;
                        state = 8;
                        continue;
                    }
                }
                4 => {
                    crate::leanh::lean_del_object(v___x_6121_);
                    v_cases_6232_ = crate::leanh::lean_ctor_get(v_code_6109_, 0);
                    crate::leanh::lean_inc_ref(v_cases_6232_);
                    crate::leanh::lean_dec_ref_known(v_code_6109_, 1);
                    v___x_6233_ = l_Lean_Compiler_LCNF_Check_Pure_checkCases(
                        v_cases_6232_,
                        v_a_6110_,
                        v_a_6111_,
                        v_a_6112_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6233_;
                }
                5 => {
                    crate::leanh::lean_del_object(v___x_6121_);
                    v_fvarId_6234_ = crate::leanh::lean_ctor_get(v_code_6109_, 0);
                    crate::leanh::lean_inc(v_fvarId_6234_);
                    crate::leanh::lean_dec_ref_known(v_code_6109_, 1);
                    v___x_6235_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar(
                        v_fvarId_6234_,
                        v_a_6110_,
                        v_a_6111_,
                        v_a_6112_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6235_;
                }
                _ => {
                    crate::leanh::lean_dec_ref_known(v_code_6109_, 1);
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    v___x_6236_ = crate::leanh::lean_box(0);
                    if v_isShared_6122_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6121_, 0, v___x_6236_);
                        v___x_6238_ = v___x_6121_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_6239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 0, v___x_6236_);
                        v___x_6238_ = v_reuseFailAlloc_6239_;
                        state = 15;
                        continue;
                    }
                }
            },
            2 => {
                crate::leanh::lean_inc_ref(v_decl_6123_);
                v___x_6128_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(
                    v_decl_6123_,
                    v_a_6110_,
                    v_a_6111_,
                    v_a_6112_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                if crate::leanh::lean_obj_tag(v___x_6128_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6128_, 1);
                    v_fvarId_6129_ = crate::leanh::lean_ctor_get(v_decl_6123_, 0);
                    crate::leanh::lean_inc_n(v_fvarId_6129_, 2);
                    crate::leanh::lean_dec_ref(v_decl_6123_);
                    v___x_6130_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6129_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6130_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6130_, 1);
                        v_jps_6131_ = crate::leanh::lean_ctor_get(v_a_6110_, 0);
                        crate::leanh::lean_inc(v_jps_6131_);
                        v_vars_6132_ = crate::leanh::lean_ctor_get(v_a_6110_, 1);
                        crate::leanh::lean_inc(v_vars_6132_);
                        crate::leanh::lean_dec_ref(v_a_6110_);
                        v___x_6133_ = l_Lean_FVarIdSet_insert(v_vars_6132_, v_fvarId_6129_);
                        if v_isShared_6127_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6126_, 1, v___x_6133_);
                            crate::leanh::lean_ctor_set(v___x_6126_, 0, v_jps_6131_);
                            v___x_6135_ = v___x_6126_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6137_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_jps_6131_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6137_, 1, v___x_6133_);
                            v___x_6135_ = v_reuseFailAlloc_6137_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_6129_);
                        crate::leanh::lean_del_object(v___x_6126_);
                        crate::leanh::lean_dec_ref(v_k_6124_);
                        crate::leanh::lean_dec_ref(v_a_6110_);
                        return v___x_6130_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6126_);
                    crate::leanh::lean_dec_ref(v_k_6124_);
                    crate::leanh::lean_dec_ref(v_decl_6123_);
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6128_;
                }
            }
            3 => {
                v_code_6109_ = v_k_6124_;
                v_a_6110_ = v___x_6135_;
                state = 0;
                continue;
            }
            4 => {
                v_jps_6144_ = crate::leanh::lean_ctor_get(v_a_6110_, 0);
                crate::leanh::lean_inc(v_jps_6144_);
                v_vars_6145_ = crate::leanh::lean_ctor_get(v_a_6110_, 1);
                crate::leanh::lean_inc_n(v_vars_6145_, 2);
                crate::leanh::lean_dec_ref(v_a_6110_);
                v___x_6146_ = crate::leanh::lean_box(1);
                if v_isShared_6143_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6142_, 0);
                    crate::leanh::lean_ctor_set(v___x_6142_, 1, v_vars_6145_);
                    crate::leanh::lean_ctor_set(v___x_6142_, 0, v___x_6146_);
                    v___x_6148_ = v___x_6142_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6155_, 0, v___x_6146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6155_, 1, v_vars_6145_);
                    v___x_6148_ = v_reuseFailAlloc_6155_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v_decl_6139_);
                v___x_6149_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(
                    v_decl_6139_,
                    v___x_6148_,
                    v_a_6111_,
                    v_a_6112_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                crate::leanh::lean_dec_ref(v___x_6148_);
                if crate::leanh::lean_obj_tag(v___x_6149_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6149_, 1);
                    v_fvarId_6150_ = crate::leanh::lean_ctor_get(v_decl_6139_, 0);
                    crate::leanh::lean_inc_n(v_fvarId_6150_, 2);
                    crate::leanh::lean_dec_ref(v_decl_6139_);
                    v___x_6151_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6150_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6151_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6151_, 1);
                        v___x_6152_ = l_Lean_FVarIdSet_insert(v_vars_6145_, v_fvarId_6150_);
                        v___x_6153_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6153_, 0, v_jps_6144_);
                        crate::leanh::lean_ctor_set(v___x_6153_, 1, v___x_6152_);
                        v_code_6109_ = v_k_6140_;
                        v_a_6110_ = v___x_6153_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fvarId_6150_);
                        crate::leanh::lean_dec(v_vars_6145_);
                        crate::leanh::lean_dec(v_jps_6144_);
                        crate::leanh::lean_dec_ref(v_k_6140_);
                        return v___x_6151_;
                    }
                } else {
                    crate::leanh::lean_dec(v_vars_6145_);
                    crate::leanh::lean_dec(v_jps_6144_);
                    crate::leanh::lean_dec_ref(v_k_6140_);
                    crate::leanh::lean_dec_ref(v_decl_6139_);
                    return v___x_6149_;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v_decl_6157_);
                v___x_6162_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(
                    v_decl_6157_,
                    v_a_6110_,
                    v_a_6111_,
                    v_a_6112_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                if crate::leanh::lean_obj_tag(v___x_6162_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6162_, 1);
                    v_fvarId_6163_ = crate::leanh::lean_ctor_get(v_decl_6157_, 0);
                    crate::leanh::lean_inc_n(v_fvarId_6163_, 2);
                    crate::leanh::lean_dec_ref(v_decl_6157_);
                    v___x_6164_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6163_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6164_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6164_, 1);
                        v_jps_6165_ = crate::leanh::lean_ctor_get(v_a_6110_, 0);
                        crate::leanh::lean_inc(v_jps_6165_);
                        v_vars_6166_ = crate::leanh::lean_ctor_get(v_a_6110_, 1);
                        crate::leanh::lean_inc(v_vars_6166_);
                        crate::leanh::lean_dec_ref(v_a_6110_);
                        v___x_6167_ = l_Lean_FVarIdSet_insert(v_jps_6165_, v_fvarId_6163_);
                        if v_isShared_6161_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6160_, 0);
                            crate::leanh::lean_ctor_set(v___x_6160_, 1, v_vars_6166_);
                            crate::leanh::lean_ctor_set(v___x_6160_, 0, v___x_6167_);
                            v___x_6169_ = v___x_6160_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_6171_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6171_, 0, v___x_6167_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6171_, 1, v_vars_6166_);
                            v___x_6169_ = v_reuseFailAlloc_6171_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_6163_);
                        crate::leanh::lean_del_object(v___x_6160_);
                        crate::leanh::lean_dec_ref(v_k_6158_);
                        crate::leanh::lean_dec_ref(v_a_6110_);
                        return v___x_6164_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6160_);
                    crate::leanh::lean_dec_ref(v_k_6158_);
                    crate::leanh::lean_dec_ref(v_decl_6157_);
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6162_;
                }
            }
            7 => {
                v_code_6109_ = v_k_6158_;
                v_a_6110_ = v___x_6169_;
                state = 0;
                continue;
            }
            8 => {
                crate::leanh::lean_inc(v_fvarId_6173_);
                v___x_6188_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
                    v_fvarId_6173_,
                    v_a_6110_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                if crate::leanh::lean_obj_tag(v___x_6188_) == 0 {
                    v_isSharedCheck_6229_ = (!crate::leanh::lean_is_exclusive(v___x_6188_)) as u8;
                    if v_isSharedCheck_6229_ == 0 {
                        v_unused_6230_ = crate::leanh::lean_ctor_get(v___x_6188_, 0);
                        crate::leanh::lean_dec(v_unused_6230_);
                        v___x_6190_ = v___x_6188_;
                        v_isShared_6191_ = v_isSharedCheck_6229_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6188_);
                        v___x_6190_ = crate::leanh::lean_box(0);
                        v_isShared_6191_ = v_isSharedCheck_6229_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6176_);
                    crate::leanh::lean_dec_ref(v_args_6174_);
                    crate::leanh::lean_dec(v_fvarId_6173_);
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6188_;
                }
            }
            9 => {
                v___x_6186_ = l_Lean_Expr_fvar___override(v_fvarId_6173_);
                v___x_6187_ = l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(
                    v___x_6186_,
                    v_args_6174_,
                    v___y_6179_,
                    v___y_6180_,
                    v___y_6181_,
                    v___y_6182_,
                    v___y_6183_,
                    v___y_6184_,
                    v___y_6185_,
                );
                crate::leanh::lean_dec_ref(v___y_6179_);
                return v___x_6187_;
            }
            10 => {
                v___x_6192_ = 0;
                crate::leanh::lean_inc(v_fvarId_6173_);
                v___x_6193_ = l_Lean_Compiler_LCNF_getFunDecl(
                    v___x_6192_,
                    v_fvarId_6173_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                if crate::leanh::lean_obj_tag(v___x_6193_) == 0 {
                    v_a_6194_ = crate::leanh::lean_ctor_get(v___x_6193_, 0);
                    crate::leanh::lean_inc(v_a_6194_);
                    crate::leanh::lean_dec_ref_known(v___x_6193_, 1);
                    v___x_6195_ = l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(v_a_6194_);
                    v___x_6196_ = lean_array_get_size(v_args_6174_);
                    v___x_6197_ = lean_nat_dec_eq(v___x_6195_, v___x_6196_);
                    if v___x_6197_ == 0 {
                        v_binderName_6198_ = crate::leanh::lean_ctor_get(v_a_6194_, 1);
                        crate::leanh::lean_inc(v_binderName_6198_);
                        crate::leanh::lean_dec(v_a_6194_);
                        v___x_6199_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Check_Pure_check___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Check_Pure_check___closed__2_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__2,
                        );
                        v___x_6200_ = l_Lean_MessageData_ofName(v_binderName_6198_);
                        if v_isShared_6177_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6176_, 7);
                            crate::leanh::lean_ctor_set(v___x_6176_, 1, v___x_6200_);
                            crate::leanh::lean_ctor_set(v___x_6176_, 0, v___x_6199_);
                            v___x_6202_ = v___x_6176_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_6220_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6220_, 0, v___x_6199_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6220_, 1, v___x_6200_);
                            v___x_6202_ = v_reuseFailAlloc_6220_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6195_);
                        crate::leanh::lean_dec(v_a_6194_);
                        crate::leanh::lean_del_object(v___x_6190_);
                        crate::leanh::lean_del_object(v___x_6176_);
                        v___y_6179_ = v_a_6110_;
                        v___y_6180_ = v_a_6111_;
                        v___y_6181_ = v_a_6112_;
                        v___y_6182_ = v_a_6113_;
                        v___y_6183_ = v_a_6114_;
                        v___y_6184_ = v_a_6115_;
                        v___y_6185_ = v_a_6116_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6190_);
                    crate::leanh::lean_del_object(v___x_6176_);
                    crate::leanh::lean_dec_ref(v_args_6174_);
                    crate::leanh::lean_dec(v_fvarId_6173_);
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    v_a_6221_ = crate::leanh::lean_ctor_get(v___x_6193_, 0);
                    v_isSharedCheck_6228_ = (!crate::leanh::lean_is_exclusive(v___x_6193_)) as u8;
                    if v_isSharedCheck_6228_ == 0 {
                        v___x_6223_ = v___x_6193_;
                        v_isShared_6224_ = v_isSharedCheck_6228_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6221_);
                        crate::leanh::lean_dec(v___x_6193_);
                        v___x_6223_ = crate::leanh::lean_box(0);
                        v_isShared_6224_ = v_isSharedCheck_6228_;
                        state = 13;
                        continue;
                    }
                }
            }
            11 => {
                v___x_6203_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__4_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__4,
                );
                v___x_6204_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6204_, 0, v___x_6202_);
                crate::leanh::lean_ctor_set(v___x_6204_, 1, v___x_6203_);
                v___x_6205_ = l_Nat_reprFast(v___x_6195_);
                if v_isShared_6191_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6190_, 3);
                    crate::leanh::lean_ctor_set(v___x_6190_, 0, v___x_6205_);
                    v___x_6207_ = v___x_6190_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6219_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6219_, 0, v___x_6205_);
                    v___x_6207_ = v_reuseFailAlloc_6219_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6208_ = l_Lean_MessageData_ofFormat(v___x_6207_);
                v___x_6209_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6209_, 0, v___x_6204_);
                crate::leanh::lean_ctor_set(v___x_6209_, 1, v___x_6208_);
                v___x_6210_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__6_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__6,
                );
                v___x_6211_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6211_, 0, v___x_6209_);
                crate::leanh::lean_ctor_set(v___x_6211_, 1, v___x_6210_);
                v___x_6212_ = l_Nat_reprFast(v___x_6196_);
                v___x_6213_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6213_, 0, v___x_6212_);
                v___x_6214_ = l_Lean_MessageData_ofFormat(v___x_6213_);
                v___x_6215_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6215_, 0, v___x_6211_);
                crate::leanh::lean_ctor_set(v___x_6215_, 1, v___x_6214_);
                v___x_6216_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__8_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__8,
                );
                v___x_6217_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6217_, 0, v___x_6215_);
                crate::leanh::lean_ctor_set(v___x_6217_, 1, v___x_6216_);
                v___x_6218_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6217_, v_a_6113_, v_a_6114_, v_a_6115_, v_a_6116_);
                if crate::leanh::lean_obj_tag(v___x_6218_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6218_, 1);
                    v___y_6179_ = v_a_6110_;
                    v___y_6180_ = v_a_6111_;
                    v___y_6181_ = v_a_6112_;
                    v___y_6182_ = v_a_6113_;
                    v___y_6183_ = v_a_6114_;
                    v___y_6184_ = v_a_6115_;
                    v___y_6185_ = v_a_6116_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_args_6174_);
                    crate::leanh::lean_dec(v_fvarId_6173_);
                    crate::leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6218_;
                }
            }
            13 => {
                if v_isShared_6224_ == 0 {
                    v___x_6226_ = v___x_6223_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_a_6221_);
                    v___x_6226_ = v_reuseFailAlloc_6227_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6226_;
            }
            15 => {
                return v___x_6238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(
    mut v_value_6242_: *mut crate::leanh::LeanObject,
    mut v___x_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
    mut v___y_6247_: *mut crate::leanh::LeanObject,
    mut v___y_6248_: *mut crate::leanh::LeanObject,
    mut v___y_6249_: *mut crate::leanh::LeanObject,
    mut v___y_6250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6259_: u8 = 0;
    let mut v_unused_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6252_ = l_Lean_Compiler_LCNF_Check_Pure_check(
                    v_value_6242_,
                    v___y_6244_,
                    v___y_6245_,
                    v___y_6246_,
                    v___y_6247_,
                    v___y_6248_,
                    v___y_6249_,
                    v___y_6250_,
                );
                if crate::leanh::lean_obj_tag(v___x_6252_) == 0 {
                    v_isSharedCheck_6259_ = (!crate::leanh::lean_is_exclusive(v___x_6252_)) as u8;
                    if v_isSharedCheck_6259_ == 0 {
                        v_unused_6260_ = crate::leanh::lean_ctor_get(v___x_6252_, 0);
                        crate::leanh::lean_dec(v_unused_6260_);
                        v___x_6254_ = v___x_6252_;
                        v_isShared_6255_ = v_isSharedCheck_6259_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6252_);
                        v___x_6254_ = crate::leanh::lean_box(0);
                        v_isShared_6255_ = v_isSharedCheck_6259_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_6252_;
                }
            }
            1 => {
                if v_isShared_6255_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6254_, 0, v___x_6243_);
                    v___x_6257_ = v___x_6254_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6258_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6258_, 0, v___x_6243_);
                    v___x_6257_ = v_reuseFailAlloc_6258_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0___boxed(
    mut v_value_6261_: *mut crate::leanh::LeanObject,
    mut v___x_6262_: *mut crate::leanh::LeanObject,
    mut v___y_6263_: *mut crate::leanh::LeanObject,
    mut v___y_6264_: *mut crate::leanh::LeanObject,
    mut v___y_6265_: *mut crate::leanh::LeanObject,
    mut v___y_6266_: *mut crate::leanh::LeanObject,
    mut v___y_6267_: *mut crate::leanh::LeanObject,
    mut v___y_6268_: *mut crate::leanh::LeanObject,
    mut v___y_6269_: *mut crate::leanh::LeanObject,
    mut v___y_6270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6271_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___lam__0(
        v_value_6261_,
        v___x_6262_,
        v___y_6263_,
        v___y_6264_,
        v___y_6265_,
        v___y_6266_,
        v___y_6267_,
        v___y_6268_,
        v___y_6269_,
    );
    crate::leanh::lean_dec(v___y_6269_);
    crate::leanh::lean_dec_ref(v___y_6268_);
    crate::leanh::lean_dec(v___y_6267_);
    crate::leanh::lean_dec_ref(v___y_6266_);
    crate::leanh::lean_dec_ref(v___y_6265_);
    crate::leanh::lean_dec(v___y_6264_);
    return v_res_6271_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkCases___boxed(
    mut v_c_6272_: *mut crate::leanh::LeanObject,
    mut v_a_6273_: *mut crate::leanh::LeanObject,
    mut v_a_6274_: *mut crate::leanh::LeanObject,
    mut v_a_6275_: *mut crate::leanh::LeanObject,
    mut v_a_6276_: *mut crate::leanh::LeanObject,
    mut v_a_6277_: *mut crate::leanh::LeanObject,
    mut v_a_6278_: *mut crate::leanh::LeanObject,
    mut v_a_6279_: *mut crate::leanh::LeanObject,
    mut v_a_6280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6281_ = l_Lean_Compiler_LCNF_Check_Pure_checkCases(
        v_c_6272_, v_a_6273_, v_a_6274_, v_a_6275_, v_a_6276_, v_a_6277_, v_a_6278_, v_a_6279_,
    );
    crate::leanh::lean_dec(v_a_6279_);
    crate::leanh::lean_dec_ref(v_a_6278_);
    crate::leanh::lean_dec(v_a_6277_);
    crate::leanh::lean_dec_ref(v_a_6276_);
    crate::leanh::lean_dec_ref(v_a_6275_);
    crate::leanh::lean_dec(v_a_6274_);
    crate::leanh::lean_dec_ref(v_a_6273_);
    return v_res_6281_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___boxed(
    mut v_funDecl_6282_: *mut crate::leanh::LeanObject,
    mut v_a_6283_: *mut crate::leanh::LeanObject,
    mut v_a_6284_: *mut crate::leanh::LeanObject,
    mut v_a_6285_: *mut crate::leanh::LeanObject,
    mut v_a_6286_: *mut crate::leanh::LeanObject,
    mut v_a_6287_: *mut crate::leanh::LeanObject,
    mut v_a_6288_: *mut crate::leanh::LeanObject,
    mut v_a_6289_: *mut crate::leanh::LeanObject,
    mut v_a_6290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6291_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(
        v_funDecl_6282_,
        v_a_6283_,
        v_a_6284_,
        v_a_6285_,
        v_a_6286_,
        v_a_6287_,
        v_a_6288_,
        v_a_6289_,
    );
    crate::leanh::lean_dec(v_a_6289_);
    crate::leanh::lean_dec_ref(v_a_6288_);
    crate::leanh::lean_dec(v_a_6287_);
    crate::leanh::lean_dec_ref(v_a_6286_);
    crate::leanh::lean_dec_ref(v_a_6285_);
    crate::leanh::lean_dec(v_a_6284_);
    crate::leanh::lean_dec_ref(v_a_6283_);
    return v_res_6291_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_check___boxed(
    mut v_code_6292_: *mut crate::leanh::LeanObject,
    mut v_a_6293_: *mut crate::leanh::LeanObject,
    mut v_a_6294_: *mut crate::leanh::LeanObject,
    mut v_a_6295_: *mut crate::leanh::LeanObject,
    mut v_a_6296_: *mut crate::leanh::LeanObject,
    mut v_a_6297_: *mut crate::leanh::LeanObject,
    mut v_a_6298_: *mut crate::leanh::LeanObject,
    mut v_a_6299_: *mut crate::leanh::LeanObject,
    mut v_a_6300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6301_ = l_Lean_Compiler_LCNF_Check_Pure_check(
        v_code_6292_,
        v_a_6293_,
        v_a_6294_,
        v_a_6295_,
        v_a_6296_,
        v_a_6297_,
        v_a_6298_,
        v_a_6299_,
    );
    crate::leanh::lean_dec(v_a_6299_);
    crate::leanh::lean_dec_ref(v_a_6298_);
    crate::leanh::lean_dec(v_a_6297_);
    crate::leanh::lean_dec_ref(v_a_6296_);
    crate::leanh::lean_dec_ref(v_a_6295_);
    crate::leanh::lean_dec(v_a_6294_);
    return v_res_6301_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed(
    mut v_declName_6302_: *mut crate::leanh::LeanObject,
    mut v_params_6303_: *mut crate::leanh::LeanObject,
    mut v_type_6304_: *mut crate::leanh::LeanObject,
    mut v_value_6305_: *mut crate::leanh::LeanObject,
    mut v_a_6306_: *mut crate::leanh::LeanObject,
    mut v_a_6307_: *mut crate::leanh::LeanObject,
    mut v_a_6308_: *mut crate::leanh::LeanObject,
    mut v_a_6309_: *mut crate::leanh::LeanObject,
    mut v_a_6310_: *mut crate::leanh::LeanObject,
    mut v_a_6311_: *mut crate::leanh::LeanObject,
    mut v_a_6312_: *mut crate::leanh::LeanObject,
    mut v_a_6313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6314_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(
        v_declName_6302_,
        v_params_6303_,
        v_type_6304_,
        v_value_6305_,
        v_a_6306_,
        v_a_6307_,
        v_a_6308_,
        v_a_6309_,
        v_a_6310_,
        v_a_6311_,
        v_a_6312_,
    );
    crate::leanh::lean_dec(v_a_6312_);
    crate::leanh::lean_dec_ref(v_a_6311_);
    crate::leanh::lean_dec(v_a_6310_);
    crate::leanh::lean_dec_ref(v_a_6309_);
    crate::leanh::lean_dec_ref(v_a_6308_);
    crate::leanh::lean_dec(v_a_6307_);
    crate::leanh::lean_dec_ref(v_a_6306_);
    return v_res_6314_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___boxed(
    mut v_typeName_6315_: *mut crate::leanh::LeanObject,
    mut v_as_6316_: *mut crate::leanh::LeanObject,
    mut v_sz_6317_: *mut crate::leanh::LeanObject,
    mut v_i_6318_: *mut crate::leanh::LeanObject,
    mut v_b_6319_: *mut crate::leanh::LeanObject,
    mut v___y_6320_: *mut crate::leanh::LeanObject,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
    mut v___y_6325_: *mut crate::leanh::LeanObject,
    mut v___y_6326_: *mut crate::leanh::LeanObject,
    mut v___y_6327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6328_: usize = 0;
    let mut v_i_boxed_6329_: usize = 0;
    let mut v_res_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6328_ = crate::leanh::lean_unbox_usize(v_sz_6317_);
    crate::leanh::lean_dec(v_sz_6317_);
    v_i_boxed_6329_ = crate::leanh::lean_unbox_usize(v_i_6318_);
    crate::leanh::lean_dec(v_i_6318_);
    v_res_6330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5(v_typeName_6315_, v_as_6316_, v_sz_boxed_6328_, v_i_boxed_6329_, v_b_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_, v___y_6324_, v___y_6325_, v___y_6326_);
    crate::leanh::lean_dec(v___y_6326_);
    crate::leanh::lean_dec_ref(v___y_6325_);
    crate::leanh::lean_dec(v___y_6324_);
    crate::leanh::lean_dec_ref(v___y_6323_);
    crate::leanh::lean_dec_ref(v___y_6322_);
    crate::leanh::lean_dec(v___y_6321_);
    crate::leanh::lean_dec_ref(v___y_6320_);
    crate::leanh::lean_dec_ref(v_as_6316_);
    return v_res_6330_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(
    mut v_as_6331_: *mut crate::leanh::LeanObject,
    mut v_i_6332_: usize,
    mut v_stop_6333_: usize,
    mut v_b_6334_: *mut crate::leanh::LeanObject,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
    mut v___y_6338_: *mut crate::leanh::LeanObject,
    mut v___y_6339_: *mut crate::leanh::LeanObject,
    mut v___y_6340_: *mut crate::leanh::LeanObject,
    mut v___y_6341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_as_6331_, v_i_6332_, v_stop_6333_, v_b_6334_, v___y_6336_, v___y_6338_, v___y_6339_, v___y_6340_, v___y_6341_);
    return v___x_6343_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___boxed(
    mut v_as_6344_: *mut crate::leanh::LeanObject,
    mut v_i_6345_: *mut crate::leanh::LeanObject,
    mut v_stop_6346_: *mut crate::leanh::LeanObject,
    mut v_b_6347_: *mut crate::leanh::LeanObject,
    mut v___y_6348_: *mut crate::leanh::LeanObject,
    mut v___y_6349_: *mut crate::leanh::LeanObject,
    mut v___y_6350_: *mut crate::leanh::LeanObject,
    mut v___y_6351_: *mut crate::leanh::LeanObject,
    mut v___y_6352_: *mut crate::leanh::LeanObject,
    mut v___y_6353_: *mut crate::leanh::LeanObject,
    mut v___y_6354_: *mut crate::leanh::LeanObject,
    mut v___y_6355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6356_: usize = 0;
    let mut v_stop_boxed_6357_: usize = 0;
    let mut v_res_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6356_ = crate::leanh::lean_unbox_usize(v_i_6345_);
    crate::leanh::lean_dec(v_i_6345_);
    v_stop_boxed_6357_ = crate::leanh::lean_unbox_usize(v_stop_6346_);
    crate::leanh::lean_dec(v_stop_6346_);
    v_res_6358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(v_as_6344_, v_i_boxed_6356_, v_stop_boxed_6357_, v_b_6347_, v___y_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_);
    crate::leanh::lean_dec(v___y_6354_);
    crate::leanh::lean_dec_ref(v___y_6353_);
    crate::leanh::lean_dec(v___y_6352_);
    crate::leanh::lean_dec_ref(v___y_6351_);
    crate::leanh::lean_dec_ref(v___y_6350_);
    crate::leanh::lean_dec(v___y_6349_);
    crate::leanh::lean_dec_ref(v___y_6348_);
    crate::leanh::lean_dec_ref(v_as_6344_);
    return v_res_6358_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4(
    mut v_00_u03b1_6359_: *mut crate::leanh::LeanObject,
    mut v_constName_6360_: *mut crate::leanh::LeanObject,
    mut v___y_6361_: *mut crate::leanh::LeanObject,
    mut v___y_6362_: *mut crate::leanh::LeanObject,
    mut v___y_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
    mut v___y_6366_: *mut crate::leanh::LeanObject,
    mut v___y_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6369_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_6360_, v___y_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_, v___y_6367_);
    return v___x_6369_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___boxed(
    mut v_00_u03b1_6370_: *mut crate::leanh::LeanObject,
    mut v_constName_6371_: *mut crate::leanh::LeanObject,
    mut v___y_6372_: *mut crate::leanh::LeanObject,
    mut v___y_6373_: *mut crate::leanh::LeanObject,
    mut v___y_6374_: *mut crate::leanh::LeanObject,
    mut v___y_6375_: *mut crate::leanh::LeanObject,
    mut v___y_6376_: *mut crate::leanh::LeanObject,
    mut v___y_6377_: *mut crate::leanh::LeanObject,
    mut v___y_6378_: *mut crate::leanh::LeanObject,
    mut v___y_6379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6380_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4(v_00_u03b1_6370_, v_constName_6371_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_);
    crate::leanh::lean_dec(v___y_6378_);
    crate::leanh::lean_dec_ref(v___y_6377_);
    crate::leanh::lean_dec(v___y_6376_);
    crate::leanh::lean_dec_ref(v___y_6375_);
    crate::leanh::lean_dec_ref(v___y_6374_);
    crate::leanh::lean_dec(v___y_6373_);
    crate::leanh::lean_dec_ref(v___y_6372_);
    return v_res_6380_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6(
    mut v_00_u03b1_6381_: *mut crate::leanh::LeanObject,
    mut v_ref_6382_: *mut crate::leanh::LeanObject,
    mut v_constName_6383_: *mut crate::leanh::LeanObject,
    mut v___y_6384_: *mut crate::leanh::LeanObject,
    mut v___y_6385_: *mut crate::leanh::LeanObject,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6392_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_6382_, v_constName_6383_, v___y_6384_, v___y_6385_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
    return v___x_6392_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___boxed(
    mut v_00_u03b1_6393_: *mut crate::leanh::LeanObject,
    mut v_ref_6394_: *mut crate::leanh::LeanObject,
    mut v_constName_6395_: *mut crate::leanh::LeanObject,
    mut v___y_6396_: *mut crate::leanh::LeanObject,
    mut v___y_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
    mut v___y_6401_: *mut crate::leanh::LeanObject,
    mut v___y_6402_: *mut crate::leanh::LeanObject,
    mut v___y_6403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6404_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6(v_00_u03b1_6393_, v_ref_6394_, v_constName_6395_, v___y_6396_, v___y_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_);
    crate::leanh::lean_dec(v___y_6402_);
    crate::leanh::lean_dec_ref(v___y_6401_);
    crate::leanh::lean_dec(v___y_6400_);
    crate::leanh::lean_dec_ref(v___y_6399_);
    crate::leanh::lean_dec_ref(v___y_6398_);
    crate::leanh::lean_dec(v___y_6397_);
    crate::leanh::lean_dec_ref(v___y_6396_);
    crate::leanh::lean_dec(v_ref_6394_);
    return v_res_6404_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8(
    mut v_00_u03b1_6405_: *mut crate::leanh::LeanObject,
    mut v_ref_6406_: *mut crate::leanh::LeanObject,
    mut v_msg_6407_: *mut crate::leanh::LeanObject,
    mut v_declHint_6408_: *mut crate::leanh::LeanObject,
    mut v___y_6409_: *mut crate::leanh::LeanObject,
    mut v___y_6410_: *mut crate::leanh::LeanObject,
    mut v___y_6411_: *mut crate::leanh::LeanObject,
    mut v___y_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6417_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_6406_, v_msg_6407_, v_declHint_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_);
    return v___x_6417_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_6418_: *mut crate::leanh::LeanObject,
    mut v_ref_6419_: *mut crate::leanh::LeanObject,
    mut v_msg_6420_: *mut crate::leanh::LeanObject,
    mut v_declHint_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
    mut v___y_6423_: *mut crate::leanh::LeanObject,
    mut v___y_6424_: *mut crate::leanh::LeanObject,
    mut v___y_6425_: *mut crate::leanh::LeanObject,
    mut v___y_6426_: *mut crate::leanh::LeanObject,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6430_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8(v_00_u03b1_6418_, v_ref_6419_, v_msg_6420_, v_declHint_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_);
    crate::leanh::lean_dec(v___y_6428_);
    crate::leanh::lean_dec_ref(v___y_6427_);
    crate::leanh::lean_dec(v___y_6426_);
    crate::leanh::lean_dec_ref(v___y_6425_);
    crate::leanh::lean_dec_ref(v___y_6424_);
    crate::leanh::lean_dec(v___y_6423_);
    crate::leanh::lean_dec_ref(v___y_6422_);
    crate::leanh::lean_dec(v_ref_6419_);
    return v_res_6430_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10(
    mut v_msg_6431_: *mut crate::leanh::LeanObject,
    mut v_declHint_6432_: *mut crate::leanh::LeanObject,
    mut v___y_6433_: *mut crate::leanh::LeanObject,
    mut v___y_6434_: *mut crate::leanh::LeanObject,
    mut v___y_6435_: *mut crate::leanh::LeanObject,
    mut v___y_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
    mut v___y_6438_: *mut crate::leanh::LeanObject,
    mut v___y_6439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6441_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_6431_, v_declHint_6432_, v___y_6439_);
    return v___x_6441_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___boxed(
    mut v_msg_6442_: *mut crate::leanh::LeanObject,
    mut v_declHint_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
    mut v___y_6445_: *mut crate::leanh::LeanObject,
    mut v___y_6446_: *mut crate::leanh::LeanObject,
    mut v___y_6447_: *mut crate::leanh::LeanObject,
    mut v___y_6448_: *mut crate::leanh::LeanObject,
    mut v___y_6449_: *mut crate::leanh::LeanObject,
    mut v___y_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6452_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10(v_msg_6442_, v_declHint_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_);
    crate::leanh::lean_dec(v___y_6450_);
    crate::leanh::lean_dec_ref(v___y_6449_);
    crate::leanh::lean_dec(v___y_6448_);
    crate::leanh::lean_dec_ref(v___y_6447_);
    crate::leanh::lean_dec_ref(v___y_6446_);
    crate::leanh::lean_dec(v___y_6445_);
    crate::leanh::lean_dec_ref(v___y_6444_);
    return v_res_6452_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10(
    mut v_00_u03b1_6453_: *mut crate::leanh::LeanObject,
    mut v_ref_6454_: *mut crate::leanh::LeanObject,
    mut v_msg_6455_: *mut crate::leanh::LeanObject,
    mut v___y_6456_: *mut crate::leanh::LeanObject,
    mut v___y_6457_: *mut crate::leanh::LeanObject,
    mut v___y_6458_: *mut crate::leanh::LeanObject,
    mut v___y_6459_: *mut crate::leanh::LeanObject,
    mut v___y_6460_: *mut crate::leanh::LeanObject,
    mut v___y_6461_: *mut crate::leanh::LeanObject,
    mut v___y_6462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6464_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_6454_, v_msg_6455_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_);
    return v___x_6464_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___boxed(
    mut v_00_u03b1_6465_: *mut crate::leanh::LeanObject,
    mut v_ref_6466_: *mut crate::leanh::LeanObject,
    mut v_msg_6467_: *mut crate::leanh::LeanObject,
    mut v___y_6468_: *mut crate::leanh::LeanObject,
    mut v___y_6469_: *mut crate::leanh::LeanObject,
    mut v___y_6470_: *mut crate::leanh::LeanObject,
    mut v___y_6471_: *mut crate::leanh::LeanObject,
    mut v___y_6472_: *mut crate::leanh::LeanObject,
    mut v___y_6473_: *mut crate::leanh::LeanObject,
    mut v___y_6474_: *mut crate::leanh::LeanObject,
    mut v___y_6475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6476_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_6465_, v_ref_6466_, v_msg_6467_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_);
    crate::leanh::lean_dec(v___y_6474_);
    crate::leanh::lean_dec_ref(v___y_6473_);
    crate::leanh::lean_dec(v___y_6472_);
    crate::leanh::lean_dec_ref(v___y_6471_);
    crate::leanh::lean_dec_ref(v___y_6470_);
    crate::leanh::lean_dec(v___y_6469_);
    crate::leanh::lean_dec_ref(v___y_6468_);
    crate::leanh::lean_dec(v_ref_6466_);
    return v_res_6476_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6479_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6479_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6480_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1_once),
        _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1,
    );
    v___x_6481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6481_, 0, v___x_6480_);
    return v___x_6481_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6482_ = crate::leanh::lean_box(1);
    v___x_6483_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_6484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2_once),
        _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2,
    );
    v___x_6485_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6485_, 0, v___x_6484_);
    crate::leanh::lean_ctor_set(v___x_6485_, 1, v___x_6483_);
    crate::leanh::lean_ctor_set(v___x_6485_, 2, v___x_6482_);
    return v___x_6485_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
    mut v_x_6486_: *mut crate::leanh::LeanObject,
    mut v_a_6487_: *mut crate::leanh::LeanObject,
    mut v_a_6488_: *mut crate::leanh::LeanObject,
    mut v_a_6489_: *mut crate::leanh::LeanObject,
    mut v_a_6490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6500_: u8 = 0;
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6492_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v___x_6493_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0;
                v___x_6494_ = lean_st_mk_ref(v___x_6492_);
                v___x_6495_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3,
                );
                crate::leanh::lean_inc(v_a_6490_);
                crate::leanh::lean_inc_ref(v_a_6489_);
                crate::leanh::lean_inc(v_a_6488_);
                crate::leanh::lean_inc_ref(v_a_6487_);
                crate::leanh::lean_inc(v___x_6494_);
                v___x_6496_ = crate::leanh::lean_apply_8(
                    v_x_6486_,
                    v___x_6493_,
                    v___x_6494_,
                    v___x_6495_,
                    v_a_6487_,
                    v_a_6488_,
                    v_a_6489_,
                    v_a_6490_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6496_) == 0 {
                    v_a_6497_ = crate::leanh::lean_ctor_get(v___x_6496_, 0);
                    v_isSharedCheck_6505_ = (!crate::leanh::lean_is_exclusive(v___x_6496_)) as u8;
                    if v_isSharedCheck_6505_ == 0 {
                        v___x_6499_ = v___x_6496_;
                        v_isShared_6500_ = v_isSharedCheck_6505_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6497_);
                        crate::leanh::lean_dec(v___x_6496_);
                        v___x_6499_ = crate::leanh::lean_box(0);
                        v_isShared_6500_ = v_isSharedCheck_6505_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6494_);
                    return v___x_6496_;
                }
            }
            1 => {
                v___x_6501_ = lean_st_ref_get(v___x_6494_);
                crate::leanh::lean_dec(v___x_6494_);
                crate::leanh::lean_dec(v___x_6501_);
                if v_isShared_6500_ == 0 {
                    v___x_6503_ = v___x_6499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6504_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6497_);
                    v___x_6503_ = v_reuseFailAlloc_6504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run___redArg___boxed(
    mut v_x_6506_: *mut crate::leanh::LeanObject,
    mut v_a_6507_: *mut crate::leanh::LeanObject,
    mut v_a_6508_: *mut crate::leanh::LeanObject,
    mut v_a_6509_: *mut crate::leanh::LeanObject,
    mut v_a_6510_: *mut crate::leanh::LeanObject,
    mut v_a_6511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6512_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
        v_x_6506_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_,
    );
    crate::leanh::lean_dec(v_a_6510_);
    crate::leanh::lean_dec_ref(v_a_6509_);
    crate::leanh::lean_dec(v_a_6508_);
    crate::leanh::lean_dec_ref(v_a_6507_);
    return v_res_6512_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run(
    mut v_00_u03b1_6513_: *mut crate::leanh::LeanObject,
    mut v_x_6514_: *mut crate::leanh::LeanObject,
    mut v_a_6515_: *mut crate::leanh::LeanObject,
    mut v_a_6516_: *mut crate::leanh::LeanObject,
    mut v_a_6517_: *mut crate::leanh::LeanObject,
    mut v_a_6518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6520_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
        v_x_6514_, v_a_6515_, v_a_6516_, v_a_6517_, v_a_6518_,
    );
    return v___x_6520_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run___boxed(
    mut v_00_u03b1_6521_: *mut crate::leanh::LeanObject,
    mut v_x_6522_: *mut crate::leanh::LeanObject,
    mut v_a_6523_: *mut crate::leanh::LeanObject,
    mut v_a_6524_: *mut crate::leanh::LeanObject,
    mut v_a_6525_: *mut crate::leanh::LeanObject,
    mut v_a_6526_: *mut crate::leanh::LeanObject,
    mut v_a_6527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6528_ = l_Lean_Compiler_LCNF_Check_Pure_run(
        v_00_u03b1_6521_,
        v_x_6522_,
        v_a_6523_,
        v_a_6524_,
        v_a_6525_,
        v_a_6526_,
    );
    crate::leanh::lean_dec(v_a_6526_);
    crate::leanh::lean_dec_ref(v_a_6525_);
    crate::leanh::lean_dec(v_a_6524_);
    crate::leanh::lean_dec_ref(v_a_6523_);
    return v_res_6528_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(
    mut v_f_6529_: *mut crate::leanh::LeanObject,
    mut v_v_6530_: *mut crate::leanh::LeanObject,
    mut v___y_6531_: *mut crate::leanh::LeanObject,
    mut v___y_6532_: *mut crate::leanh::LeanObject,
    mut v___y_6533_: *mut crate::leanh::LeanObject,
    mut v___y_6534_: *mut crate::leanh::LeanObject,
    mut v___y_6535_: *mut crate::leanh::LeanObject,
    mut v___y_6536_: *mut crate::leanh::LeanObject,
    mut v___y_6537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6543_: u8 = 0;
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6548_: u8 = 0;
    let mut v_unused_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_6530_) == 0 {
                    v_code_6539_ = crate::leanh::lean_ctor_get(v_v_6530_, 0);
                    crate::leanh::lean_inc_ref(v_code_6539_);
                    crate::leanh::lean_dec_ref_known(v_v_6530_, 1);
                    crate::leanh::lean_inc(v___y_6537_);
                    crate::leanh::lean_inc_ref(v___y_6536_);
                    crate::leanh::lean_inc(v___y_6535_);
                    crate::leanh::lean_inc_ref(v___y_6534_);
                    crate::leanh::lean_inc_ref(v___y_6533_);
                    crate::leanh::lean_inc(v___y_6532_);
                    crate::leanh::lean_inc_ref(v___y_6531_);
                    v___x_6540_ = crate::leanh::lean_apply_9(
                        v_f_6529_,
                        v_code_6539_,
                        v___y_6531_,
                        v___y_6532_,
                        v___y_6533_,
                        v___y_6534_,
                        v___y_6535_,
                        v___y_6536_,
                        v___y_6537_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6540_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_6529_);
                    v_isSharedCheck_6548_ = (!crate::leanh::lean_is_exclusive(v_v_6530_)) as u8;
                    if v_isSharedCheck_6548_ == 0 {
                        v_unused_6549_ = crate::leanh::lean_ctor_get(v_v_6530_, 0);
                        crate::leanh::lean_dec(v_unused_6549_);
                        v___x_6542_ = v_v_6530_;
                        v_isShared_6543_ = v_isSharedCheck_6548_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_6530_);
                        v___x_6542_ = crate::leanh::lean_box(0);
                        v_isShared_6543_ = v_isSharedCheck_6548_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6544_ = crate::leanh::lean_box(0);
                if v_isShared_6543_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6542_, 0);
                    crate::leanh::lean_ctor_set(v___x_6542_, 0, v___x_6544_);
                    v___x_6546_ = v___x_6542_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6547_, 0, v___x_6544_);
                    v___x_6546_ = v_reuseFailAlloc_6547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg___boxed(
    mut v_f_6550_: *mut crate::leanh::LeanObject,
    mut v_v_6551_: *mut crate::leanh::LeanObject,
    mut v___y_6552_: *mut crate::leanh::LeanObject,
    mut v___y_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
    mut v___y_6555_: *mut crate::leanh::LeanObject,
    mut v___y_6556_: *mut crate::leanh::LeanObject,
    mut v___y_6557_: *mut crate::leanh::LeanObject,
    mut v___y_6558_: *mut crate::leanh::LeanObject,
    mut v___y_6559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6560_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(v_f_6550_, v_v_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
    crate::leanh::lean_dec(v___y_6558_);
    crate::leanh::lean_dec_ref(v___y_6557_);
    crate::leanh::lean_dec(v___y_6556_);
    crate::leanh::lean_dec_ref(v___y_6555_);
    crate::leanh::lean_dec_ref(v___y_6554_);
    crate::leanh::lean_dec(v___y_6553_);
    crate::leanh::lean_dec_ref(v___y_6552_);
    return v_res_6560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0(
    mut v_pu_6561_: u8,
    mut v_f_6562_: *mut crate::leanh::LeanObject,
    mut v_v_6563_: *mut crate::leanh::LeanObject,
    mut v___y_6564_: *mut crate::leanh::LeanObject,
    mut v___y_6565_: *mut crate::leanh::LeanObject,
    mut v___y_6566_: *mut crate::leanh::LeanObject,
    mut v___y_6567_: *mut crate::leanh::LeanObject,
    mut v___y_6568_: *mut crate::leanh::LeanObject,
    mut v___y_6569_: *mut crate::leanh::LeanObject,
    mut v___y_6570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6572_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(v_f_6562_, v_v_6563_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_);
    return v___x_6572_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed(
    mut v_pu_6573_: *mut crate::leanh::LeanObject,
    mut v_f_6574_: *mut crate::leanh::LeanObject,
    mut v_v_6575_: *mut crate::leanh::LeanObject,
    mut v___y_6576_: *mut crate::leanh::LeanObject,
    mut v___y_6577_: *mut crate::leanh::LeanObject,
    mut v___y_6578_: *mut crate::leanh::LeanObject,
    mut v___y_6579_: *mut crate::leanh::LeanObject,
    mut v___y_6580_: *mut crate::leanh::LeanObject,
    mut v___y_6581_: *mut crate::leanh::LeanObject,
    mut v___y_6582_: *mut crate::leanh::LeanObject,
    mut v___y_6583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6584_: u8 = 0;
    let mut v_res_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6584_ = (crate::leanh::lean_unbox(v_pu_6573_) as u8);
    v_res_6585_ =
        l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0(
            v_pu_boxed_6584_,
            v_f_6574_,
            v_v_6575_,
            v___y_6576_,
            v___y_6577_,
            v___y_6578_,
            v___y_6579_,
            v___y_6580_,
            v___y_6581_,
            v___y_6582_,
        );
    crate::leanh::lean_dec(v___y_6582_);
    crate::leanh::lean_dec_ref(v___y_6581_);
    crate::leanh::lean_dec(v___y_6580_);
    crate::leanh::lean_dec_ref(v___y_6579_);
    crate::leanh::lean_dec_ref(v___y_6578_);
    crate::leanh::lean_dec(v___y_6577_);
    crate::leanh::lean_dec_ref(v___y_6576_);
    return v_res_6585_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_check(
    mut v_pu_6586_: u8,
    mut v_decl_6587_: *mut crate::leanh::LeanObject,
    mut v_a_6588_: *mut crate::leanh::LeanObject,
    mut v_a_6589_: *mut crate::leanh::LeanObject,
    mut v_a_6590_: *mut crate::leanh::LeanObject,
    mut v_a_6591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_pu_6586_ == 0 {
        let mut v_toSignature_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_params_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toSignature_6593_ = crate::leanh::lean_ctor_get(v_decl_6587_, 0);
        crate::leanh::lean_inc_ref(v_toSignature_6593_);
        v_value_6594_ = crate::leanh::lean_ctor_get(v_decl_6587_, 1);
        crate::leanh::lean_inc_ref(v_value_6594_);
        crate::leanh::lean_dec_ref(v_decl_6587_);
        v_name_6595_ = crate::leanh::lean_ctor_get(v_toSignature_6593_, 0);
        crate::leanh::lean_inc(v_name_6595_);
        v_type_6596_ = crate::leanh::lean_ctor_get(v_toSignature_6593_, 2);
        crate::leanh::lean_inc_ref(v_type_6596_);
        v_params_6597_ = crate::leanh::lean_ctor_get(v_toSignature_6593_, 3);
        crate::leanh::lean_inc_ref(v_params_6597_);
        crate::leanh::lean_dec_ref(v_toSignature_6593_);
        v___x_6598_ = crate::leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed as *mut core::ffi::c_void,
            12,
            3,
        );
        crate::leanh::lean_closure_set(v___x_6598_, 0, v_name_6595_);
        crate::leanh::lean_closure_set(v___x_6598_, 1, v_params_6597_);
        crate::leanh::lean_closure_set(v___x_6598_, 2, v_type_6596_);
        v___x_6599_ = crate::leanh::lean_box((v_pu_6586_) as usize);
        v___x_6600_ = crate::leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed as *mut core::ffi::c_void, 11, 3);
        crate::leanh::lean_closure_set(v___x_6600_, 0, v___x_6599_);
        crate::leanh::lean_closure_set(v___x_6600_, 1, v___x_6598_);
        crate::leanh::lean_closure_set(v___x_6600_, 2, v_value_6594_);
        v___x_6601_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
            v___x_6600_,
            v_a_6588_,
            v_a_6589_,
            v_a_6590_,
            v_a_6591_,
        );
        return v___x_6601_;
    } else {
        let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_decl_6587_);
        v___x_6602_ = crate::leanh::lean_box(0);
        v___x_6603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6603_, 0, v___x_6602_);
        return v___x_6603_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_check___boxed(
    mut v_pu_6604_: *mut crate::leanh::LeanObject,
    mut v_decl_6605_: *mut crate::leanh::LeanObject,
    mut v_a_6606_: *mut crate::leanh::LeanObject,
    mut v_a_6607_: *mut crate::leanh::LeanObject,
    mut v_a_6608_: *mut crate::leanh::LeanObject,
    mut v_a_6609_: *mut crate::leanh::LeanObject,
    mut v_a_6610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6611_: u8 = 0;
    let mut v_res_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6611_ = (crate::leanh::lean_unbox(v_pu_6604_) as u8);
    v_res_6612_ = l_Lean_Compiler_LCNF_Decl_check(
        v_pu_boxed_6611_,
        v_decl_6605_,
        v_a_6606_,
        v_a_6607_,
        v_a_6608_,
        v_a_6609_,
    );
    crate::leanh::lean_dec(v_a_6609_);
    crate::leanh::lean_dec_ref(v_a_6608_);
    crate::leanh::lean_dec(v_a_6607_);
    crate::leanh::lean_dec_ref(v_a_6606_);
    return v_res_6612_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Check(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Check(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Check(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Check(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Check(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Check(builtin);
}
