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
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 97, 116, 32, 76, 67, 78, 70, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 97, 114, 103, 117, 109, 101, 110, 116, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [10, 98, 117, 116, 32, 105, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__0_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__1_value: leanh::LeanStringObject<
    33,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__3_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__5_value: leanh::LeanStringObject<
    19,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__7_value: leanh::LeanStringObject<
    15,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 32, 96, 99, 97, 115, 101, 115, 96, 44, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [96, 32, 104, 97, 115, 32, 35, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [32, 102, 105, 101, 108, 100, 115, 44, 32, 98, 117, 116, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 104, 97, 115, 32, 35, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 111, 102, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 110, 97, 109, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 32, 96, 99, 97, 115, 101, 115, 96, 44, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [96, 32, 111, 99, 99, 117, 114, 115, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 111, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(
    mut v_a_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v_checkTypes_3314_: u8 = 0;
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_a_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3309_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_3307_);
                if leanh::lean_obj_tag(v___x_3309_) == 0 {
                    v_a_3310_ = leanh::lean_ctor_get(v___x_3309_, 0);
                    v_isSharedCheck_3319_ = (!leanh::lean_is_exclusive(v___x_3309_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3312_ = v___x_3309_;
                        v_isShared_3313_ = v_isSharedCheck_3319_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3310_);
                        leanh::lean_dec(v___x_3309_);
                        v___x_3312_ = leanh::lean_box(0);
                        v_isShared_3313_ = v_isSharedCheck_3319_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3320_ = leanh::lean_ctor_get(v___x_3309_, 0);
                    v_isSharedCheck_3327_ = (!leanh::lean_is_exclusive(v___x_3309_)) as u8;
                    if v_isSharedCheck_3327_ == 0 {
                        v___x_3322_ = v___x_3309_;
                        v_isShared_3323_ = v_isSharedCheck_3327_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3320_);
                        leanh::lean_dec(v___x_3309_);
                        v___x_3322_ = leanh::lean_box(0);
                        v_isShared_3323_ = v_isSharedCheck_3327_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_checkTypes_3314_ = leanh::lean_ctor_get_uint8(
                    v_a_3310_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                leanh::lean_dec(v_a_3310_);
                v___x_3315_ = leanh::lean_box((v_checkTypes_3314_) as usize);
                if v_isShared_3313_ == 0 {
                    leanh::lean_ctor_set(v___x_3312_, 0, v___x_3315_);
                    v___x_3317_ = v___x_3312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
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
                    v_reuseFailAlloc_3326_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
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
    mut v_a_3328_: *mut leanh::LeanObject,
    mut v_a_3329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3330_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_3328_);
    leanh::lean_dec_ref(v_a_3328_);
    return v_res_3330_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes(
    mut v_a_3331_: *mut leanh::LeanObject,
    mut v_a_3332_: *mut leanh::LeanObject,
    mut v_a_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
    mut v_a_3337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_3334_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes___boxed(
    mut v_a_3340_: *mut leanh::LeanObject,
    mut v_a_3341_: *mut leanh::LeanObject,
    mut v_a_3342_: *mut leanh::LeanObject,
    mut v_a_3343_: *mut leanh::LeanObject,
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_a_3345_: *mut leanh::LeanObject,
    mut v_a_3346_: *mut leanh::LeanObject,
    mut v_a_3347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3348_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes(
        v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_,
    );
    leanh::lean_dec(v_a_3346_);
    leanh::lean_dec_ref(v_a_3345_);
    leanh::lean_dec(v_a_3344_);
    leanh::lean_dec_ref(v_a_3343_);
    leanh::lean_dec_ref(v_a_3342_);
    leanh::lean_dec(v_a_3341_);
    leanh::lean_dec_ref(v_a_3340_);
    return v_res_3348_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3349_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3349_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3350_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0);
    v___x_3351_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3351_, 0, v___x_3350_);
    return v___x_3351_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3352_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1);
    v___x_3353_ = leanh::lean_unsigned_to_nat(0);
    v___x_3354_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3354_, 0, v___x_3353_);
    leanh::lean_ctor_set(v___x_3354_, 1, v___x_3353_);
    leanh::lean_ctor_set(v___x_3354_, 2, v___x_3353_);
    leanh::lean_ctor_set(v___x_3354_, 3, v___x_3353_);
    leanh::lean_ctor_set(v___x_3354_, 4, v___x_3352_);
    leanh::lean_ctor_set(v___x_3354_, 5, v___x_3352_);
    leanh::lean_ctor_set(v___x_3354_, 6, v___x_3352_);
    leanh::lean_ctor_set(v___x_3354_, 7, v___x_3352_);
    leanh::lean_ctor_set(v___x_3354_, 8, v___x_3352_);
    leanh::lean_ctor_set(v___x_3354_, 9, v___x_3352_);
    return v___x_3354_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
    mut v_msg_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
    mut v___y_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v_env_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_unused_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3388_: u8 = 0;
    let mut v_a_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3392_: u8 = 0;
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3361_ = leanh::lean_ctor_get(v___y_3358_, 2);
                v_ref_3362_ = leanh::lean_ctor_get(v___y_3358_, 5);
                v___x_3363_ = lean_st_ref_get(v___y_3359_);
                v___x_3364_ = lean_st_ref_get(v___y_3357_);
                v___x_3365_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3356_);
                if leanh::lean_obj_tag(v___x_3365_) == 0 {
                    v_a_3366_ = leanh::lean_ctor_get(v___x_3365_, 0);
                    v_isSharedCheck_3388_ = (!leanh::lean_is_exclusive(v___x_3365_)) as u8;
                    if v_isSharedCheck_3388_ == 0 {
                        v___x_3368_ = v___x_3365_;
                        v_isShared_3369_ = v_isSharedCheck_3388_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3366_);
                        leanh::lean_dec(v___x_3365_);
                        v___x_3368_ = leanh::lean_box(0);
                        v_isShared_3369_ = v_isSharedCheck_3388_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3364_);
                    leanh::lean_dec(v___x_3363_);
                    leanh::lean_dec_ref(v_msg_3355_);
                    v_a_3389_ = leanh::lean_ctor_get(v___x_3365_, 0);
                    v_isSharedCheck_3396_ = (!leanh::lean_is_exclusive(v___x_3365_)) as u8;
                    if v_isSharedCheck_3396_ == 0 {
                        v___x_3391_ = v___x_3365_;
                        v_isShared_3392_ = v_isSharedCheck_3396_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3389_);
                        leanh::lean_dec(v___x_3365_);
                        v___x_3391_ = leanh::lean_box(0);
                        v_isShared_3392_ = v_isSharedCheck_3396_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3370_ = leanh::lean_ctor_get(v___x_3363_, 0);
                leanh::lean_inc_ref(v_env_3370_);
                leanh::lean_dec(v___x_3363_);
                v_lctx_3371_ = leanh::lean_ctor_get(v___x_3364_, 0);
                v_isSharedCheck_3386_ = (!leanh::lean_is_exclusive(v___x_3364_)) as u8;
                if v_isSharedCheck_3386_ == 0 {
                    v_unused_3387_ = leanh::lean_ctor_get(v___x_3364_, 1);
                    leanh::lean_dec(v_unused_3387_);
                    v___x_3373_ = v___x_3364_;
                    v_isShared_3374_ = v_isSharedCheck_3386_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lctx_3371_);
                    leanh::lean_dec(v___x_3364_);
                    v___x_3373_ = leanh::lean_box(0);
                    v_isShared_3374_ = v_isSharedCheck_3386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3375_ = (leanh::lean_unbox(v_a_3366_) as u8);
                leanh::lean_dec(v_a_3366_);
                v___x_3376_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3371_, v___x_3375_);
                leanh::lean_dec_ref(v_lctx_3371_);
                v___x_3377_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                leanh::lean_inc_ref(v_options_3361_);
                v___x_3378_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3378_, 0, v_env_3370_);
                leanh::lean_ctor_set(v___x_3378_, 1, v___x_3377_);
                leanh::lean_ctor_set(v___x_3378_, 2, v___x_3376_);
                leanh::lean_ctor_set(v___x_3378_, 3, v_options_3361_);
                if v_isShared_3374_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3373_, 3);
                    leanh::lean_ctor_set(v___x_3373_, 1, v_msg_3355_);
                    leanh::lean_ctor_set(v___x_3373_, 0, v___x_3378_);
                    v___x_3380_ = v___x_3373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3378_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_msg_3355_);
                    v___x_3380_ = v_reuseFailAlloc_3385_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_ref_3362_);
                v___x_3381_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3381_, 0, v_ref_3362_);
                leanh::lean_ctor_set(v___x_3381_, 1, v___x_3380_);
                if v_isShared_3369_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3368_, 1);
                    leanh::lean_ctor_set(v___x_3368_, 0, v___x_3381_);
                    v___x_3383_ = v___x_3368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3384_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
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
                    v_reuseFailAlloc_3395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
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
    mut v_msg_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
    mut v___y_3399_: *mut leanh::LeanObject,
    mut v___y_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
    mut v___y_3402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3403_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
            v_msg_3397_,
            v___y_3398_,
            v___y_3399_,
            v___y_3400_,
            v___y_3401_,
        );
    leanh::lean_dec(v___y_3401_);
    leanh::lean_dec_ref(v___y_3400_);
    leanh::lean_dec(v___y_3399_);
    leanh::lean_dec_ref(v___y_3398_);
    return v_res_3403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1(
    mut v_00_u03b1_3404_: *mut leanh::LeanObject,
    mut v_msg_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3415_: *mut leanh::LeanObject,
    mut v_msg_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3423_);
    leanh::lean_dec_ref(v___y_3422_);
    leanh::lean_dec(v___y_3421_);
    leanh::lean_dec_ref(v___y_3420_);
    leanh::lean_dec_ref(v___y_3419_);
    leanh::lean_dec(v___y_3418_);
    leanh::lean_dec_ref(v___y_3417_);
    return v_res_3425_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(
    mut v_k_3426_: *mut leanh::LeanObject,
    mut v_t_3427_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3427_) == 0 {
                    v_k_3428_ = leanh::lean_ctor_get(v_t_3427_, 1);
                    v_l_3429_ = leanh::lean_ctor_get(v_t_3427_, 3);
                    v_r_3430_ = leanh::lean_ctor_get(v_t_3427_, 4);
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
    mut v_k_3436_: *mut leanh::LeanObject,
    mut v_t_3437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3438_: u8 = 0;
    let mut v_r_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3438_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_k_3436_, v_t_3437_);
    leanh::lean_dec(v_t_3437_);
    leanh::lean_dec(v_k_3436_);
    v_r_3439_ = leanh::lean_box((v_res_3438_) as usize);
    return v_r_3439_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0;
    v___x_3442_ = l_Lean_stringToMessageData(v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFVar(
    mut v_fvarId_3443_: *mut leanh::LeanObject,
    mut v_a_3444_: *mut leanh::LeanObject,
    mut v_a_3445_: *mut leanh::LeanObject,
    mut v_a_3446_: *mut leanh::LeanObject,
    mut v_a_3447_: *mut leanh::LeanObject,
    mut v_a_3448_: *mut leanh::LeanObject,
    mut v_a_3449_: *mut leanh::LeanObject,
    mut v_a_3450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3463_: u8 = 0;
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_3452_ = leanh::lean_ctor_get(v_a_3444_, 1);
                v___x_3453_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_fvarId_3443_, v_vars_3452_);
                if v___x_3453_ == 0 {
                    v___x_3454_ = l_Lean_Compiler_LCNF_getBinderName(
                        v_fvarId_3443_,
                        v_a_3447_,
                        v_a_3448_,
                        v_a_3449_,
                        v_a_3450_,
                    );
                    if leanh::lean_obj_tag(v___x_3454_) == 0 {
                        v_a_3455_ = leanh::lean_ctor_get(v___x_3454_, 0);
                        leanh::lean_inc(v_a_3455_);
                        leanh::lean_dec_ref_known(v___x_3454_, 1);
                        v___x_3456_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1,
                        );
                        v___x_3457_ = l_Lean_MessageData_ofName(v_a_3455_);
                        v___x_3458_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3458_, 0, v___x_3456_);
                        leanh::lean_ctor_set(v___x_3458_, 1, v___x_3457_);
                        v___x_3459_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_3458_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
                        return v___x_3459_;
                    } else {
                        v_a_3460_ = leanh::lean_ctor_get(v___x_3454_, 0);
                        v_isSharedCheck_3467_ =
                            (!leanh::lean_is_exclusive(v___x_3454_)) as u8;
                        if v_isSharedCheck_3467_ == 0 {
                            v___x_3462_ = v___x_3454_;
                            v_isShared_3463_ = v_isSharedCheck_3467_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3460_);
                            leanh::lean_dec(v___x_3454_);
                            v___x_3462_ = leanh::lean_box(0);
                            v_isShared_3463_ = v_isSharedCheck_3467_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fvarId_3443_);
                    v___x_3468_ = leanh::lean_box(0);
                    v___x_3469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3469_, 0, v___x_3468_);
                    return v___x_3469_;
                }
            }
            1 => {
                if v_isShared_3463_ == 0 {
                    v___x_3465_ = v___x_3462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
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
    mut v_fvarId_3470_: *mut leanh::LeanObject,
    mut v_a_3471_: *mut leanh::LeanObject,
    mut v_a_3472_: *mut leanh::LeanObject,
    mut v_a_3473_: *mut leanh::LeanObject,
    mut v_a_3474_: *mut leanh::LeanObject,
    mut v_a_3475_: *mut leanh::LeanObject,
    mut v_a_3476_: *mut leanh::LeanObject,
    mut v_a_3477_: *mut leanh::LeanObject,
    mut v_a_3478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3477_);
    leanh::lean_dec_ref(v_a_3476_);
    leanh::lean_dec(v_a_3475_);
    leanh::lean_dec_ref(v_a_3474_);
    leanh::lean_dec_ref(v_a_3473_);
    leanh::lean_dec(v_a_3472_);
    leanh::lean_dec_ref(v_a_3471_);
    return v_res_3479_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(
    mut v_00_u03b2_3480_: *mut leanh::LeanObject,
    mut v_k_3481_: *mut leanh::LeanObject,
    mut v_t_3482_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3483_: u8 = 0;
    v___x_3483_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_k_3481_, v_t_3482_);
    return v___x_3483_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___boxed(
    mut v_00_u03b2_3484_: *mut leanh::LeanObject,
    mut v_k_3485_: *mut leanh::LeanObject,
    mut v_t_3486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3487_: u8 = 0;
    let mut v_r_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3487_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(v_00_u03b2_3484_, v_k_3485_, v_t_3486_);
    leanh::lean_dec(v_t_3486_);
    leanh::lean_dec(v_k_3485_);
    v_r_3488_ = leanh::lean_box((v_res_3487_) as usize);
    return v_r_3488_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = leanh::lean_unsigned_to_nat(32);
    v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
    v___x_3491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3491_, 0, v___x_3490_);
    return v___x_3491_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3492_: usize = 0;
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = 5usize;
    v___x_3493_ = leanh::lean_unsigned_to_nat(0);
    v___x_3494_ = leanh::lean_unsigned_to_nat(32);
    v___x_3495_ = lean_mk_empty_array_with_capacity(v___x_3494_);
    v___x_3496_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0);
    v___x_3497_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3497_, 0, v___x_3496_);
    leanh::lean_ctor_set(v___x_3497_, 1, v___x_3495_);
    leanh::lean_ctor_set(v___x_3497_, 2, v___x_3493_);
    leanh::lean_ctor_set(v___x_3497_, 3, v___x_3493_);
    leanh::lean_ctor_set_usize(v___x_3497_, 4, v___x_3492_);
    return v___x_3497_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3498_ = leanh::lean_box(1);
    v___x_3499_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_3500_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1);
    v___x_3501_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3501_, 0, v___x_3500_);
    leanh::lean_ctor_set(v___x_3501_, 1, v___x_3499_);
    leanh::lean_ctor_set(v___x_3501_, 2, v___x_3498_);
    return v___x_3501_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_3502_: *mut leanh::LeanObject,
    mut v___y_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3506_ = lean_st_ref_get(v___y_3504_);
    v_env_3507_ = leanh::lean_ctor_get(v___x_3506_, 0);
    leanh::lean_inc_ref(v_env_3507_);
    leanh::lean_dec(v___x_3506_);
    v_options_3508_ = leanh::lean_ctor_get(v___y_3503_, 2);
    v___x_3509_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
    v___x_3510_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
    leanh::lean_inc_ref(v_options_3508_);
    v___x_3511_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3511_, 0, v_env_3507_);
    leanh::lean_ctor_set(v___x_3511_, 1, v___x_3509_);
    leanh::lean_ctor_set(v___x_3511_, 2, v___x_3510_);
    leanh::lean_ctor_set(v___x_3511_, 3, v_options_3508_);
    v___x_3512_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3512_, 0, v___x_3511_);
    leanh::lean_ctor_set(v___x_3512_, 1, v_msgData_3502_);
    v___x_3513_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3513_, 0, v___x_3512_);
    return v___x_3513_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_3514_: *mut leanh::LeanObject,
    mut v___y_3515_: *mut leanh::LeanObject,
    mut v___y_3516_: *mut leanh::LeanObject,
    mut v___y_3517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3518_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_3514_, v___y_3515_, v___y_3516_);
    leanh::lean_dec(v___y_3516_);
    leanh::lean_dec_ref(v___y_3515_);
    return v_res_3518_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_3519_: *mut leanh::LeanObject,
    mut v___y_3520_: *mut leanh::LeanObject,
    mut v___y_3521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3523_ = leanh::lean_ctor_get(v___y_3520_, 5);
                v___x_3524_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_3519_, v___y_3520_, v___y_3521_);
                v_a_3525_ = leanh::lean_ctor_get(v___x_3524_, 0);
                v_isSharedCheck_3533_ = (!leanh::lean_is_exclusive(v___x_3524_)) as u8;
                if v_isSharedCheck_3533_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3525_);
                    leanh::lean_dec(v___x_3524_);
                    v___x_3527_ = leanh::lean_box(0);
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3523_);
                v___x_3529_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3529_, 0, v_ref_3523_);
                leanh::lean_ctor_set(v___x_3529_, 1, v_a_3525_);
                if v_isShared_3528_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3527_, 1);
                    leanh::lean_ctor_set(v___x_3527_, 0, v___x_3529_);
                    v___x_3531_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
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
    mut v_msg_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3538_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3534_, v___y_3535_, v___y_3536_);
    leanh::lean_dec(v___y_3536_);
    leanh::lean_dec_ref(v___y_3535_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_3539_: *mut leanh::LeanObject,
    mut v_msg_3540_: *mut leanh::LeanObject,
    mut v___y_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3556_: u8 = 0;
    let mut v_cancelTk_x3f_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3558_: u8 = 0;
    let mut v_inheritedTraceOptions_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3544_ = leanh::lean_ctor_get(v___y_3541_, 0);
    v_fileMap_3545_ = leanh::lean_ctor_get(v___y_3541_, 1);
    v_options_3546_ = leanh::lean_ctor_get(v___y_3541_, 2);
    v_currRecDepth_3547_ = leanh::lean_ctor_get(v___y_3541_, 3);
    v_maxRecDepth_3548_ = leanh::lean_ctor_get(v___y_3541_, 4);
    v_ref_3549_ = leanh::lean_ctor_get(v___y_3541_, 5);
    v_currNamespace_3550_ = leanh::lean_ctor_get(v___y_3541_, 6);
    v_openDecls_3551_ = leanh::lean_ctor_get(v___y_3541_, 7);
    v_initHeartbeats_3552_ = leanh::lean_ctor_get(v___y_3541_, 8);
    v_maxHeartbeats_3553_ = leanh::lean_ctor_get(v___y_3541_, 9);
    v_quotContext_3554_ = leanh::lean_ctor_get(v___y_3541_, 10);
    v_currMacroScope_3555_ = leanh::lean_ctor_get(v___y_3541_, 11);
    v_diag_3556_ = leanh::lean_ctor_get_uint8(
        v___y_3541_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3557_ = leanh::lean_ctor_get(v___y_3541_, 12);
    v_suppressElabErrors_3558_ = leanh::lean_ctor_get_uint8(
        v___y_3541_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3559_ = leanh::lean_ctor_get(v___y_3541_, 13);
    v_ref_3560_ = l_Lean_replaceRef(v_ref_3539_, v_ref_3549_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3559_);
    leanh::lean_inc(v_cancelTk_x3f_3557_);
    leanh::lean_inc(v_currMacroScope_3555_);
    leanh::lean_inc(v_quotContext_3554_);
    leanh::lean_inc(v_maxHeartbeats_3553_);
    leanh::lean_inc(v_initHeartbeats_3552_);
    leanh::lean_inc(v_openDecls_3551_);
    leanh::lean_inc(v_currNamespace_3550_);
    leanh::lean_inc(v_maxRecDepth_3548_);
    leanh::lean_inc(v_currRecDepth_3547_);
    leanh::lean_inc_ref(v_options_3546_);
    leanh::lean_inc_ref(v_fileMap_3545_);
    leanh::lean_inc_ref(v_fileName_3544_);
    v___x_3561_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3561_, 0, v_fileName_3544_);
    leanh::lean_ctor_set(v___x_3561_, 1, v_fileMap_3545_);
    leanh::lean_ctor_set(v___x_3561_, 2, v_options_3546_);
    leanh::lean_ctor_set(v___x_3561_, 3, v_currRecDepth_3547_);
    leanh::lean_ctor_set(v___x_3561_, 4, v_maxRecDepth_3548_);
    leanh::lean_ctor_set(v___x_3561_, 5, v_ref_3560_);
    leanh::lean_ctor_set(v___x_3561_, 6, v_currNamespace_3550_);
    leanh::lean_ctor_set(v___x_3561_, 7, v_openDecls_3551_);
    leanh::lean_ctor_set(v___x_3561_, 8, v_initHeartbeats_3552_);
    leanh::lean_ctor_set(v___x_3561_, 9, v_maxHeartbeats_3553_);
    leanh::lean_ctor_set(v___x_3561_, 10, v_quotContext_3554_);
    leanh::lean_ctor_set(v___x_3561_, 11, v_currMacroScope_3555_);
    leanh::lean_ctor_set(v___x_3561_, 12, v_cancelTk_x3f_3557_);
    leanh::lean_ctor_set(v___x_3561_, 13, v_inheritedTraceOptions_3559_);
    leanh::lean_ctor_set_uint8(
        v___x_3561_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3556_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3561_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3558_,
    );
    v___x_3562_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3540_, v___x_3561_, v___y_3542_);
    leanh::lean_dec_ref_known(v___x_3561_, 14);
    return v___x_3562_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_3563_: *mut leanh::LeanObject,
    mut v_msg_3564_: *mut leanh::LeanObject,
    mut v___y_3565_: *mut leanh::LeanObject,
    mut v___y_3566_: *mut leanh::LeanObject,
    mut v___y_3567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3563_, v_msg_3564_, v___y_3565_, v___y_3566_);
    leanh::lean_dec(v___y_3566_);
    leanh::lean_dec_ref(v___y_3565_);
    leanh::lean_dec(v_ref_3563_);
    return v_res_3568_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3570_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_3571_ = l_Lean_stringToMessageData(v___x_3570_);
    return v___x_3571_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3573_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
    v___x_3574_ = l_Lean_stringToMessageData(v___x_3573_);
    return v___x_3574_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3576_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
    v___x_3577_ = l_Lean_stringToMessageData(v___x_3576_);
    return v___x_3577_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3579_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_3580_ = l_Lean_stringToMessageData(v___x_3579_);
    return v___x_3580_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_3583_ = l_Lean_stringToMessageData(v___x_3582_);
    return v___x_3583_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3585_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_3586_ = l_Lean_stringToMessageData(v___x_3585_);
    return v___x_3586_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3588_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_3589_ = l_Lean_stringToMessageData(v___x_3588_);
    return v___x_3589_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_3590_: *mut leanh::LeanObject,
    mut v_declHint_3591_: *mut leanh::LeanObject,
    mut v___y_3592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v_isExporting_3597_: u8 = 0;
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3619_: u8 = 0;
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: u8 = 0;
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3594_ = lean_st_ref_get(v___y_3592_);
                v_env_3595_ = leanh::lean_ctor_get(v___x_3594_, 0);
                leanh::lean_inc_ref(v_env_3595_);
                leanh::lean_dec(v___x_3594_);
                v___x_3596_ = l_Lean_Name_isAnonymous(v_declHint_3591_);
                if v___x_3596_ == 0 {
                    v_isExporting_3597_ = leanh::lean_ctor_get_uint8(
                        v_env_3595_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3597_ == 0 {
                        leanh::lean_dec_ref(v_env_3595_);
                        leanh::lean_dec(v_declHint_3591_);
                        v___x_3598_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3598_, 0, v_msg_3590_);
                        return v___x_3598_;
                    } else {
                        leanh::lean_inc_ref(v_env_3595_);
                        v___x_3599_ = l_Lean_Environment_setExporting(v_env_3595_, v___x_3596_);
                        leanh::lean_inc(v_declHint_3591_);
                        leanh::lean_inc_ref(v___x_3599_);
                        v___x_3600_ = l_Lean_Environment_contains(
                            v___x_3599_,
                            v_declHint_3591_,
                            v_isExporting_3597_,
                        );
                        if v___x_3600_ == 0 {
                            leanh::lean_dec_ref(v___x_3599_);
                            leanh::lean_dec_ref(v_env_3595_);
                            leanh::lean_dec(v_declHint_3591_);
                            v___x_3601_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3601_, 0, v_msg_3590_);
                            return v___x_3601_;
                        } else {
                            v___x_3602_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                            v___x_3603_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_3604_ = l_Lean_Options_empty;
                            v___x_3605_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3605_, 0, v___x_3599_);
                            leanh::lean_ctor_set(v___x_3605_, 1, v___x_3602_);
                            leanh::lean_ctor_set(v___x_3605_, 2, v___x_3603_);
                            leanh::lean_ctor_set(v___x_3605_, 3, v___x_3604_);
                            leanh::lean_inc(v_declHint_3591_);
                            v___x_3606_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3591_, v___x_3596_);
                            v_c_3607_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3607_, 0, v___x_3605_);
                            leanh::lean_ctor_set(v_c_3607_, 1, v___x_3606_);
                            v___x_3608_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3595_,
                                v_declHint_3591_,
                            );
                            if leanh::lean_obj_tag(v___x_3608_) == 0 {
                                leanh::lean_dec_ref(v_env_3595_);
                                leanh::lean_dec(v_declHint_3591_);
                                v___x_3609_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_3610_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3610_, 0, v___x_3609_);
                                leanh::lean_ctor_set(v___x_3610_, 1, v_c_3607_);
                                v___x_3611_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_3612_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3612_, 0, v___x_3610_);
                                leanh::lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                                v___x_3613_ = l_Lean_MessageData_note(v___x_3612_);
                                v___x_3614_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3614_, 0, v_msg_3590_);
                                leanh::lean_ctor_set(v___x_3614_, 1, v___x_3613_);
                                v___x_3615_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3615_, 0, v___x_3614_);
                                return v___x_3615_;
                            } else {
                                v_val_3616_ = leanh::lean_ctor_get(v___x_3608_, 0);
                                v_isSharedCheck_3651_ =
                                    (!leanh::lean_is_exclusive(v___x_3608_)) as u8;
                                if v_isSharedCheck_3651_ == 0 {
                                    v___x_3618_ = v___x_3608_;
                                    v_isShared_3619_ = v_isSharedCheck_3651_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3616_);
                                    leanh::lean_dec(v___x_3608_);
                                    v___x_3618_ = leanh::lean_box(0);
                                    v_isShared_3619_ = v_isSharedCheck_3651_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3595_);
                    leanh::lean_dec(v_declHint_3591_);
                    v___x_3652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3652_, 0, v_msg_3590_);
                    return v___x_3652_;
                }
            }
            1 => {
                v___x_3620_ = leanh::lean_box(0);
                v___x_3621_ = l_Lean_Environment_header(v_env_3595_);
                leanh::lean_dec_ref(v_env_3595_);
                v___x_3622_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3621_);
                v_mod_3623_ = lean_array_get(v___x_3620_, v___x_3622_, v_val_3616_);
                leanh::lean_dec(v_val_3616_);
                leanh::lean_dec_ref(v___x_3622_);
                v___x_3624_ = l_Lean_isPrivateName(v_declHint_3591_);
                leanh::lean_dec(v_declHint_3591_);
                if v___x_3624_ == 0 {
                    v___x_3625_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_3626_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3626_, 0, v___x_3625_);
                    leanh::lean_ctor_set(v___x_3626_, 1, v_c_3607_);
                    v___x_3627_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_3628_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3628_, 0, v___x_3626_);
                    leanh::lean_ctor_set(v___x_3628_, 1, v___x_3627_);
                    v___x_3629_ = l_Lean_MessageData_ofName(v_mod_3623_);
                    v___x_3630_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3630_, 0, v___x_3628_);
                    leanh::lean_ctor_set(v___x_3630_, 1, v___x_3629_);
                    v___x_3631_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_3632_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3632_, 0, v___x_3630_);
                    leanh::lean_ctor_set(v___x_3632_, 1, v___x_3631_);
                    v___x_3633_ = l_Lean_MessageData_note(v___x_3632_);
                    v___x_3634_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3634_, 0, v_msg_3590_);
                    leanh::lean_ctor_set(v___x_3634_, 1, v___x_3633_);
                    if v_isShared_3619_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3618_, 0);
                        leanh::lean_ctor_set(v___x_3618_, 0, v___x_3634_);
                        v___x_3636_ = v___x_3618_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3637_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
                        v___x_3636_ = v_reuseFailAlloc_3637_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_3639_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3639_, 0, v___x_3638_);
                    leanh::lean_ctor_set(v___x_3639_, 1, v_c_3607_);
                    v___x_3640_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_3641_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3641_, 0, v___x_3639_);
                    leanh::lean_ctor_set(v___x_3641_, 1, v___x_3640_);
                    v___x_3642_ = l_Lean_MessageData_ofName(v_mod_3623_);
                    v___x_3643_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3643_, 0, v___x_3641_);
                    leanh::lean_ctor_set(v___x_3643_, 1, v___x_3642_);
                    v___x_3644_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_3645_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3645_, 0, v___x_3643_);
                    leanh::lean_ctor_set(v___x_3645_, 1, v___x_3644_);
                    v___x_3646_ = l_Lean_MessageData_note(v___x_3645_);
                    v___x_3647_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3647_, 0, v_msg_3590_);
                    leanh::lean_ctor_set(v___x_3647_, 1, v___x_3646_);
                    if v_isShared_3619_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3618_, 0);
                        leanh::lean_ctor_set(v___x_3618_, 0, v___x_3647_);
                        v___x_3649_ = v___x_3618_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
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
    mut v_msg_3653_: *mut leanh::LeanObject,
    mut v_declHint_3654_: *mut leanh::LeanObject,
    mut v___y_3655_: *mut leanh::LeanObject,
    mut v___y_3656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3653_, v_declHint_3654_, v___y_3655_);
    leanh::lean_dec(v___y_3655_);
    return v_res_3657_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_3658_: *mut leanh::LeanObject,
    mut v_declHint_3659_: *mut leanh::LeanObject,
    mut v___y_3660_: *mut leanh::LeanObject,
    mut v___y_3661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3667_: u8 = 0;
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3658_, v_declHint_3659_, v___y_3661_);
                v_a_3664_ = leanh::lean_ctor_get(v___x_3663_, 0);
                v_isSharedCheck_3673_ = (!leanh::lean_is_exclusive(v___x_3663_)) as u8;
                if v_isSharedCheck_3673_ == 0 {
                    v___x_3666_ = v___x_3663_;
                    v_isShared_3667_ = v_isSharedCheck_3673_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3664_);
                    leanh::lean_dec(v___x_3663_);
                    v___x_3666_ = leanh::lean_box(0);
                    v_isShared_3667_ = v_isSharedCheck_3673_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3668_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3669_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3669_, 0, v___x_3668_);
                leanh::lean_ctor_set(v___x_3669_, 1, v_a_3664_);
                if v_isShared_3667_ == 0 {
                    leanh::lean_ctor_set(v___x_3666_, 0, v___x_3669_);
                    v___x_3671_ = v___x_3666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
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
    mut v_msg_3674_: *mut leanh::LeanObject,
    mut v_declHint_3675_: *mut leanh::LeanObject,
    mut v___y_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3679_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3674_, v_declHint_3675_, v___y_3676_, v___y_3677_);
    leanh::lean_dec(v___y_3677_);
    leanh::lean_dec_ref(v___y_3676_);
    return v_res_3679_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_3680_: *mut leanh::LeanObject,
    mut v_msg_3681_: *mut leanh::LeanObject,
    mut v_declHint_3682_: *mut leanh::LeanObject,
    mut v___y_3683_: *mut leanh::LeanObject,
    mut v___y_3684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3686_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3681_, v_declHint_3682_, v___y_3683_, v___y_3684_);
    v_a_3687_ = leanh::lean_ctor_get(v___x_3686_, 0);
    leanh::lean_inc(v_a_3687_);
    leanh::lean_dec_ref(v___x_3686_);
    v___x_3688_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3680_, v_a_3687_, v___y_3683_, v___y_3684_);
    return v___x_3688_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_3689_: *mut leanh::LeanObject,
    mut v_msg_3690_: *mut leanh::LeanObject,
    mut v_declHint_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3689_, v_msg_3690_, v_declHint_3691_, v___y_3692_, v___y_3693_);
    leanh::lean_dec(v___y_3693_);
    leanh::lean_dec_ref(v___y_3692_);
    leanh::lean_dec(v_ref_3689_);
    return v_res_3695_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(
    mut v_ref_3702_: *mut leanh::LeanObject,
    mut v_constName_3703_: *mut leanh::LeanObject,
    mut v___y_3704_: *mut leanh::LeanObject,
    mut v___y_3705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u8 = 0;
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3707_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_3708_ = 0;
    leanh::lean_inc(v_constName_3703_);
    v___x_3709_ = l_Lean_MessageData_ofConstName(v_constName_3703_, v___x_3708_);
    v___x_3710_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3710_, 0, v___x_3707_);
    leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
    v___x_3711_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_3712_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3712_, 0, v___x_3710_);
    leanh::lean_ctor_set(v___x_3712_, 1, v___x_3711_);
    v___x_3713_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3702_, v___x_3712_, v_constName_3703_, v___y_3704_, v___y_3705_);
    return v___x_3713_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_3714_: *mut leanh::LeanObject,
    mut v_constName_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
    mut v___y_3718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3719_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3714_, v_constName_3715_, v___y_3716_, v___y_3717_);
    leanh::lean_dec(v___y_3717_);
    leanh::lean_dec_ref(v___y_3716_);
    leanh::lean_dec(v_ref_3714_);
    return v_res_3719_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(
    mut v_constName_3720_: *mut leanh::LeanObject,
    mut v___y_3721_: *mut leanh::LeanObject,
    mut v___y_3722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3724_ = leanh::lean_ctor_get(v___y_3721_, 5);
    v___x_3725_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3724_, v_constName_3720_, v___y_3721_, v___y_3722_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg___boxed(
    mut v_constName_3726_: *mut leanh::LeanObject,
    mut v___y_3727_: *mut leanh::LeanObject,
    mut v___y_3728_: *mut leanh::LeanObject,
    mut v___y_3729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3726_, v___y_3727_, v___y_3728_);
    leanh::lean_dec(v___y_3728_);
    leanh::lean_dec_ref(v___y_3727_);
    return v_res_3730_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(
    mut v_constName_3731_: *mut leanh::LeanObject,
    mut v___y_3732_: *mut leanh::LeanObject,
    mut v___y_3733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3735_ = lean_st_ref_get(v___y_3733_);
                v_env_3736_ = leanh::lean_ctor_get(v___x_3735_, 0);
                leanh::lean_inc_ref(v_env_3736_);
                leanh::lean_dec(v___x_3735_);
                v___x_3737_ = 0;
                leanh::lean_inc(v_constName_3731_);
                v___x_3738_ =
                    l_Lean_Environment_find_x3f(v_env_3736_, v_constName_3731_, v___x_3737_);
                if leanh::lean_obj_tag(v___x_3738_) == 0 {
                    v___x_3739_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3731_, v___y_3732_, v___y_3733_);
                    return v___x_3739_;
                } else {
                    leanh::lean_dec(v_constName_3731_);
                    v_val_3740_ = leanh::lean_ctor_get(v___x_3738_, 0);
                    v_isSharedCheck_3747_ = (!leanh::lean_is_exclusive(v___x_3738_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3742_ = v___x_3738_;
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3740_);
                        leanh::lean_dec(v___x_3738_);
                        v___x_3742_ = leanh::lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3743_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3742_, 0);
                    v___x_3745_ = v___x_3742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_val_3740_);
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
    mut v_constName_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
    mut v___y_3750_: *mut leanh::LeanObject,
    mut v___y_3751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(
        v_constName_3748_,
        v___y_3749_,
        v___y_3750_,
    );
    leanh::lean_dec(v___y_3750_);
    leanh::lean_dec_ref(v___y_3749_);
    return v_res_3752_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(
    mut v_f_3753_: *mut leanh::LeanObject,
    mut v_i_3754_: *mut leanh::LeanObject,
    mut v_a_3755_: *mut leanh::LeanObject,
    mut v_a_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3763_: u8 = 0;
    let mut v_val_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: u8 = 0;
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_a_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3780_: u8 = 0;
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_f_3753_) == 4 {
                    v_declName_3758_ = leanh::lean_ctor_get(v_f_3753_, 0);
                    leanh::lean_inc(v_declName_3758_);
                    leanh::lean_dec_ref_known(v_f_3753_, 2);
                    v___x_3759_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(v_declName_3758_, v_a_3755_, v_a_3756_);
                    if leanh::lean_obj_tag(v___x_3759_) == 0 {
                        v_a_3760_ = leanh::lean_ctor_get(v___x_3759_, 0);
                        v_isSharedCheck_3776_ =
                            (!leanh::lean_is_exclusive(v___x_3759_)) as u8;
                        if v_isSharedCheck_3776_ == 0 {
                            v___x_3762_ = v___x_3759_;
                            v_isShared_3763_ = v_isSharedCheck_3776_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3760_);
                            leanh::lean_dec(v___x_3759_);
                            v___x_3762_ = leanh::lean_box(0);
                            v_isShared_3763_ = v_isSharedCheck_3776_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3777_ = leanh::lean_ctor_get(v___x_3759_, 0);
                        v_isSharedCheck_3784_ =
                            (!leanh::lean_is_exclusive(v___x_3759_)) as u8;
                        if v_isSharedCheck_3784_ == 0 {
                            v___x_3779_ = v___x_3759_;
                            v_isShared_3780_ = v_isSharedCheck_3784_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3777_);
                            leanh::lean_dec(v___x_3759_);
                            v___x_3779_ = leanh::lean_box(0);
                            v_isShared_3780_ = v_isSharedCheck_3784_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_3753_);
                    v___x_3785_ = 0;
                    v___x_3786_ = leanh::lean_box((v___x_3785_) as usize);
                    v___x_3787_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3787_, 0, v___x_3786_);
                    return v___x_3787_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3760_) == 6 {
                    v_val_3764_ = leanh::lean_ctor_get(v_a_3760_, 0);
                    leanh::lean_inc_ref(v_val_3764_);
                    leanh::lean_dec_ref_known(v_a_3760_, 1);
                    v_numParams_3765_ = leanh::lean_ctor_get(v_val_3764_, 3);
                    leanh::lean_inc(v_numParams_3765_);
                    leanh::lean_dec_ref(v_val_3764_);
                    v___x_3766_ = lean_nat_dec_lt(v_i_3754_, v_numParams_3765_);
                    leanh::lean_dec(v_numParams_3765_);
                    v___x_3767_ = leanh::lean_box((v___x_3766_) as usize);
                    if v_isShared_3763_ == 0 {
                        leanh::lean_ctor_set(v___x_3762_, 0, v___x_3767_);
                        v___x_3769_ = v___x_3762_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3770_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
                        v___x_3769_ = v_reuseFailAlloc_3770_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3760_);
                    v___x_3771_ = 0;
                    v___x_3772_ = leanh::lean_box((v___x_3771_) as usize);
                    if v_isShared_3763_ == 0 {
                        leanh::lean_ctor_set(v___x_3762_, 0, v___x_3772_);
                        v___x_3774_ = v___x_3762_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3775_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
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
                    v_reuseFailAlloc_3783_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
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
    mut v_f_3788_: *mut leanh::LeanObject,
    mut v_i_3789_: *mut leanh::LeanObject,
    mut v_a_3790_: *mut leanh::LeanObject,
    mut v_a_3791_: *mut leanh::LeanObject,
    mut v_a_3792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3793_ =
        l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(v_f_3788_, v_i_3789_, v_a_3790_, v_a_3791_);
    leanh::lean_dec(v_a_3791_);
    leanh::lean_dec_ref(v_a_3790_);
    leanh::lean_dec(v_i_3789_);
    return v_res_3793_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0(
    mut v_00_u03b1_3794_: *mut leanh::LeanObject,
    mut v_constName_3795_: *mut leanh::LeanObject,
    mut v___y_3796_: *mut leanh::LeanObject,
    mut v___y_3797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3799_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3795_, v___y_3796_, v___y_3797_);
    return v___x_3799_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___boxed(
    mut v_00_u03b1_3800_: *mut leanh::LeanObject,
    mut v_constName_3801_: *mut leanh::LeanObject,
    mut v___y_3802_: *mut leanh::LeanObject,
    mut v___y_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3805_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0(v_00_u03b1_3800_, v_constName_3801_, v___y_3802_, v___y_3803_);
    leanh::lean_dec(v___y_3803_);
    leanh::lean_dec_ref(v___y_3802_);
    return v_res_3805_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3806_: *mut leanh::LeanObject,
    mut v_ref_3807_: *mut leanh::LeanObject,
    mut v_constName_3808_: *mut leanh::LeanObject,
    mut v___y_3809_: *mut leanh::LeanObject,
    mut v___y_3810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3807_, v_constName_3808_, v___y_3809_, v___y_3810_);
    return v___x_3812_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3813_: *mut leanh::LeanObject,
    mut v_ref_3814_: *mut leanh::LeanObject,
    mut v_constName_3815_: *mut leanh::LeanObject,
    mut v___y_3816_: *mut leanh::LeanObject,
    mut v___y_3817_: *mut leanh::LeanObject,
    mut v___y_3818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3819_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1(v_00_u03b1_3813_, v_ref_3814_, v_constName_3815_, v___y_3816_, v___y_3817_);
    leanh::lean_dec(v___y_3817_);
    leanh::lean_dec_ref(v___y_3816_);
    leanh::lean_dec(v_ref_3814_);
    return v_res_3819_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_3820_: *mut leanh::LeanObject,
    mut v_ref_3821_: *mut leanh::LeanObject,
    mut v_msg_3822_: *mut leanh::LeanObject,
    mut v_declHint_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3821_, v_msg_3822_, v_declHint_3823_, v___y_3824_, v___y_3825_);
    return v___x_3827_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_3828_: *mut leanh::LeanObject,
    mut v_ref_3829_: *mut leanh::LeanObject,
    mut v_msg_3830_: *mut leanh::LeanObject,
    mut v_declHint_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3828_, v_ref_3829_, v_msg_3830_, v_declHint_3831_, v___y_3832_, v___y_3833_);
    leanh::lean_dec(v___y_3833_);
    leanh::lean_dec_ref(v___y_3832_);
    leanh::lean_dec(v_ref_3829_);
    return v_res_3835_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_3836_: *mut leanh::LeanObject,
    mut v_declHint_3837_: *mut leanh::LeanObject,
    mut v___y_3838_: *mut leanh::LeanObject,
    mut v___y_3839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3836_, v_declHint_3837_, v___y_3839_);
    return v___x_3841_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_3842_: *mut leanh::LeanObject,
    mut v_declHint_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
    mut v___y_3845_: *mut leanh::LeanObject,
    mut v___y_3846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3842_, v_declHint_3843_, v___y_3844_, v___y_3845_);
    leanh::lean_dec(v___y_3845_);
    leanh::lean_dec_ref(v___y_3844_);
    return v_res_3847_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_3848_: *mut leanh::LeanObject,
    mut v_ref_3849_: *mut leanh::LeanObject,
    mut v_msg_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3849_, v_msg_3850_, v___y_3851_, v___y_3852_);
    return v___x_3854_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_3855_: *mut leanh::LeanObject,
    mut v_ref_3856_: *mut leanh::LeanObject,
    mut v_msg_3857_: *mut leanh::LeanObject,
    mut v___y_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3855_, v_ref_3856_, v_msg_3857_, v___y_3858_, v___y_3859_);
    leanh::lean_dec(v___y_3859_);
    leanh::lean_dec_ref(v___y_3858_);
    leanh::lean_dec(v_ref_3856_);
    return v_res_3861_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_3862_: *mut leanh::LeanObject,
    mut v_msg_3863_: *mut leanh::LeanObject,
    mut v___y_3864_: *mut leanh::LeanObject,
    mut v___y_3865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3863_, v___y_3864_, v___y_3865_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_3868_: *mut leanh::LeanObject,
    mut v_msg_3869_: *mut leanh::LeanObject,
    mut v___y_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3873_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3868_, v_msg_3869_, v___y_3870_, v___y_3871_);
    leanh::lean_dec(v___y_3871_);
    leanh::lean_dec_ref(v___y_3870_);
    return v_res_3873_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(
    mut v_sz_3874_: usize,
    mut v_i_3875_: usize,
    mut v_bs_3876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3877_: u8 = 0;
    let mut v_v_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: usize = 0;
    let mut v___x_3883_: usize = 0;
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3877_ = lean_usize_dec_lt(v_i_3875_, v_sz_3874_);
                if v___x_3877_ == 0 {
                    return v_bs_3876_;
                } else {
                    v_v_3878_ = lean_array_uget(v_bs_3876_, v_i_3875_);
                    v___x_3879_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_3886_: *mut leanh::LeanObject,
    mut v_i_3887_: *mut leanh::LeanObject,
    mut v_bs_3888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3889_: usize = 0;
    let mut v_i_boxed_3890_: usize = 0;
    let mut v_res_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3889_ = leanh::lean_unbox_usize(v_sz_3886_);
    leanh::lean_dec(v_sz_3886_);
    v_i_boxed_3890_ = leanh::lean_unbox_usize(v_i_3887_);
    leanh::lean_dec(v_i_3887_);
    v_res_3891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(v_sz_boxed_3889_, v_i_boxed_3890_, v_bs_3888_);
    return v_res_3891_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0;
    v___x_3894_ = l_Lean_stringToMessageData(v___x_3893_);
    return v___x_3894_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3896_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2;
    v___x_3897_ = l_Lean_stringToMessageData(v___x_3896_);
    return v___x_3897_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3899_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4;
    v___x_3900_ = l_Lean_stringToMessageData(v___x_3899_);
    return v___x_3900_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6;
    v___x_3903_ = l_Lean_stringToMessageData(v___x_3902_);
    return v___x_3903_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(
    mut v___x_3904_: *mut leanh::LeanObject,
    mut v___x_3905_: *mut leanh::LeanObject,
    mut v_a_3906_: *mut leanh::LeanObject,
    mut v_args_3907_: *mut leanh::LeanObject,
    mut v_f_3908_: *mut leanh::LeanObject,
    mut v_____x_3909_: *mut leanh::LeanObject,
    mut v_fType_3910_: *mut leanh::LeanObject,
    mut v_j_3911_: *mut leanh::LeanObject,
    mut v___y_3912_: *mut leanh::LeanObject,
    mut v___y_3913_: *mut leanh::LeanObject,
    mut v___y_3914_: *mut leanh::LeanObject,
    mut v___y_3915_: *mut leanh::LeanObject,
    mut v___y_3916_: *mut leanh::LeanObject,
    mut v___y_3917_: *mut leanh::LeanObject,
    mut v___y_3918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v___x_3935_: u8 = 0;
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: u8 = 0;
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3943_: usize = 0;
    let mut v___x_3944_: usize = 0;
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut v_a_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_a_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_a_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3920_ = leanh::lean_ctor_get(v_____x_3909_, 0);
                v_snd_3921_ = leanh::lean_ctor_get(v_____x_3909_, 1);
                v_isSharedCheck_3995_ = (!leanh::lean_is_exclusive(v_____x_3909_)) as u8;
                if v_isSharedCheck_3995_ == 0 {
                    v___x_3923_ = v_____x_3909_;
                    v_isShared_3924_ = v_isSharedCheck_3995_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3921_);
                    leanh::lean_inc(v_fst_3920_);
                    leanh::lean_dec(v_____x_3909_);
                    v___x_3923_ = leanh::lean_box(0);
                    v_isShared_3924_ = v_isSharedCheck_3995_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3932_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v___y_3915_);
                if leanh::lean_obj_tag(v___x_3932_) == 0 {
                    v_a_3933_ = leanh::lean_ctor_get(v___x_3932_, 0);
                    leanh::lean_inc(v_a_3933_);
                    leanh::lean_dec_ref_known(v___x_3932_, 1);
                    v___x_3934_ = (leanh::lean_unbox(v_a_3933_) as u8);
                    leanh::lean_dec(v_a_3933_);
                    if v___x_3934_ == 0 {
                        leanh::lean_dec(v_fst_3920_);
                        leanh::lean_dec_ref(v_f_3908_);
                        leanh::lean_dec_ref(v_args_3907_);
                        leanh::lean_dec(v___x_3905_);
                        state = 2;
                        continue;
                    } else {
                        v___x_3935_ = 0;
                        leanh::lean_inc(v___x_3905_);
                        v___x_3936_ = l_Lean_Compiler_LCNF_Arg_inferType(
                            v___x_3935_,
                            v___x_3905_,
                            v___y_3915_,
                            v___y_3916_,
                            v___y_3917_,
                            v___y_3918_,
                        );
                        if leanh::lean_obj_tag(v___x_3936_) == 0 {
                            v_a_3937_ = leanh::lean_ctor_get(v___x_3936_, 0);
                            leanh::lean_inc_n(v_a_3937_, 2);
                            leanh::lean_dec_ref_known(v___x_3936_, 1);
                            leanh::lean_inc_ref(v_args_3907_);
                            v___x_3938_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(
                                v_fst_3920_,
                                v_j_3911_,
                                v_a_3906_,
                                v_args_3907_,
                            );
                            leanh::lean_dec(v_fst_3920_);
                            leanh::lean_inc_ref(v___x_3938_);
                            v___x_3939_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_a_3937_,
                                v___x_3938_,
                                v___y_3914_,
                                v___y_3915_,
                                v___y_3916_,
                                v___y_3917_,
                                v___y_3918_,
                            );
                            if leanh::lean_obj_tag(v___x_3939_) == 0 {
                                v_a_3940_ = leanh::lean_ctor_get(v___x_3939_, 0);
                                leanh::lean_inc(v_a_3940_);
                                leanh::lean_dec_ref_known(v___x_3939_, 1);
                                v___x_3941_ = (leanh::lean_unbox(v_a_3940_) as u8);
                                leanh::lean_dec(v_a_3940_);
                                if v___x_3941_ == 0 {
                                    v___x_3942_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1);
                                    v_sz_3943_ = lean_array_size(v_args_3907_);
                                    v___x_3944_ = 0usize;
                                    v___x_3945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(v_sz_3943_, v___x_3944_, v_args_3907_);
                                    v___x_3946_ = l_Lean_mkAppN(v_f_3908_, v___x_3945_);
                                    leanh::lean_dec_ref(v___x_3945_);
                                    v___x_3947_ = l_Lean_indentExpr(v___x_3946_);
                                    v___x_3948_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3948_, 0, v___x_3942_);
                                    leanh::lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                                    v___x_3949_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3);
                                    v___x_3950_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                                    leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                                    v___x_3951_ =
                                        l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v___x_3905_);
                                    v___x_3952_ = l_Lean_MessageData_ofExpr(v___x_3951_);
                                    v___x_3953_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3953_, 0, v___x_3950_);
                                    leanh::lean_ctor_set(v___x_3953_, 1, v___x_3952_);
                                    v___x_3954_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5);
                                    v___x_3955_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3955_, 0, v___x_3953_);
                                    leanh::lean_ctor_set(v___x_3955_, 1, v___x_3954_);
                                    v___x_3956_ = l_Lean_indentExpr(v_a_3937_);
                                    v___x_3957_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3957_, 0, v___x_3955_);
                                    leanh::lean_ctor_set(v___x_3957_, 1, v___x_3956_);
                                    v___x_3958_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                                    v___x_3959_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3959_, 0, v___x_3957_);
                                    leanh::lean_ctor_set(v___x_3959_, 1, v___x_3958_);
                                    v___x_3960_ = l_Lean_indentExpr(v___x_3938_);
                                    v___x_3961_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_3959_);
                                    leanh::lean_ctor_set(v___x_3961_, 1, v___x_3960_);
                                    v___x_3962_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_3961_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
                                    if leanh::lean_obj_tag(v___x_3962_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_3962_, 1);
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_del_object(v___x_3923_);
                                        leanh::lean_dec(v_snd_3921_);
                                        leanh::lean_dec(v_j_3911_);
                                        leanh::lean_dec(v___x_3904_);
                                        v_a_3963_ = leanh::lean_ctor_get(v___x_3962_, 0);
                                        v_isSharedCheck_3970_ =
                                            (!leanh::lean_is_exclusive(v___x_3962_)) as u8;
                                        if v_isSharedCheck_3970_ == 0 {
                                            v___x_3965_ = v___x_3962_;
                                            v_isShared_3966_ = v_isSharedCheck_3970_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3963_);
                                            leanh::lean_dec(v___x_3962_);
                                            v___x_3965_ = leanh::lean_box(0);
                                            v_isShared_3966_ = v_isSharedCheck_3970_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_3938_);
                                    leanh::lean_dec(v_a_3937_);
                                    leanh::lean_dec_ref(v_f_3908_);
                                    leanh::lean_dec_ref(v_args_3907_);
                                    leanh::lean_dec(v___x_3905_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_3938_);
                                leanh::lean_dec(v_a_3937_);
                                leanh::lean_del_object(v___x_3923_);
                                leanh::lean_dec(v_snd_3921_);
                                leanh::lean_dec(v_j_3911_);
                                leanh::lean_dec_ref(v_f_3908_);
                                leanh::lean_dec_ref(v_args_3907_);
                                leanh::lean_dec(v___x_3905_);
                                leanh::lean_dec(v___x_3904_);
                                v_a_3971_ = leanh::lean_ctor_get(v___x_3939_, 0);
                                v_isSharedCheck_3978_ =
                                    (!leanh::lean_is_exclusive(v___x_3939_)) as u8;
                                if v_isSharedCheck_3978_ == 0 {
                                    v___x_3973_ = v___x_3939_;
                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3971_);
                                    leanh::lean_dec(v___x_3939_);
                                    v___x_3973_ = leanh::lean_box(0);
                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_3923_);
                            leanh::lean_dec(v_snd_3921_);
                            leanh::lean_dec(v_fst_3920_);
                            leanh::lean_dec(v_j_3911_);
                            leanh::lean_dec_ref(v_f_3908_);
                            leanh::lean_dec_ref(v_args_3907_);
                            leanh::lean_dec(v___x_3905_);
                            leanh::lean_dec(v___x_3904_);
                            v_a_3979_ = leanh::lean_ctor_get(v___x_3936_, 0);
                            v_isSharedCheck_3986_ =
                                (!leanh::lean_is_exclusive(v___x_3936_)) as u8;
                            if v_isSharedCheck_3986_ == 0 {
                                v___x_3981_ = v___x_3936_;
                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3979_);
                                leanh::lean_dec(v___x_3936_);
                                v___x_3981_ = leanh::lean_box(0);
                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3923_);
                    leanh::lean_dec(v_snd_3921_);
                    leanh::lean_dec(v_fst_3920_);
                    leanh::lean_dec(v_j_3911_);
                    leanh::lean_dec_ref(v_f_3908_);
                    leanh::lean_dec_ref(v_args_3907_);
                    leanh::lean_dec(v___x_3905_);
                    leanh::lean_dec(v___x_3904_);
                    v_a_3987_ = leanh::lean_ctor_get(v___x_3932_, 0);
                    v_isSharedCheck_3994_ = (!leanh::lean_is_exclusive(v___x_3932_)) as u8;
                    if v_isSharedCheck_3994_ == 0 {
                        v___x_3989_ = v___x_3932_;
                        v_isShared_3990_ = v_isSharedCheck_3994_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3987_);
                        leanh::lean_dec(v___x_3932_);
                        v___x_3989_ = leanh::lean_box(0);
                        v_isShared_3990_ = v_isSharedCheck_3994_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3924_ == 0 {
                    leanh::lean_ctor_set(v___x_3923_, 1, v_j_3911_);
                    leanh::lean_ctor_set(v___x_3923_, 0, v_snd_3921_);
                    v___x_3927_ = v___x_3923_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_snd_3921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_j_3911_);
                    v___x_3927_ = v_reuseFailAlloc_3931_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3928_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3928_, 0, v___x_3904_);
                leanh::lean_ctor_set(v___x_3928_, 1, v___x_3927_);
                v___x_3929_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                v___x_3930_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3930_, 0, v___x_3929_);
                return v___x_3930_;
            }
            4 => {
                if v_isShared_3966_ == 0 {
                    v___x_3968_ = v___x_3965_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
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
                    v_reuseFailAlloc_3977_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
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
                    v_reuseFailAlloc_3985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
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
                    v_reuseFailAlloc_3993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
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
    mut v___x_3996_: *mut leanh::LeanObject,
    mut v___x_3997_: *mut leanh::LeanObject,
    mut v_a_3998_: *mut leanh::LeanObject,
    mut v_args_3999_: *mut leanh::LeanObject,
    mut v_f_4000_: *mut leanh::LeanObject,
    mut v_____x_4001_: *mut leanh::LeanObject,
    mut v_fType_4002_: *mut leanh::LeanObject,
    mut v_j_4003_: *mut leanh::LeanObject,
    mut v___y_4004_: *mut leanh::LeanObject,
    mut v___y_4005_: *mut leanh::LeanObject,
    mut v___y_4006_: *mut leanh::LeanObject,
    mut v___y_4007_: *mut leanh::LeanObject,
    mut v___y_4008_: *mut leanh::LeanObject,
    mut v___y_4009_: *mut leanh::LeanObject,
    mut v___y_4010_: *mut leanh::LeanObject,
    mut v___y_4011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4012_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_3996_, v___x_3997_, v_a_3998_, v_args_3999_, v_f_4000_, v_____x_4001_, v_fType_4002_, v_j_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
    leanh::lean_dec(v___y_4010_);
    leanh::lean_dec_ref(v___y_4009_);
    leanh::lean_dec(v___y_4008_);
    leanh::lean_dec_ref(v___y_4007_);
    leanh::lean_dec_ref(v___y_4006_);
    leanh::lean_dec(v___y_4005_);
    leanh::lean_dec_ref(v___y_4004_);
    leanh::lean_dec_ref(v_fType_4002_);
    leanh::lean_dec(v_a_3998_);
    return v_res_4012_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(
    mut v_upperBound_4015_: *mut leanh::LeanObject,
    mut v_args_4016_: *mut leanh::LeanObject,
    mut v_f_4017_: *mut leanh::LeanObject,
    mut v_a_4018_: *mut leanh::LeanObject,
    mut v_b_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
    mut v___y_4022_: *mut leanh::LeanObject,
    mut v___y_4023_: *mut leanh::LeanObject,
    mut v___y_4024_: *mut leanh::LeanObject,
    mut v___y_4025_: *mut leanh::LeanObject,
    mut v___y_4026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v_a_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v_a_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4050_: u8 = 0;
    let mut v___x_4051_: u8 = 0;
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v_fst_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_unused_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4051_ = lean_nat_dec_lt(v_a_4018_, v_upperBound_4015_);
                if v___x_4051_ == 0 {
                    leanh::lean_dec(v_a_4018_);
                    leanh::lean_dec_ref(v_f_4017_);
                    leanh::lean_dec_ref(v_args_4016_);
                    v___x_4052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4052_, 0, v_b_4019_);
                    return v___x_4052_;
                } else {
                    v_snd_4053_ = leanh::lean_ctor_get(v_b_4019_, 1);
                    v_isSharedCheck_4097_ = (!leanh::lean_is_exclusive(v_b_4019_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v_unused_4098_ = leanh::lean_ctor_get(v_b_4019_, 0);
                        leanh::lean_dec(v_unused_4098_);
                        v___x_4055_ = v_b_4019_;
                        v_isShared_4056_ = v_isSharedCheck_4097_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4053_);
                        leanh::lean_dec(v_b_4019_);
                        v___x_4055_ = leanh::lean_box(0);
                        v_isShared_4056_ = v_isSharedCheck_4097_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_4029_) == 0 {
                    v_a_4030_ = leanh::lean_ctor_get(v___y_4029_, 0);
                    v_isSharedCheck_4042_ = (!leanh::lean_is_exclusive(v___y_4029_)) as u8;
                    if v_isSharedCheck_4042_ == 0 {
                        v___x_4032_ = v___y_4029_;
                        v_isShared_4033_ = v_isSharedCheck_4042_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4030_);
                        leanh::lean_dec(v___y_4029_);
                        v___x_4032_ = leanh::lean_box(0);
                        v_isShared_4033_ = v_isSharedCheck_4042_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4018_);
                    leanh::lean_dec_ref(v_f_4017_);
                    leanh::lean_dec_ref(v_args_4016_);
                    v_a_4043_ = leanh::lean_ctor_get(v___y_4029_, 0);
                    v_isSharedCheck_4050_ = (!leanh::lean_is_exclusive(v___y_4029_)) as u8;
                    if v_isSharedCheck_4050_ == 0 {
                        v___x_4045_ = v___y_4029_;
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4043_);
                        leanh::lean_dec(v___y_4029_);
                        v___x_4045_ = leanh::lean_box(0);
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4030_) == 0 {
                    leanh::lean_dec(v_a_4018_);
                    leanh::lean_dec_ref(v_f_4017_);
                    leanh::lean_dec_ref(v_args_4016_);
                    v_a_4034_ = leanh::lean_ctor_get(v_a_4030_, 0);
                    leanh::lean_inc(v_a_4034_);
                    leanh::lean_dec_ref_known(v_a_4030_, 1);
                    if v_isShared_4033_ == 0 {
                        leanh::lean_ctor_set(v___x_4032_, 0, v_a_4034_);
                        v___x_4036_ = v___x_4032_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4037_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4034_);
                        v___x_4036_ = v_reuseFailAlloc_4037_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4032_);
                    v_a_4038_ = leanh::lean_ctor_get(v_a_4030_, 0);
                    leanh::lean_inc(v_a_4038_);
                    leanh::lean_dec_ref_known(v_a_4030_, 1);
                    v___x_4039_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4040_ = lean_nat_add(v_a_4018_, v___x_4039_);
                    leanh::lean_dec(v_a_4018_);
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
                    v_reuseFailAlloc_4049_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
                    v___x_4048_ = v_reuseFailAlloc_4049_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4048_;
            }
            6 => {
                v_fst_4057_ = leanh::lean_ctor_get(v_snd_4053_, 0);
                v_snd_4058_ = leanh::lean_ctor_get(v_snd_4053_, 1);
                v_isSharedCheck_4096_ = (!leanh::lean_is_exclusive(v_snd_4053_)) as u8;
                if v_isSharedCheck_4096_ == 0 {
                    v___x_4060_ = v_snd_4053_;
                    v_isShared_4061_ = v_isSharedCheck_4096_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4058_);
                    leanh::lean_inc(v_fst_4057_);
                    leanh::lean_dec(v_snd_4053_);
                    v___x_4060_ = leanh::lean_box(0);
                    v_isShared_4061_ = v_isSharedCheck_4096_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4062_ = l_Lean_Expr_isErased(v_fst_4057_);
                if v___x_4062_ == 0 {
                    v___x_4063_ = leanh::lean_box(0);
                    v___x_4064_ = lean_array_fget_borrowed(v_args_4016_, v_a_4018_);
                    v___x_4065_ = l_Lean_Expr_headBeta(v_fst_4057_);
                    if leanh::lean_obj_tag(v___x_4065_) == 7 {
                        leanh::lean_del_object(v___x_4055_);
                        v_binderType_4066_ = leanh::lean_ctor_get(v___x_4065_, 1);
                        leanh::lean_inc_ref(v_binderType_4066_);
                        v_body_4067_ = leanh::lean_ctor_get(v___x_4065_, 2);
                        leanh::lean_inc_ref(v_body_4067_);
                        if v_isShared_4061_ == 0 {
                            leanh::lean_ctor_set(v___x_4060_, 1, v_body_4067_);
                            leanh::lean_ctor_set(v___x_4060_, 0, v_binderType_4066_);
                            v___x_4069_ = v___x_4060_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4071_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4071_,
                                0,
                                v_binderType_4066_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_body_4067_);
                            v___x_4069_ = v_reuseFailAlloc_4071_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_inc_ref(v_args_4016_);
                        v___x_4072_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(
                            v___x_4065_,
                            v_snd_4058_,
                            v_a_4018_,
                            v_args_4016_,
                        );
                        leanh::lean_dec_ref(v___x_4065_);
                        v___x_4073_ = l_Lean_Expr_headBeta(v___x_4072_);
                        if leanh::lean_obj_tag(v___x_4073_) == 7 {
                            leanh::lean_dec(v_snd_4058_);
                            leanh::lean_del_object(v___x_4055_);
                            v_binderType_4074_ = leanh::lean_ctor_get(v___x_4073_, 1);
                            leanh::lean_inc_ref(v_binderType_4074_);
                            v_body_4075_ = leanh::lean_ctor_get(v___x_4073_, 2);
                            leanh::lean_inc_ref(v_body_4075_);
                            if v_isShared_4061_ == 0 {
                                leanh::lean_ctor_set(v___x_4060_, 1, v_body_4075_);
                                leanh::lean_ctor_set(v___x_4060_, 0, v_binderType_4074_);
                                v___x_4077_ = v___x_4060_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_4079_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4079_,
                                    0,
                                    v_binderType_4074_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4079_,
                                    1,
                                    v_body_4075_,
                                );
                                v___x_4077_ = v_reuseFailAlloc_4079_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4018_);
                            leanh::lean_dec_ref(v_f_4017_);
                            leanh::lean_dec_ref(v_args_4016_);
                            v___x_4080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0;
                            if v_isShared_4061_ == 0 {
                                leanh::lean_ctor_set(v___x_4060_, 0, v___x_4073_);
                                v___x_4082_ = v___x_4060_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4087_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4073_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_snd_4058_);
                                v___x_4082_ = v_reuseFailAlloc_4087_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4018_);
                    leanh::lean_dec_ref(v_f_4017_);
                    leanh::lean_dec_ref(v_args_4016_);
                    v___x_4088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0;
                    if v_isShared_4061_ == 0 {
                        v___x_4090_ = v___x_4060_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4095_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_fst_4057_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_snd_4058_);
                        v___x_4090_ = v_reuseFailAlloc_4095_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                leanh::lean_inc_ref(v_f_4017_);
                leanh::lean_inc_ref(v_args_4016_);
                leanh::lean_inc(v___x_4064_);
                v___x_4070_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_4063_, v___x_4064_, v_a_4018_, v_args_4016_, v_f_4017_, v___x_4069_, v___x_4065_, v_snd_4058_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
                leanh::lean_dec_ref_known(v___x_4065_, 3);
                v___y_4029_ = v___x_4070_;
                state = 1;
                continue;
            }
            9 => {
                leanh::lean_inc_ref(v_f_4017_);
                leanh::lean_inc_ref(v_args_4016_);
                leanh::lean_inc(v_a_4018_);
                leanh::lean_inc(v___x_4064_);
                v___x_4078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_4063_, v___x_4064_, v_a_4018_, v_args_4016_, v_f_4017_, v___x_4077_, v___x_4073_, v_a_4018_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
                leanh::lean_dec_ref_known(v___x_4073_, 3);
                v___y_4029_ = v___x_4078_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_4056_ == 0 {
                    leanh::lean_ctor_set(v___x_4055_, 1, v___x_4082_);
                    leanh::lean_ctor_set(v___x_4055_, 0, v___x_4080_);
                    v___x_4084_ = v___x_4055_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4082_);
                    v___x_4084_ = v_reuseFailAlloc_4086_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4085_, 0, v___x_4084_);
                return v___x_4085_;
            }
            12 => {
                if v_isShared_4056_ == 0 {
                    leanh::lean_ctor_set(v___x_4055_, 1, v___x_4090_);
                    leanh::lean_ctor_set(v___x_4055_, 0, v___x_4088_);
                    v___x_4092_ = v___x_4055_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4090_);
                    v___x_4092_ = v_reuseFailAlloc_4094_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4093_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4093_, 0, v___x_4092_);
                return v___x_4093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___boxed(
    mut v_upperBound_4099_: *mut leanh::LeanObject,
    mut v_args_4100_: *mut leanh::LeanObject,
    mut v_f_4101_: *mut leanh::LeanObject,
    mut v_a_4102_: *mut leanh::LeanObject,
    mut v_b_4103_: *mut leanh::LeanObject,
    mut v___y_4104_: *mut leanh::LeanObject,
    mut v___y_4105_: *mut leanh::LeanObject,
    mut v___y_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
    mut v___y_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v_upperBound_4099_, v_args_4100_, v_f_4101_, v_a_4102_, v_b_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    leanh::lean_dec(v___y_4110_);
    leanh::lean_dec_ref(v___y_4109_);
    leanh::lean_dec(v___y_4108_);
    leanh::lean_dec_ref(v___y_4107_);
    leanh::lean_dec_ref(v___y_4106_);
    leanh::lean_dec(v___y_4105_);
    leanh::lean_dec_ref(v___y_4104_);
    leanh::lean_dec(v_upperBound_4099_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(
    mut v_f_4113_: *mut leanh::LeanObject,
    mut v_args_4114_: *mut leanh::LeanObject,
    mut v_a_4115_: *mut leanh::LeanObject,
    mut v_a_4116_: *mut leanh::LeanObject,
    mut v_a_4117_: *mut leanh::LeanObject,
    mut v_a_4118_: *mut leanh::LeanObject,
    mut v_a_4119_: *mut leanh::LeanObject,
    mut v_a_4120_: *mut leanh::LeanObject,
    mut v_a_4121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4134_: u8 = 0;
    let mut v_fst_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4144_: u8 = 0;
    let mut v_a_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4152_: u8 = 0;
    let mut v_a_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4156_: u8 = 0;
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_f_4113_);
                v___x_4123_ = l_Lean_Compiler_LCNF_inferType(
                    v_f_4113_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_,
                );
                if leanh::lean_obj_tag(v___x_4123_) == 0 {
                    v_a_4124_ = leanh::lean_ctor_get(v___x_4123_, 0);
                    leanh::lean_inc(v_a_4124_);
                    leanh::lean_dec_ref_known(v___x_4123_, 1);
                    v___x_4125_ = lean_array_get_size(v_args_4114_);
                    v___x_4126_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4127_ = leanh::lean_box(0);
                    v___x_4128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4128_, 0, v_a_4124_);
                    leanh::lean_ctor_set(v___x_4128_, 1, v___x_4126_);
                    v___x_4129_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4129_, 0, v___x_4127_);
                    leanh::lean_ctor_set(v___x_4129_, 1, v___x_4128_);
                    v___x_4130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v___x_4125_, v_args_4114_, v_f_4113_, v___x_4126_, v___x_4129_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
                    if leanh::lean_obj_tag(v___x_4130_) == 0 {
                        v_a_4131_ = leanh::lean_ctor_get(v___x_4130_, 0);
                        v_isSharedCheck_4144_ =
                            (!leanh::lean_is_exclusive(v___x_4130_)) as u8;
                        if v_isSharedCheck_4144_ == 0 {
                            v___x_4133_ = v___x_4130_;
                            v_isShared_4134_ = v_isSharedCheck_4144_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4131_);
                            leanh::lean_dec(v___x_4130_);
                            v___x_4133_ = leanh::lean_box(0);
                            v_isShared_4134_ = v_isSharedCheck_4144_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4145_ = leanh::lean_ctor_get(v___x_4130_, 0);
                        v_isSharedCheck_4152_ =
                            (!leanh::lean_is_exclusive(v___x_4130_)) as u8;
                        if v_isSharedCheck_4152_ == 0 {
                            v___x_4147_ = v___x_4130_;
                            v_isShared_4148_ = v_isSharedCheck_4152_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4145_);
                            leanh::lean_dec(v___x_4130_);
                            v___x_4147_ = leanh::lean_box(0);
                            v_isShared_4148_ = v_isSharedCheck_4152_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_args_4114_);
                    leanh::lean_dec_ref(v_f_4113_);
                    v_a_4153_ = leanh::lean_ctor_get(v___x_4123_, 0);
                    v_isSharedCheck_4160_ = (!leanh::lean_is_exclusive(v___x_4123_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4155_ = v___x_4123_;
                        v_isShared_4156_ = v_isSharedCheck_4160_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4153_);
                        leanh::lean_dec(v___x_4123_);
                        v___x_4155_ = leanh::lean_box(0);
                        v_isShared_4156_ = v_isSharedCheck_4160_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4135_ = leanh::lean_ctor_get(v_a_4131_, 0);
                leanh::lean_inc(v_fst_4135_);
                leanh::lean_dec(v_a_4131_);
                if leanh::lean_obj_tag(v_fst_4135_) == 0 {
                    v___x_4136_ = leanh::lean_box(0);
                    if v_isShared_4134_ == 0 {
                        leanh::lean_ctor_set(v___x_4133_, 0, v___x_4136_);
                        v___x_4138_ = v___x_4133_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4139_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
                        v___x_4138_ = v_reuseFailAlloc_4139_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_4140_ = leanh::lean_ctor_get(v_fst_4135_, 0);
                    leanh::lean_inc(v_val_4140_);
                    leanh::lean_dec_ref_known(v_fst_4135_, 1);
                    if v_isShared_4134_ == 0 {
                        leanh::lean_ctor_set(v___x_4133_, 0, v_val_4140_);
                        v___x_4142_ = v___x_4133_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4143_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_val_4140_);
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
                    v_reuseFailAlloc_4151_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
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
                    v_reuseFailAlloc_4159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
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
    mut v_f_4161_: *mut leanh::LeanObject,
    mut v_args_4162_: *mut leanh::LeanObject,
    mut v_a_4163_: *mut leanh::LeanObject,
    mut v_a_4164_: *mut leanh::LeanObject,
    mut v_a_4165_: *mut leanh::LeanObject,
    mut v_a_4166_: *mut leanh::LeanObject,
    mut v_a_4167_: *mut leanh::LeanObject,
    mut v_a_4168_: *mut leanh::LeanObject,
    mut v_a_4169_: *mut leanh::LeanObject,
    mut v_a_4170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4169_);
    leanh::lean_dec_ref(v_a_4168_);
    leanh::lean_dec(v_a_4167_);
    leanh::lean_dec_ref(v_a_4166_);
    leanh::lean_dec_ref(v_a_4165_);
    leanh::lean_dec(v_a_4164_);
    leanh::lean_dec_ref(v_a_4163_);
    return v_res_4171_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1(
    mut v_upperBound_4172_: *mut leanh::LeanObject,
    mut v_args_4173_: *mut leanh::LeanObject,
    mut v_f_4174_: *mut leanh::LeanObject,
    mut v_inst_4175_: *mut leanh::LeanObject,
    mut v_R_4176_: *mut leanh::LeanObject,
    mut v_a_4177_: *mut leanh::LeanObject,
    mut v_b_4178_: *mut leanh::LeanObject,
    mut v_c_4179_: *mut leanh::LeanObject,
    mut v___y_4180_: *mut leanh::LeanObject,
    mut v___y_4181_: *mut leanh::LeanObject,
    mut v___y_4182_: *mut leanh::LeanObject,
    mut v___y_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
    mut v___y_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v_upperBound_4172_, v_args_4173_, v_f_4174_, v_a_4177_, v_b_4178_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
    return v___x_4188_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___boxed(
    mut v_upperBound_4189_: *mut leanh::LeanObject,
    mut v_args_4190_: *mut leanh::LeanObject,
    mut v_f_4191_: *mut leanh::LeanObject,
    mut v_inst_4192_: *mut leanh::LeanObject,
    mut v_R_4193_: *mut leanh::LeanObject,
    mut v_a_4194_: *mut leanh::LeanObject,
    mut v_b_4195_: *mut leanh::LeanObject,
    mut v_c_4196_: *mut leanh::LeanObject,
    mut v___y_4197_: *mut leanh::LeanObject,
    mut v___y_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4203_);
    leanh::lean_dec_ref(v___y_4202_);
    leanh::lean_dec(v___y_4201_);
    leanh::lean_dec_ref(v___y_4200_);
    leanh::lean_dec_ref(v___y_4199_);
    leanh::lean_dec(v___y_4198_);
    leanh::lean_dec_ref(v___y_4197_);
    leanh::lean_dec(v_upperBound_4189_);
    return v_res_4205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(
    mut v_e_4206_: *mut leanh::LeanObject,
    mut v_a_4207_: *mut leanh::LeanObject,
    mut v_a_4208_: *mut leanh::LeanObject,
    mut v_a_4209_: *mut leanh::LeanObject,
    mut v_a_4210_: *mut leanh::LeanObject,
    mut v_a_4211_: *mut leanh::LeanObject,
    mut v_a_4212_: *mut leanh::LeanObject,
    mut v_a_4213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4222_: u8 = 0;
    let mut v_unused_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_4206_) {
                0 => {
                    v_isSharedCheck_4222_ = (!leanh::lean_is_exclusive(v_e_4206_)) as u8;
                    if v_isSharedCheck_4222_ == 0 {
                        v_unused_4223_ = leanh::lean_ctor_get(v_e_4206_, 0);
                        leanh::lean_dec(v_unused_4223_);
                        v___x_4216_ = v_e_4206_;
                        v_isShared_4217_ = v_isSharedCheck_4222_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_e_4206_);
                        v___x_4216_ = leanh::lean_box(0);
                        v_isShared_4217_ = v_isSharedCheck_4222_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4224_ = leanh::lean_box(0);
                    v___x_4225_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4225_, 0, v___x_4224_);
                    return v___x_4225_;
                }
                2 => {
                    v_struct_4226_ = leanh::lean_ctor_get(v_e_4206_, 2);
                    leanh::lean_inc(v_struct_4226_);
                    leanh::lean_dec_ref_known(v_e_4206_, 3);
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
                    v_declName_4228_ = leanh::lean_ctor_get(v_e_4206_, 0);
                    leanh::lean_inc(v_declName_4228_);
                    v_us_4229_ = leanh::lean_ctor_get(v_e_4206_, 1);
                    leanh::lean_inc(v_us_4229_);
                    v_args_4230_ = leanh::lean_ctor_get(v_e_4206_, 2);
                    leanh::lean_inc_ref(v_args_4230_);
                    leanh::lean_dec_ref_known(v_e_4206_, 3);
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
                    v_fvarId_4233_ = leanh::lean_ctor_get(v_e_4206_, 0);
                    leanh::lean_inc_n(v_fvarId_4233_, 2);
                    v_args_4234_ = leanh::lean_ctor_get(v_e_4206_, 1);
                    leanh::lean_inc_ref(v_args_4234_);
                    leanh::lean_dec_ref_known(v_e_4206_, 2);
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
                    if leanh::lean_obj_tag(v___x_4235_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4235_, 1);
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
                        leanh::lean_dec_ref(v_args_4234_);
                        leanh::lean_dec(v_fvarId_4233_);
                        return v___x_4235_;
                    }
                }
            },
            1 => {
                v___x_4218_ = leanh::lean_box(0);
                if v_isShared_4217_ == 0 {
                    leanh::lean_ctor_set(v___x_4216_, 0, v___x_4218_);
                    v___x_4220_ = v___x_4216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4218_);
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
    mut v_e_4238_: *mut leanh::LeanObject,
    mut v_a_4239_: *mut leanh::LeanObject,
    mut v_a_4240_: *mut leanh::LeanObject,
    mut v_a_4241_: *mut leanh::LeanObject,
    mut v_a_4242_: *mut leanh::LeanObject,
    mut v_a_4243_: *mut leanh::LeanObject,
    mut v_a_4244_: *mut leanh::LeanObject,
    mut v_a_4245_: *mut leanh::LeanObject,
    mut v_a_4246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4247_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(
        v_e_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_,
    );
    leanh::lean_dec(v_a_4245_);
    leanh::lean_dec_ref(v_a_4244_);
    leanh::lean_dec(v_a_4243_);
    leanh::lean_dec_ref(v_a_4242_);
    leanh::lean_dec_ref(v_a_4241_);
    leanh::lean_dec(v_a_4240_);
    leanh::lean_dec_ref(v_a_4239_);
    return v_res_4247_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4249_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0;
    v___x_4250_ = l_Lean_stringToMessageData(v___x_4249_);
    return v___x_4250_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
    mut v_jp_4251_: *mut leanh::LeanObject,
    mut v_a_4252_: *mut leanh::LeanObject,
    mut v_a_4253_: *mut leanh::LeanObject,
    mut v_a_4254_: *mut leanh::LeanObject,
    mut v_a_4255_: *mut leanh::LeanObject,
    mut v_a_4256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_jps_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: u8 = 0;
    v_jps_4258_ = leanh::lean_ctor_get(v_a_4252_, 0);
    v___x_4259_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_jp_4251_, v_jps_4258_);
    if v___x_4259_ == 0 {
        let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4260_ = leanh::lean_obj_once(
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
        v___x_4263_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4263_, 0, v___x_4260_);
        leanh::lean_ctor_set(v___x_4263_, 1, v___x_4262_);
        v___x_4264_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
        v___x_4265_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4265_, 0, v___x_4263_);
        leanh::lean_ctor_set(v___x_4265_, 1, v___x_4264_);
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
        let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_jp_4251_);
        v___x_4267_ = leanh::lean_box(0);
        v___x_4268_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4268_, 0, v___x_4267_);
        return v___x_4268_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___boxed(
    mut v_jp_4269_: *mut leanh::LeanObject,
    mut v_a_4270_: *mut leanh::LeanObject,
    mut v_a_4271_: *mut leanh::LeanObject,
    mut v_a_4272_: *mut leanh::LeanObject,
    mut v_a_4273_: *mut leanh::LeanObject,
    mut v_a_4274_: *mut leanh::LeanObject,
    mut v_a_4275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4276_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
        v_jp_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_,
    );
    leanh::lean_dec(v_a_4274_);
    leanh::lean_dec_ref(v_a_4273_);
    leanh::lean_dec(v_a_4272_);
    leanh::lean_dec_ref(v_a_4271_);
    leanh::lean_dec_ref(v_a_4270_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(
    mut v_jp_4277_: *mut leanh::LeanObject,
    mut v_a_4278_: *mut leanh::LeanObject,
    mut v_a_4279_: *mut leanh::LeanObject,
    mut v_a_4280_: *mut leanh::LeanObject,
    mut v_a_4281_: *mut leanh::LeanObject,
    mut v_a_4282_: *mut leanh::LeanObject,
    mut v_a_4283_: *mut leanh::LeanObject,
    mut v_a_4284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
        v_jp_4277_, v_a_4278_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_,
    );
    return v___x_4286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___boxed(
    mut v_jp_4287_: *mut leanh::LeanObject,
    mut v_a_4288_: *mut leanh::LeanObject,
    mut v_a_4289_: *mut leanh::LeanObject,
    mut v_a_4290_: *mut leanh::LeanObject,
    mut v_a_4291_: *mut leanh::LeanObject,
    mut v_a_4292_: *mut leanh::LeanObject,
    mut v_a_4293_: *mut leanh::LeanObject,
    mut v_a_4294_: *mut leanh::LeanObject,
    mut v_a_4295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4296_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(
        v_jp_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_,
    );
    leanh::lean_dec(v_a_4294_);
    leanh::lean_dec_ref(v_a_4293_);
    leanh::lean_dec(v_a_4292_);
    leanh::lean_dec_ref(v_a_4291_);
    leanh::lean_dec_ref(v_a_4290_);
    leanh::lean_dec(v_a_4289_);
    leanh::lean_dec_ref(v_a_4288_);
    return v_res_4296_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4298_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0;
    v___x_4299_ = l_Lean_stringToMessageData(v___x_4298_);
    return v___x_4299_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4301_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2;
    v___x_4302_ = l_Lean_stringToMessageData(v___x_4301_);
    return v___x_4302_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
    mut v_param_4303_: *mut leanh::LeanObject,
    mut v_a_4304_: *mut leanh::LeanObject,
    mut v_a_4305_: *mut leanh::LeanObject,
    mut v_a_4306_: *mut leanh::LeanObject,
    mut v_a_4307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4317_: u8 = 0;
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4309_ = leanh::lean_ctor_get(v_param_4303_, 0);
                v_binderName_4310_ = leanh::lean_ctor_get(v_param_4303_, 1);
                leanh::lean_inc(v_binderName_4310_);
                v___x_4311_ = 0;
                leanh::lean_inc(v_fvarId_4309_);
                v___x_4312_ = l_Lean_Compiler_LCNF_getParam(
                    v___x_4311_,
                    v_fvarId_4309_,
                    v_a_4304_,
                    v_a_4305_,
                    v_a_4306_,
                    v_a_4307_,
                );
                if leanh::lean_obj_tag(v___x_4312_) == 0 {
                    v_a_4313_ = leanh::lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4328_ = (!leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4315_ = v___x_4312_;
                        v_isShared_4316_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4313_);
                        leanh::lean_dec(v___x_4312_);
                        v___x_4315_ = leanh::lean_box(0);
                        v_isShared_4316_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_binderName_4310_);
                    leanh::lean_dec_ref(v_param_4303_);
                    v_a_4329_ = leanh::lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4336_ = (!leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4331_ = v___x_4312_;
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4329_);
                        leanh::lean_dec(v___x_4312_);
                        v___x_4331_ = leanh::lean_box(0);
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4317_ =
                    l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(v_param_4303_, v_a_4313_);
                leanh::lean_dec(v_a_4313_);
                leanh::lean_dec_ref(v_param_4303_);
                if v___x_4317_ == 0 {
                    leanh::lean_del_object(v___x_4315_);
                    v___x_4318_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1,
                    );
                    v___x_4319_ = l_Lean_MessageData_ofName(v_binderName_4310_);
                    v___x_4320_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4318_);
                    leanh::lean_ctor_set(v___x_4320_, 1, v___x_4319_);
                    v___x_4321_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3,
                    );
                    v___x_4322_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4322_, 0, v___x_4320_);
                    leanh::lean_ctor_set(v___x_4322_, 1, v___x_4321_);
                    v___x_4323_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4322_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_);
                    return v___x_4323_;
                } else {
                    leanh::lean_dec(v_binderName_4310_);
                    v___x_4324_ = leanh::lean_box(0);
                    if v_isShared_4316_ == 0 {
                        leanh::lean_ctor_set(v___x_4315_, 0, v___x_4324_);
                        v___x_4326_ = v___x_4315_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
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
                    v_reuseFailAlloc_4335_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
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
    mut v_param_4337_: *mut leanh::LeanObject,
    mut v_a_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
    mut v_a_4340_: *mut leanh::LeanObject,
    mut v_a_4341_: *mut leanh::LeanObject,
    mut v_a_4342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4343_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
        v_param_4337_,
        v_a_4338_,
        v_a_4339_,
        v_a_4340_,
        v_a_4341_,
    );
    leanh::lean_dec(v_a_4341_);
    leanh::lean_dec_ref(v_a_4340_);
    leanh::lean_dec(v_a_4339_);
    leanh::lean_dec_ref(v_a_4338_);
    return v_res_4343_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParam(
    mut v_param_4344_: *mut leanh::LeanObject,
    mut v_a_4345_: *mut leanh::LeanObject,
    mut v_a_4346_: *mut leanh::LeanObject,
    mut v_a_4347_: *mut leanh::LeanObject,
    mut v_a_4348_: *mut leanh::LeanObject,
    mut v_a_4349_: *mut leanh::LeanObject,
    mut v_a_4350_: *mut leanh::LeanObject,
    mut v_a_4351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_param_4354_: *mut leanh::LeanObject,
    mut v_a_4355_: *mut leanh::LeanObject,
    mut v_a_4356_: *mut leanh::LeanObject,
    mut v_a_4357_: *mut leanh::LeanObject,
    mut v_a_4358_: *mut leanh::LeanObject,
    mut v_a_4359_: *mut leanh::LeanObject,
    mut v_a_4360_: *mut leanh::LeanObject,
    mut v_a_4361_: *mut leanh::LeanObject,
    mut v_a_4362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4361_);
    leanh::lean_dec_ref(v_a_4360_);
    leanh::lean_dec(v_a_4359_);
    leanh::lean_dec_ref(v_a_4358_);
    leanh::lean_dec_ref(v_a_4357_);
    leanh::lean_dec(v_a_4356_);
    leanh::lean_dec_ref(v_a_4355_);
    return v_res_4363_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(
    mut v_as_4364_: *mut leanh::LeanObject,
    mut v_i_4365_: usize,
    mut v_stop_4366_: usize,
    mut v_b_4367_: *mut leanh::LeanObject,
    mut v___y_4368_: *mut leanh::LeanObject,
    mut v___y_4369_: *mut leanh::LeanObject,
    mut v___y_4370_: *mut leanh::LeanObject,
    mut v___y_4371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: usize = 0;
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4373_ = lean_usize_dec_eq(v_i_4365_, v_stop_4366_);
                if v___x_4373_ == 0 {
                    v___x_4374_ = lean_array_uget_borrowed(v_as_4364_, v_i_4365_);
                    leanh::lean_inc(v___x_4374_);
                    v___x_4375_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
                        v___x_4374_,
                        v___y_4368_,
                        v___y_4369_,
                        v___y_4370_,
                        v___y_4371_,
                    );
                    if leanh::lean_obj_tag(v___x_4375_) == 0 {
                        v_a_4376_ = leanh::lean_ctor_get(v___x_4375_, 0);
                        leanh::lean_inc(v_a_4376_);
                        leanh::lean_dec_ref_known(v___x_4375_, 1);
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
                    v___x_4380_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4380_, 0, v_b_4367_);
                    return v___x_4380_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg___boxed(
    mut v_as_4381_: *mut leanh::LeanObject,
    mut v_i_4382_: *mut leanh::LeanObject,
    mut v_stop_4383_: *mut leanh::LeanObject,
    mut v_b_4384_: *mut leanh::LeanObject,
    mut v___y_4385_: *mut leanh::LeanObject,
    mut v___y_4386_: *mut leanh::LeanObject,
    mut v___y_4387_: *mut leanh::LeanObject,
    mut v___y_4388_: *mut leanh::LeanObject,
    mut v___y_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4390_: usize = 0;
    let mut v_stop_boxed_4391_: usize = 0;
    let mut v_res_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4390_ = leanh::lean_unbox_usize(v_i_4382_);
    leanh::lean_dec(v_i_4382_);
    v_stop_boxed_4391_ = leanh::lean_unbox_usize(v_stop_4383_);
    leanh::lean_dec(v_stop_4383_);
    v_res_4392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_as_4381_, v_i_boxed_4390_, v_stop_boxed_4391_, v_b_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
    leanh::lean_dec(v___y_4388_);
    leanh::lean_dec_ref(v___y_4387_);
    leanh::lean_dec(v___y_4386_);
    leanh::lean_dec_ref(v___y_4385_);
    leanh::lean_dec_ref(v_as_4381_);
    return v_res_4392_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParams(
    mut v_params_4393_: *mut leanh::LeanObject,
    mut v_a_4394_: *mut leanh::LeanObject,
    mut v_a_4395_: *mut leanh::LeanObject,
    mut v_a_4396_: *mut leanh::LeanObject,
    mut v_a_4397_: *mut leanh::LeanObject,
    mut v_a_4398_: *mut leanh::LeanObject,
    mut v_a_4399_: *mut leanh::LeanObject,
    mut v_a_4400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: u8 = 0;
    v___x_4402_ = leanh::lean_unsigned_to_nat(0);
    v___x_4403_ = lean_array_get_size(v_params_4393_);
    v___x_4404_ = leanh::lean_box(0);
    v___x_4405_ = lean_nat_dec_lt(v___x_4402_, v___x_4403_);
    if v___x_4405_ == 0 {
        let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4406_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4406_, 0, v___x_4404_);
        return v___x_4406_;
    } else {
        let mut v___x_4407_: u8 = 0;
        v___x_4407_ = lean_nat_dec_le(v___x_4403_, v___x_4403_);
        if v___x_4407_ == 0 {
            if v___x_4405_ == 0 {
                let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4408_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4408_, 0, v___x_4404_);
                return v___x_4408_;
            } else {
                let mut v___x_4409_: usize = 0;
                let mut v___x_4410_: usize = 0;
                let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4409_ = 0usize;
                v___x_4410_ = lean_usize_of_nat(v___x_4403_);
                v___x_4411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_params_4393_, v___x_4409_, v___x_4410_, v___x_4404_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
                return v___x_4411_;
            }
        } else {
            let mut v___x_4412_: usize = 0;
            let mut v___x_4413_: usize = 0;
            let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4412_ = 0usize;
            v___x_4413_ = lean_usize_of_nat(v___x_4403_);
            v___x_4414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_params_4393_, v___x_4412_, v___x_4413_, v___x_4404_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
            return v___x_4414_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParams___boxed(
    mut v_params_4415_: *mut leanh::LeanObject,
    mut v_a_4416_: *mut leanh::LeanObject,
    mut v_a_4417_: *mut leanh::LeanObject,
    mut v_a_4418_: *mut leanh::LeanObject,
    mut v_a_4419_: *mut leanh::LeanObject,
    mut v_a_4420_: *mut leanh::LeanObject,
    mut v_a_4421_: *mut leanh::LeanObject,
    mut v_a_4422_: *mut leanh::LeanObject,
    mut v_a_4423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4422_);
    leanh::lean_dec_ref(v_a_4421_);
    leanh::lean_dec(v_a_4420_);
    leanh::lean_dec_ref(v_a_4419_);
    leanh::lean_dec_ref(v_a_4418_);
    leanh::lean_dec(v_a_4417_);
    leanh::lean_dec_ref(v_a_4416_);
    leanh::lean_dec_ref(v_params_4415_);
    return v_res_4424_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(
    mut v_as_4425_: *mut leanh::LeanObject,
    mut v_i_4426_: usize,
    mut v_stop_4427_: usize,
    mut v_b_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
    mut v___y_4435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_as_4425_, v_i_4426_, v_stop_4427_, v_b_4428_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
    return v___x_4437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___boxed(
    mut v_as_4438_: *mut leanh::LeanObject,
    mut v_i_4439_: *mut leanh::LeanObject,
    mut v_stop_4440_: *mut leanh::LeanObject,
    mut v_b_4441_: *mut leanh::LeanObject,
    mut v___y_4442_: *mut leanh::LeanObject,
    mut v___y_4443_: *mut leanh::LeanObject,
    mut v___y_4444_: *mut leanh::LeanObject,
    mut v___y_4445_: *mut leanh::LeanObject,
    mut v___y_4446_: *mut leanh::LeanObject,
    mut v___y_4447_: *mut leanh::LeanObject,
    mut v___y_4448_: *mut leanh::LeanObject,
    mut v___y_4449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4450_: usize = 0;
    let mut v_stop_boxed_4451_: usize = 0;
    let mut v_res_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4450_ = leanh::lean_unbox_usize(v_i_4439_);
    leanh::lean_dec(v_i_4439_);
    v_stop_boxed_4451_ = leanh::lean_unbox_usize(v_stop_4440_);
    leanh::lean_dec(v_stop_4440_);
    v_res_4452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(v_as_4438_, v_i_boxed_4450_, v_stop_boxed_4451_, v_b_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
    leanh::lean_dec(v___y_4448_);
    leanh::lean_dec_ref(v___y_4447_);
    leanh::lean_dec(v___y_4446_);
    leanh::lean_dec_ref(v___y_4445_);
    leanh::lean_dec_ref(v___y_4444_);
    leanh::lean_dec(v___y_4443_);
    leanh::lean_dec_ref(v___y_4442_);
    leanh::lean_dec_ref(v_as_4438_);
    return v_res_4452_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4454_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0;
    v___x_4455_ = l_Lean_stringToMessageData(v___x_4454_);
    return v___x_4455_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4457_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2;
    v___x_4458_ = l_Lean_stringToMessageData(v___x_4457_);
    return v___x_4458_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4;
    v___x_4461_ = l_Lean_stringToMessageData(v___x_4460_);
    return v___x_4461_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6;
    v___x_4464_ = l_Lean_stringToMessageData(v___x_4463_);
    return v___x_4464_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(
    mut v_letDecl_4465_: *mut leanh::LeanObject,
    mut v_a_4466_: *mut leanh::LeanObject,
    mut v_a_4467_: *mut leanh::LeanObject,
    mut v_a_4468_: *mut leanh::LeanObject,
    mut v_a_4469_: *mut leanh::LeanObject,
    mut v_a_4470_: *mut leanh::LeanObject,
    mut v_a_4471_: *mut leanh::LeanObject,
    mut v_a_4472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4488_: u8 = 0;
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut v_a_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4504_: u8 = 0;
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4508_: u8 = 0;
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u8 = 0;
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: u8 = 0;
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_a_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4542_: u8 = 0;
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v_a_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4550_: u8 = 0;
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4474_ = leanh::lean_ctor_get(v_letDecl_4465_, 0);
                v_binderName_4475_ = leanh::lean_ctor_get(v_letDecl_4465_, 1);
                leanh::lean_inc(v_binderName_4475_);
                v_type_4476_ = leanh::lean_ctor_get(v_letDecl_4465_, 2);
                v_value_4477_ = leanh::lean_ctor_get(v_letDecl_4465_, 3);
                leanh::lean_inc(v_value_4477_);
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
                if leanh::lean_obj_tag(v___x_4509_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4509_, 1);
                    v___x_4510_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_4469_);
                    if leanh::lean_obj_tag(v___x_4510_) == 0 {
                        v_a_4511_ = leanh::lean_ctor_get(v___x_4510_, 0);
                        leanh::lean_inc(v_a_4511_);
                        leanh::lean_dec_ref_known(v___x_4510_, 1);
                        v___x_4512_ = (leanh::lean_unbox(v_a_4511_) as u8);
                        leanh::lean_dec(v_a_4511_);
                        if v___x_4512_ == 0 {
                            v___y_4479_ = v_a_4469_;
                            v___y_4480_ = v_a_4470_;
                            v___y_4481_ = v_a_4471_;
                            v___y_4482_ = v_a_4472_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4513_ = 0;
                            leanh::lean_inc(v_value_4477_);
                            v___x_4514_ = l_Lean_Compiler_LCNF_LetValue_inferType(
                                v___x_4513_,
                                v_value_4477_,
                                v_a_4469_,
                                v_a_4470_,
                                v_a_4471_,
                                v_a_4472_,
                            );
                            if leanh::lean_obj_tag(v___x_4514_) == 0 {
                                v_a_4515_ = leanh::lean_ctor_get(v___x_4514_, 0);
                                leanh::lean_inc_n(v_a_4515_, 2);
                                leanh::lean_dec_ref_known(v___x_4514_, 1);
                                leanh::lean_inc_ref(v_type_4476_);
                                v___x_4516_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                    v_type_4476_,
                                    v_a_4515_,
                                    v_a_4468_,
                                    v_a_4469_,
                                    v_a_4470_,
                                    v_a_4471_,
                                    v_a_4472_,
                                );
                                if leanh::lean_obj_tag(v___x_4516_) == 0 {
                                    v_a_4517_ = leanh::lean_ctor_get(v___x_4516_, 0);
                                    leanh::lean_inc(v_a_4517_);
                                    leanh::lean_dec_ref_known(v___x_4516_, 1);
                                    v___x_4518_ = (leanh::lean_unbox(v_a_4517_) as u8);
                                    leanh::lean_dec(v_a_4517_);
                                    if v___x_4518_ == 0 {
                                        leanh::lean_inc_ref(v_type_4476_);
                                        leanh::lean_dec_ref(v_letDecl_4465_);
                                        v___x_4519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once), _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5);
                                        v___x_4520_ = l_Lean_MessageData_ofName(v_binderName_4475_);
                                        v___x_4521_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4521_, 0, v___x_4519_);
                                        leanh::lean_ctor_set(v___x_4521_, 1, v___x_4520_);
                                        v___x_4522_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once), _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7);
                                        v___x_4523_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4523_, 0, v___x_4521_);
                                        leanh::lean_ctor_set(v___x_4523_, 1, v___x_4522_);
                                        v___x_4524_ = l_Lean_indentExpr(v_a_4515_);
                                        v___x_4525_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4525_, 0, v___x_4523_);
                                        leanh::lean_ctor_set(v___x_4525_, 1, v___x_4524_);
                                        v___x_4526_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                                        v___x_4527_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4527_, 0, v___x_4525_);
                                        leanh::lean_ctor_set(v___x_4527_, 1, v___x_4526_);
                                        v___x_4528_ = l_Lean_indentExpr(v_type_4476_);
                                        v___x_4529_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4529_, 0, v___x_4527_);
                                        leanh::lean_ctor_set(v___x_4529_, 1, v___x_4528_);
                                        v___x_4530_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4529_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
                                        return v___x_4530_;
                                    } else {
                                        leanh::lean_dec(v_a_4515_);
                                        v___y_4479_ = v_a_4469_;
                                        v___y_4480_ = v_a_4470_;
                                        v___y_4481_ = v_a_4471_;
                                        v___y_4482_ = v_a_4472_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_4515_);
                                    leanh::lean_dec(v_binderName_4475_);
                                    leanh::lean_dec_ref(v_letDecl_4465_);
                                    v_a_4531_ = leanh::lean_ctor_get(v___x_4516_, 0);
                                    v_isSharedCheck_4538_ =
                                        (!leanh::lean_is_exclusive(v___x_4516_)) as u8;
                                    if v_isSharedCheck_4538_ == 0 {
                                        v___x_4533_ = v___x_4516_;
                                        v_isShared_4534_ = v_isSharedCheck_4538_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4531_);
                                        leanh::lean_dec(v___x_4516_);
                                        v___x_4533_ = leanh::lean_box(0);
                                        v_isShared_4534_ = v_isSharedCheck_4538_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_binderName_4475_);
                                leanh::lean_dec_ref(v_letDecl_4465_);
                                v_a_4539_ = leanh::lean_ctor_get(v___x_4514_, 0);
                                v_isSharedCheck_4546_ =
                                    (!leanh::lean_is_exclusive(v___x_4514_)) as u8;
                                if v_isSharedCheck_4546_ == 0 {
                                    v___x_4541_ = v___x_4514_;
                                    v_isShared_4542_ = v_isSharedCheck_4546_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4539_);
                                    leanh::lean_dec(v___x_4514_);
                                    v___x_4541_ = leanh::lean_box(0);
                                    v_isShared_4542_ = v_isSharedCheck_4546_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_binderName_4475_);
                        leanh::lean_dec_ref(v_letDecl_4465_);
                        v_a_4547_ = leanh::lean_ctor_get(v___x_4510_, 0);
                        v_isSharedCheck_4554_ =
                            (!leanh::lean_is_exclusive(v___x_4510_)) as u8;
                        if v_isSharedCheck_4554_ == 0 {
                            v___x_4549_ = v___x_4510_;
                            v_isShared_4550_ = v_isSharedCheck_4554_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4547_);
                            leanh::lean_dec(v___x_4510_);
                            v___x_4549_ = leanh::lean_box(0);
                            v_isShared_4550_ = v_isSharedCheck_4554_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_binderName_4475_);
                    leanh::lean_dec_ref(v_letDecl_4465_);
                    return v___x_4509_;
                }
            }
            1 => {
                v___x_4483_ = 0;
                leanh::lean_inc(v_fvarId_4474_);
                v___x_4484_ = l_Lean_Compiler_LCNF_getLetDecl(
                    v___x_4483_,
                    v_fvarId_4474_,
                    v___y_4479_,
                    v___y_4480_,
                    v___y_4481_,
                    v___y_4482_,
                );
                if leanh::lean_obj_tag(v___x_4484_) == 0 {
                    v_a_4485_ = leanh::lean_ctor_get(v___x_4484_, 0);
                    v_isSharedCheck_4500_ = (!leanh::lean_is_exclusive(v___x_4484_)) as u8;
                    if v_isSharedCheck_4500_ == 0 {
                        v___x_4487_ = v___x_4484_;
                        v_isShared_4488_ = v_isSharedCheck_4500_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4485_);
                        leanh::lean_dec(v___x_4484_);
                        v___x_4487_ = leanh::lean_box(0);
                        v_isShared_4488_ = v_isSharedCheck_4500_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_binderName_4475_);
                    leanh::lean_dec_ref(v_letDecl_4465_);
                    v_a_4501_ = leanh::lean_ctor_get(v___x_4484_, 0);
                    v_isSharedCheck_4508_ = (!leanh::lean_is_exclusive(v___x_4484_)) as u8;
                    if v_isSharedCheck_4508_ == 0 {
                        v___x_4503_ = v___x_4484_;
                        v_isShared_4504_ = v_isSharedCheck_4508_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4501_);
                        leanh::lean_dec(v___x_4484_);
                        v___x_4503_ = leanh::lean_box(0);
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
                leanh::lean_dec(v_a_4485_);
                leanh::lean_dec_ref(v_letDecl_4465_);
                if v___x_4489_ == 0 {
                    leanh::lean_del_object(v___x_4487_);
                    v___x_4490_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1,
                    );
                    v___x_4491_ = l_Lean_MessageData_ofName(v_binderName_4475_);
                    v___x_4492_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4492_, 0, v___x_4490_);
                    leanh::lean_ctor_set(v___x_4492_, 1, v___x_4491_);
                    v___x_4493_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3,
                    );
                    v___x_4494_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4494_, 0, v___x_4492_);
                    leanh::lean_ctor_set(v___x_4494_, 1, v___x_4493_);
                    v___x_4495_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4494_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
                    return v___x_4495_;
                } else {
                    leanh::lean_dec(v_binderName_4475_);
                    v___x_4496_ = leanh::lean_box(0);
                    if v_isShared_4488_ == 0 {
                        leanh::lean_ctor_set(v___x_4487_, 0, v___x_4496_);
                        v___x_4498_ = v___x_4487_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4499_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
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
                    v_reuseFailAlloc_4507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
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
                    v_reuseFailAlloc_4537_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
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
                    v_reuseFailAlloc_4545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
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
                    v_reuseFailAlloc_4553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
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
    mut v_letDecl_4555_: *mut leanh::LeanObject,
    mut v_a_4556_: *mut leanh::LeanObject,
    mut v_a_4557_: *mut leanh::LeanObject,
    mut v_a_4558_: *mut leanh::LeanObject,
    mut v_a_4559_: *mut leanh::LeanObject,
    mut v_a_4560_: *mut leanh::LeanObject,
    mut v_a_4561_: *mut leanh::LeanObject,
    mut v_a_4562_: *mut leanh::LeanObject,
    mut v_a_4563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4562_);
    leanh::lean_dec_ref(v_a_4561_);
    leanh::lean_dec(v_a_4560_);
    leanh::lean_dec_ref(v_a_4559_);
    leanh::lean_dec_ref(v_a_4558_);
    leanh::lean_dec(v_a_4557_);
    leanh::lean_dec_ref(v_a_4556_);
    return v_res_4564_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(
    mut v_a_4565_: *mut leanh::LeanObject,
    mut v_x_4566_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4567_: u8 = 0;
    let mut v_key_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4566_) == 0 {
                    v___x_4567_ = 0;
                    return v___x_4567_;
                } else {
                    v_key_4568_ = leanh::lean_ctor_get(v_x_4566_, 0);
                    v_tail_4569_ = leanh::lean_ctor_get(v_x_4566_, 2);
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
    mut v_a_4572_: *mut leanh::LeanObject,
    mut v_x_4573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4574_: u8 = 0;
    let mut v_r_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_4572_, v_x_4573_);
    leanh::lean_dec(v_x_4573_);
    leanh::lean_dec(v_a_4572_);
    v_r_4575_ = leanh::lean_box((v_res_4574_) as usize);
    return v_r_4575_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_4576_: *mut leanh::LeanObject,
    mut v_x_4577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4577_) == 0 {
                    return v_x_4576_;
                } else {
                    v_key_4578_ = leanh::lean_ctor_get(v_x_4577_, 0);
                    v_value_4579_ = leanh::lean_ctor_get(v_x_4577_, 1);
                    v_tail_4580_ = leanh::lean_ctor_get(v_x_4577_, 2);
                    v_isSharedCheck_4603_ = (!leanh::lean_is_exclusive(v_x_4577_)) as u8;
                    if v_isSharedCheck_4603_ == 0 {
                        v___x_4582_ = v_x_4577_;
                        v_isShared_4583_ = v_isSharedCheck_4603_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4580_);
                        leanh::lean_inc(v_value_4579_);
                        leanh::lean_inc(v_key_4578_);
                        leanh::lean_dec(v_x_4577_);
                        v___x_4582_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_4597_);
                if v_isShared_4583_ == 0 {
                    leanh::lean_ctor_set(v___x_4582_, 2, v___x_4597_);
                    v___x_4599_ = v___x_4582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4602_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_key_4578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_value_4579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 2, v___x_4597_);
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
    mut v_i_4604_: *mut leanh::LeanObject,
    mut v_source_4605_: *mut leanh::LeanObject,
    mut v_target_4606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: u8 = 0;
    let mut v_es_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4607_ = lean_array_get_size(v_source_4605_);
                v___x_4608_ = lean_nat_dec_lt(v_i_4604_, v___x_4607_);
                if v___x_4608_ == 0 {
                    leanh::lean_dec_ref(v_source_4605_);
                    leanh::lean_dec(v_i_4604_);
                    return v_target_4606_;
                } else {
                    v_es_4609_ = lean_array_fget(v_source_4605_, v_i_4604_);
                    v___x_4610_ = leanh::lean_box(0);
                    v_source_4611_ = lean_array_fset(v_source_4605_, v_i_4604_, v___x_4610_);
                    v_target_4612_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4606_, v_es_4609_);
                    v___x_4613_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4614_ = lean_nat_add(v_i_4604_, v___x_4613_);
                    leanh::lean_dec(v_i_4604_);
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
    mut v_data_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4617_ = lean_array_get_size(v_data_4616_);
    v___x_4618_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4619_ = lean_nat_mul(v___x_4617_, v___x_4618_);
    v___x_4620_ = leanh::lean_unsigned_to_nat(0);
    v___x_4621_ = leanh::lean_box(0);
    v___x_4622_ = lean_mk_array(v_nbuckets_4619_, v___x_4621_);
    v___x_4623_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(v___x_4620_, v_data_4616_, v___x_4622_);
    return v___x_4623_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(
    mut v_m_4624_: *mut leanh::LeanObject,
    mut v_a_4625_: *mut leanh::LeanObject,
    mut v_b_4626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: u8 = 0;
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4646_: u8 = 0;
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v_val_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v_unused_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4627_ = leanh::lean_ctor_get(v_m_4624_, 0);
                v_buckets_4628_ = leanh::lean_ctor_get(v_m_4624_, 1);
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
                    leanh::lean_inc_ref(v_buckets_4628_);
                    leanh::lean_inc(v_size_4627_);
                    v_isSharedCheck_4664_ = (!leanh::lean_is_exclusive(v_m_4624_)) as u8;
                    if v_isSharedCheck_4664_ == 0 {
                        v_unused_4665_ = leanh::lean_ctor_get(v_m_4624_, 1);
                        leanh::lean_dec(v_unused_4665_);
                        v_unused_4666_ = leanh::lean_ctor_get(v_m_4624_, 0);
                        leanh::lean_dec(v_unused_4666_);
                        v___x_4645_ = v_m_4624_;
                        v_isShared_4646_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_4624_);
                        v___x_4645_ = leanh::lean_box(0);
                        v_isShared_4646_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_4626_);
                    leanh::lean_dec(v_a_4625_);
                    return v_m_4624_;
                }
            }
            1 => {
                v___x_4647_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_4648_ = lean_nat_add(v_size_4627_, v___x_4647_);
                leanh::lean_dec(v_size_4627_);
                leanh::lean_inc(v_bkt_4642_);
                v___x_4649_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4649_, 0, v_a_4625_);
                leanh::lean_ctor_set(v___x_4649_, 1, v_b_4626_);
                leanh::lean_ctor_set(v___x_4649_, 2, v_bkt_4642_);
                v_buckets_x27_4650_ = lean_array_uset(v_buckets_4628_, v___x_4641_, v___x_4649_);
                v___x_4651_ = leanh::lean_unsigned_to_nat(4);
                v___x_4652_ = lean_nat_mul(v_size_x27_4648_, v___x_4651_);
                v___x_4653_ = leanh::lean_unsigned_to_nat(3);
                v___x_4654_ = lean_nat_div(v___x_4652_, v___x_4653_);
                leanh::lean_dec(v___x_4652_);
                v___x_4655_ = lean_array_get_size(v_buckets_x27_4650_);
                v___x_4656_ = lean_nat_dec_le(v___x_4654_, v___x_4655_);
                leanh::lean_dec(v___x_4654_);
                if v___x_4656_ == 0 {
                    v_val_4657_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(v_buckets_x27_4650_);
                    if v_isShared_4646_ == 0 {
                        leanh::lean_ctor_set(v___x_4645_, 1, v_val_4657_);
                        leanh::lean_ctor_set(v___x_4645_, 0, v_size_x27_4648_);
                        v___x_4659_ = v___x_4645_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4660_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_size_x27_4648_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_val_4657_);
                        v___x_4659_ = v_reuseFailAlloc_4660_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4646_ == 0 {
                        leanh::lean_ctor_set(v___x_4645_, 1, v_buckets_x27_4650_);
                        leanh::lean_ctor_set(v___x_4645_, 0, v_size_x27_4648_);
                        v___x_4662_ = v___x_4645_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_size_x27_4648_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_buckets_x27_4650_);
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
    mut v_m_4667_: *mut leanh::LeanObject,
    mut v_a_4668_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    v_buckets_4669_ = leanh::lean_ctor_get(v_m_4667_, 1);
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
    mut v_m_4685_: *mut leanh::LeanObject,
    mut v_a_4686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4687_: u8 = 0;
    let mut v_r_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4687_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v_m_4685_, v_a_4686_);
    leanh::lean_dec(v_a_4686_);
    leanh::lean_dec_ref(v_m_4685_);
    v_r_4688_ = leanh::lean_box((v_res_4687_) as usize);
    return v_r_4688_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4690_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0;
    v___x_4691_ = l_Lean_stringToMessageData(v___x_4690_);
    return v___x_4691_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
    mut v_fvarId_4692_: *mut leanh::LeanObject,
    mut v_a_4693_: *mut leanh::LeanObject,
    mut v_a_4694_: *mut leanh::LeanObject,
    mut v_a_4695_: *mut leanh::LeanObject,
    mut v_a_4696_: *mut leanh::LeanObject,
    mut v_a_4697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: u8 = 0;
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4706_ = lean_st_ref_get(v_a_4693_);
                v___x_4707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v___x_4706_, v_fvarId_4692_);
                leanh::lean_dec(v___x_4706_);
                if v___x_4707_ == 0 {
                    v___y_4700_ = v_a_4693_;
                    state = 1;
                    continue;
                } else {
                    v___x_4708_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1,
                    );
                    v___x_4709_ = l_Lean_MessageData_ofName(v_fvarId_4692_);
                    v___x_4710_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4710_, 0, v___x_4708_);
                    leanh::lean_ctor_set(v___x_4710_, 1, v___x_4709_);
                    v___x_4711_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                    v___x_4712_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4712_, 0, v___x_4710_);
                    leanh::lean_ctor_set(v___x_4712_, 1, v___x_4711_);
                    v___x_4713_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4712_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
                    return v___x_4713_;
                }
            }
            1 => {
                v___x_4701_ = lean_st_ref_take(v___y_4700_);
                v___x_4702_ = leanh::lean_box(0);
                v___x_4703_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(v___x_4701_, v_fvarId_4692_, v___x_4702_);
                v___x_4704_ = lean_st_ref_set(v___y_4700_, v___x_4703_);
                v___x_4705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4705_, 0, v___x_4702_);
                return v___x_4705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___boxed(
    mut v_fvarId_4714_: *mut leanh::LeanObject,
    mut v_a_4715_: *mut leanh::LeanObject,
    mut v_a_4716_: *mut leanh::LeanObject,
    mut v_a_4717_: *mut leanh::LeanObject,
    mut v_a_4718_: *mut leanh::LeanObject,
    mut v_a_4719_: *mut leanh::LeanObject,
    mut v_a_4720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4721_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
        v_fvarId_4714_,
        v_a_4715_,
        v_a_4716_,
        v_a_4717_,
        v_a_4718_,
        v_a_4719_,
    );
    leanh::lean_dec(v_a_4719_);
    leanh::lean_dec_ref(v_a_4718_);
    leanh::lean_dec(v_a_4717_);
    leanh::lean_dec_ref(v_a_4716_);
    leanh::lean_dec(v_a_4715_);
    return v_res_4721_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId(
    mut v_fvarId_4722_: *mut leanh::LeanObject,
    mut v_a_4723_: *mut leanh::LeanObject,
    mut v_a_4724_: *mut leanh::LeanObject,
    mut v_a_4725_: *mut leanh::LeanObject,
    mut v_a_4726_: *mut leanh::LeanObject,
    mut v_a_4727_: *mut leanh::LeanObject,
    mut v_a_4728_: *mut leanh::LeanObject,
    mut v_a_4729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_fvarId_4732_: *mut leanh::LeanObject,
    mut v_a_4733_: *mut leanh::LeanObject,
    mut v_a_4734_: *mut leanh::LeanObject,
    mut v_a_4735_: *mut leanh::LeanObject,
    mut v_a_4736_: *mut leanh::LeanObject,
    mut v_a_4737_: *mut leanh::LeanObject,
    mut v_a_4738_: *mut leanh::LeanObject,
    mut v_a_4739_: *mut leanh::LeanObject,
    mut v_a_4740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4739_);
    leanh::lean_dec_ref(v_a_4738_);
    leanh::lean_dec(v_a_4737_);
    leanh::lean_dec_ref(v_a_4736_);
    leanh::lean_dec_ref(v_a_4735_);
    leanh::lean_dec(v_a_4734_);
    leanh::lean_dec_ref(v_a_4733_);
    return v_res_4741_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0(
    mut v_00_u03b2_4742_: *mut leanh::LeanObject,
    mut v_m_4743_: *mut leanh::LeanObject,
    mut v_a_4744_: *mut leanh::LeanObject,
    mut v_b_4745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4746_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(v_m_4743_, v_a_4744_, v_b_4745_);
    return v___x_4746_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(
    mut v_00_u03b2_4747_: *mut leanh::LeanObject,
    mut v_m_4748_: *mut leanh::LeanObject,
    mut v_a_4749_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4750_: u8 = 0;
    v___x_4750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v_m_4748_, v_a_4749_);
    return v___x_4750_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___boxed(
    mut v_00_u03b2_4751_: *mut leanh::LeanObject,
    mut v_m_4752_: *mut leanh::LeanObject,
    mut v_a_4753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4754_: u8 = 0;
    let mut v_r_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4754_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(v_00_u03b2_4751_, v_m_4752_, v_a_4753_);
    leanh::lean_dec(v_a_4753_);
    leanh::lean_dec_ref(v_m_4752_);
    v_r_4755_ = leanh::lean_box((v_res_4754_) as usize);
    return v_r_4755_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(
    mut v_00_u03b2_4756_: *mut leanh::LeanObject,
    mut v_a_4757_: *mut leanh::LeanObject,
    mut v_x_4758_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4759_: u8 = 0;
    v___x_4759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_4757_, v_x_4758_);
    return v___x_4759_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___boxed(
    mut v_00_u03b2_4760_: *mut leanh::LeanObject,
    mut v_a_4761_: *mut leanh::LeanObject,
    mut v_x_4762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4763_: u8 = 0;
    let mut v_r_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(v_00_u03b2_4760_, v_a_4761_, v_x_4762_);
    leanh::lean_dec(v_x_4762_);
    leanh::lean_dec(v_a_4761_);
    v_r_4764_ = leanh::lean_box((v_res_4763_) as usize);
    return v_r_4764_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1(
    mut v_00_u03b2_4765_: *mut leanh::LeanObject,
    mut v_data_4766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(v_data_4766_);
    return v___x_4767_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4768_: *mut leanh::LeanObject,
    mut v_i_4769_: *mut leanh::LeanObject,
    mut v_source_4770_: *mut leanh::LeanObject,
    mut v_target_4771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4772_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(v_i_4769_, v_source_4770_, v_target_4771_);
    return v___x_4772_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4773_: *mut leanh::LeanObject,
    mut v_x_4774_: *mut leanh::LeanObject,
    mut v_x_4775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4776_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4774_, v_x_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg(
    mut v_fvarId_4777_: *mut leanh::LeanObject,
    mut v_x_4778_: *mut leanh::LeanObject,
    mut v_a_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
    mut v_a_4781_: *mut leanh::LeanObject,
    mut v_a_4782_: *mut leanh::LeanObject,
    mut v_a_4783_: *mut leanh::LeanObject,
    mut v_a_4784_: *mut leanh::LeanObject,
    mut v_a_4785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_fvarId_4777_);
                v___x_4787_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4777_,
                    v_a_4780_,
                    v_a_4782_,
                    v_a_4783_,
                    v_a_4784_,
                    v_a_4785_,
                );
                if leanh::lean_obj_tag(v___x_4787_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4787_, 1);
                    v_jps_4788_ = leanh::lean_ctor_get(v_a_4779_, 0);
                    v_vars_4789_ = leanh::lean_ctor_get(v_a_4779_, 1);
                    leanh::lean_inc(v_vars_4789_);
                    v___x_4790_ = l_Lean_FVarIdSet_insert(v_vars_4789_, v_fvarId_4777_);
                    leanh::lean_inc(v_jps_4788_);
                    v___x_4791_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4791_, 0, v_jps_4788_);
                    leanh::lean_ctor_set(v___x_4791_, 1, v___x_4790_);
                    leanh::lean_inc(v_a_4785_);
                    leanh::lean_inc_ref(v_a_4784_);
                    leanh::lean_inc(v_a_4783_);
                    leanh::lean_inc_ref(v_a_4782_);
                    leanh::lean_inc_ref(v_a_4781_);
                    leanh::lean_inc(v_a_4780_);
                    v___x_4792_ = leanh::lean_apply_8(
                        v_x_4778_,
                        v___x_4791_,
                        v_a_4780_,
                        v_a_4781_,
                        v_a_4782_,
                        v_a_4783_,
                        v_a_4784_,
                        v_a_4785_,
                        leanh::lean_box(0),
                    );
                    return v___x_4792_;
                } else {
                    leanh::lean_dec_ref(v_x_4778_);
                    leanh::lean_dec(v_fvarId_4777_);
                    v_a_4793_ = leanh::lean_ctor_get(v___x_4787_, 0);
                    v_isSharedCheck_4800_ = (!leanh::lean_is_exclusive(v___x_4787_)) as u8;
                    if v_isSharedCheck_4800_ == 0 {
                        v___x_4795_ = v___x_4787_;
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4793_);
                        leanh::lean_dec(v___x_4787_);
                        v___x_4795_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4799_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
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
    mut v_fvarId_4801_: *mut leanh::LeanObject,
    mut v_x_4802_: *mut leanh::LeanObject,
    mut v_a_4803_: *mut leanh::LeanObject,
    mut v_a_4804_: *mut leanh::LeanObject,
    mut v_a_4805_: *mut leanh::LeanObject,
    mut v_a_4806_: *mut leanh::LeanObject,
    mut v_a_4807_: *mut leanh::LeanObject,
    mut v_a_4808_: *mut leanh::LeanObject,
    mut v_a_4809_: *mut leanh::LeanObject,
    mut v_a_4810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4809_);
    leanh::lean_dec_ref(v_a_4808_);
    leanh::lean_dec(v_a_4807_);
    leanh::lean_dec_ref(v_a_4806_);
    leanh::lean_dec_ref(v_a_4805_);
    leanh::lean_dec(v_a_4804_);
    leanh::lean_dec_ref(v_a_4803_);
    return v_res_4811_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withFVarId(
    mut v_00_u03b1_4812_: *mut leanh::LeanObject,
    mut v_fvarId_4813_: *mut leanh::LeanObject,
    mut v_x_4814_: *mut leanh::LeanObject,
    mut v_a_4815_: *mut leanh::LeanObject,
    mut v_a_4816_: *mut leanh::LeanObject,
    mut v_a_4817_: *mut leanh::LeanObject,
    mut v_a_4818_: *mut leanh::LeanObject,
    mut v_a_4819_: *mut leanh::LeanObject,
    mut v_a_4820_: *mut leanh::LeanObject,
    mut v_a_4821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4832_: u8 = 0;
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_fvarId_4813_);
                v___x_4823_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4813_,
                    v_a_4816_,
                    v_a_4818_,
                    v_a_4819_,
                    v_a_4820_,
                    v_a_4821_,
                );
                if leanh::lean_obj_tag(v___x_4823_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4823_, 1);
                    v_jps_4824_ = leanh::lean_ctor_get(v_a_4815_, 0);
                    v_vars_4825_ = leanh::lean_ctor_get(v_a_4815_, 1);
                    leanh::lean_inc(v_vars_4825_);
                    v___x_4826_ = l_Lean_FVarIdSet_insert(v_vars_4825_, v_fvarId_4813_);
                    leanh::lean_inc(v_jps_4824_);
                    v___x_4827_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4827_, 0, v_jps_4824_);
                    leanh::lean_ctor_set(v___x_4827_, 1, v___x_4826_);
                    leanh::lean_inc(v_a_4821_);
                    leanh::lean_inc_ref(v_a_4820_);
                    leanh::lean_inc(v_a_4819_);
                    leanh::lean_inc_ref(v_a_4818_);
                    leanh::lean_inc_ref(v_a_4817_);
                    leanh::lean_inc(v_a_4816_);
                    v___x_4828_ = leanh::lean_apply_8(
                        v_x_4814_,
                        v___x_4827_,
                        v_a_4816_,
                        v_a_4817_,
                        v_a_4818_,
                        v_a_4819_,
                        v_a_4820_,
                        v_a_4821_,
                        leanh::lean_box(0),
                    );
                    return v___x_4828_;
                } else {
                    leanh::lean_dec_ref(v_x_4814_);
                    leanh::lean_dec(v_fvarId_4813_);
                    v_a_4829_ = leanh::lean_ctor_get(v___x_4823_, 0);
                    v_isSharedCheck_4836_ = (!leanh::lean_is_exclusive(v___x_4823_)) as u8;
                    if v_isSharedCheck_4836_ == 0 {
                        v___x_4831_ = v___x_4823_;
                        v_isShared_4832_ = v_isSharedCheck_4836_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4829_);
                        leanh::lean_dec(v___x_4823_);
                        v___x_4831_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4835_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
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
    mut v_00_u03b1_4837_: *mut leanh::LeanObject,
    mut v_fvarId_4838_: *mut leanh::LeanObject,
    mut v_x_4839_: *mut leanh::LeanObject,
    mut v_a_4840_: *mut leanh::LeanObject,
    mut v_a_4841_: *mut leanh::LeanObject,
    mut v_a_4842_: *mut leanh::LeanObject,
    mut v_a_4843_: *mut leanh::LeanObject,
    mut v_a_4844_: *mut leanh::LeanObject,
    mut v_a_4845_: *mut leanh::LeanObject,
    mut v_a_4846_: *mut leanh::LeanObject,
    mut v_a_4847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4846_);
    leanh::lean_dec_ref(v_a_4845_);
    leanh::lean_dec(v_a_4844_);
    leanh::lean_dec_ref(v_a_4843_);
    leanh::lean_dec_ref(v_a_4842_);
    leanh::lean_dec(v_a_4841_);
    leanh::lean_dec_ref(v_a_4840_);
    return v_res_4848_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg(
    mut v_fvarId_4849_: *mut leanh::LeanObject,
    mut v_x_4850_: *mut leanh::LeanObject,
    mut v_a_4851_: *mut leanh::LeanObject,
    mut v_a_4852_: *mut leanh::LeanObject,
    mut v_a_4853_: *mut leanh::LeanObject,
    mut v_a_4854_: *mut leanh::LeanObject,
    mut v_a_4855_: *mut leanh::LeanObject,
    mut v_a_4856_: *mut leanh::LeanObject,
    mut v_a_4857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_fvarId_4849_);
                v___x_4859_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4849_,
                    v_a_4852_,
                    v_a_4854_,
                    v_a_4855_,
                    v_a_4856_,
                    v_a_4857_,
                );
                if leanh::lean_obj_tag(v___x_4859_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4859_, 1);
                    v_jps_4860_ = leanh::lean_ctor_get(v_a_4851_, 0);
                    v_vars_4861_ = leanh::lean_ctor_get(v_a_4851_, 1);
                    leanh::lean_inc(v_jps_4860_);
                    v___x_4862_ = l_Lean_FVarIdSet_insert(v_jps_4860_, v_fvarId_4849_);
                    leanh::lean_inc(v_vars_4861_);
                    v___x_4863_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4863_, 0, v___x_4862_);
                    leanh::lean_ctor_set(v___x_4863_, 1, v_vars_4861_);
                    leanh::lean_inc(v_a_4857_);
                    leanh::lean_inc_ref(v_a_4856_);
                    leanh::lean_inc(v_a_4855_);
                    leanh::lean_inc_ref(v_a_4854_);
                    leanh::lean_inc_ref(v_a_4853_);
                    leanh::lean_inc(v_a_4852_);
                    v___x_4864_ = leanh::lean_apply_8(
                        v_x_4850_,
                        v___x_4863_,
                        v_a_4852_,
                        v_a_4853_,
                        v_a_4854_,
                        v_a_4855_,
                        v_a_4856_,
                        v_a_4857_,
                        leanh::lean_box(0),
                    );
                    return v___x_4864_;
                } else {
                    leanh::lean_dec_ref(v_x_4850_);
                    leanh::lean_dec(v_fvarId_4849_);
                    v_a_4865_ = leanh::lean_ctor_get(v___x_4859_, 0);
                    v_isSharedCheck_4872_ = (!leanh::lean_is_exclusive(v___x_4859_)) as u8;
                    if v_isSharedCheck_4872_ == 0 {
                        v___x_4867_ = v___x_4859_;
                        v_isShared_4868_ = v_isSharedCheck_4872_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4865_);
                        leanh::lean_dec(v___x_4859_);
                        v___x_4867_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
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
    mut v_fvarId_4873_: *mut leanh::LeanObject,
    mut v_x_4874_: *mut leanh::LeanObject,
    mut v_a_4875_: *mut leanh::LeanObject,
    mut v_a_4876_: *mut leanh::LeanObject,
    mut v_a_4877_: *mut leanh::LeanObject,
    mut v_a_4878_: *mut leanh::LeanObject,
    mut v_a_4879_: *mut leanh::LeanObject,
    mut v_a_4880_: *mut leanh::LeanObject,
    mut v_a_4881_: *mut leanh::LeanObject,
    mut v_a_4882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4881_);
    leanh::lean_dec_ref(v_a_4880_);
    leanh::lean_dec(v_a_4879_);
    leanh::lean_dec_ref(v_a_4878_);
    leanh::lean_dec_ref(v_a_4877_);
    leanh::lean_dec(v_a_4876_);
    leanh::lean_dec_ref(v_a_4875_);
    return v_res_4883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withJp(
    mut v_00_u03b1_4884_: *mut leanh::LeanObject,
    mut v_fvarId_4885_: *mut leanh::LeanObject,
    mut v_x_4886_: *mut leanh::LeanObject,
    mut v_a_4887_: *mut leanh::LeanObject,
    mut v_a_4888_: *mut leanh::LeanObject,
    mut v_a_4889_: *mut leanh::LeanObject,
    mut v_a_4890_: *mut leanh::LeanObject,
    mut v_a_4891_: *mut leanh::LeanObject,
    mut v_a_4892_: *mut leanh::LeanObject,
    mut v_a_4893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4904_: u8 = 0;
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_fvarId_4885_);
                v___x_4895_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4885_,
                    v_a_4888_,
                    v_a_4890_,
                    v_a_4891_,
                    v_a_4892_,
                    v_a_4893_,
                );
                if leanh::lean_obj_tag(v___x_4895_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4895_, 1);
                    v_jps_4896_ = leanh::lean_ctor_get(v_a_4887_, 0);
                    v_vars_4897_ = leanh::lean_ctor_get(v_a_4887_, 1);
                    leanh::lean_inc(v_jps_4896_);
                    v___x_4898_ = l_Lean_FVarIdSet_insert(v_jps_4896_, v_fvarId_4885_);
                    leanh::lean_inc(v_vars_4897_);
                    v___x_4899_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4899_, 0, v___x_4898_);
                    leanh::lean_ctor_set(v___x_4899_, 1, v_vars_4897_);
                    leanh::lean_inc(v_a_4893_);
                    leanh::lean_inc_ref(v_a_4892_);
                    leanh::lean_inc(v_a_4891_);
                    leanh::lean_inc_ref(v_a_4890_);
                    leanh::lean_inc_ref(v_a_4889_);
                    leanh::lean_inc(v_a_4888_);
                    v___x_4900_ = leanh::lean_apply_8(
                        v_x_4886_,
                        v___x_4899_,
                        v_a_4888_,
                        v_a_4889_,
                        v_a_4890_,
                        v_a_4891_,
                        v_a_4892_,
                        v_a_4893_,
                        leanh::lean_box(0),
                    );
                    return v___x_4900_;
                } else {
                    leanh::lean_dec_ref(v_x_4886_);
                    leanh::lean_dec(v_fvarId_4885_);
                    v_a_4901_ = leanh::lean_ctor_get(v___x_4895_, 0);
                    v_isSharedCheck_4908_ = (!leanh::lean_is_exclusive(v___x_4895_)) as u8;
                    if v_isSharedCheck_4908_ == 0 {
                        v___x_4903_ = v___x_4895_;
                        v_isShared_4904_ = v_isSharedCheck_4908_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4901_);
                        leanh::lean_dec(v___x_4895_);
                        v___x_4903_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
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
    mut v_00_u03b1_4909_: *mut leanh::LeanObject,
    mut v_fvarId_4910_: *mut leanh::LeanObject,
    mut v_x_4911_: *mut leanh::LeanObject,
    mut v_a_4912_: *mut leanh::LeanObject,
    mut v_a_4913_: *mut leanh::LeanObject,
    mut v_a_4914_: *mut leanh::LeanObject,
    mut v_a_4915_: *mut leanh::LeanObject,
    mut v_a_4916_: *mut leanh::LeanObject,
    mut v_a_4917_: *mut leanh::LeanObject,
    mut v_a_4918_: *mut leanh::LeanObject,
    mut v_a_4919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4918_);
    leanh::lean_dec_ref(v_a_4917_);
    leanh::lean_dec(v_a_4916_);
    leanh::lean_dec_ref(v_a_4915_);
    leanh::lean_dec_ref(v_a_4914_);
    leanh::lean_dec(v_a_4913_);
    leanh::lean_dec_ref(v_a_4912_);
    return v_res_4920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0(
    mut v_x1_4921_: *mut leanh::LeanObject,
    mut v_x2_4922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fvarId_4923_ = leanh::lean_ctor_get(v_x2_4922_, 0);
    leanh::lean_inc(v_fvarId_4923_);
    leanh::lean_dec_ref(v_x2_4922_);
    v___x_4924_ = l_Lean_FVarIdSet_insert(v_x1_4921_, v_fvarId_4923_);
    return v___x_4924_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1(
    mut v_x_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
    mut v___y_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
    mut v___y_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
    mut v___y_4932_: *mut leanh::LeanObject,
    mut v___y_4933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fvarId_4935_ = leanh::lean_ctor_get(v___y_4926_, 0);
    leanh::lean_inc(v_fvarId_4935_);
    leanh::lean_dec_ref(v___y_4926_);
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
    mut v_x_4937_: *mut leanh::LeanObject,
    mut v___y_4938_: *mut leanh::LeanObject,
    mut v___y_4939_: *mut leanh::LeanObject,
    mut v___y_4940_: *mut leanh::LeanObject,
    mut v___y_4941_: *mut leanh::LeanObject,
    mut v___y_4942_: *mut leanh::LeanObject,
    mut v___y_4943_: *mut leanh::LeanObject,
    mut v___y_4944_: *mut leanh::LeanObject,
    mut v___y_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4945_);
    leanh::lean_dec_ref(v___y_4944_);
    leanh::lean_dec(v___y_4943_);
    leanh::lean_dec_ref(v___y_4942_);
    leanh::lean_dec_ref(v___y_4941_);
    leanh::lean_dec(v___y_4940_);
    leanh::lean_dec_ref(v___y_4939_);
    return v_res_4947_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4948_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_4948_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4949_ = leanh::lean_obj_once(
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
    mut v_params_4976_: *mut leanh::LeanObject,
    mut v_x_4977_: *mut leanh::LeanObject,
    mut v_a_4978_: *mut leanh::LeanObject,
    mut v_a_4979_: *mut leanh::LeanObject,
    mut v_a_4980_: *mut leanh::LeanObject,
    mut v_a_4981_: *mut leanh::LeanObject,
    mut v_a_4982_: *mut leanh::LeanObject,
    mut v_a_4983_: *mut leanh::LeanObject,
    mut v_a_4984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v_toFunctor_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v___f_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: u8 = 0;
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: usize = 0;
    let mut v___x_5041_: usize = 0;
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: usize = 0;
    let mut v___x_5046_: usize = 0;
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v___x_5060_: u8 = 0;
    let mut v___f_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5064_: usize = 0;
    let mut v___x_5065_: usize = 0;
    let mut v___x_1277__overap_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: usize = 0;
    let mut v___x_5069_: usize = 0;
    let mut v___x_1281__overap_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5074_: u8 = 0;
    let mut v_unused_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5076_: u8 = 0;
    let mut v_unused_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4986_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1,
                );
                v_toApplicative_4987_ = leanh::lean_ctor_get(v___x_4986_, 0);
                v_toFunctor_4988_ = leanh::lean_ctor_get(v_toApplicative_4987_, 0);
                v_toSeq_4989_ = leanh::lean_ctor_get(v_toApplicative_4987_, 2);
                v_toSeqLeft_4990_ = leanh::lean_ctor_get(v_toApplicative_4987_, 3);
                v_toSeqRight_4991_ = leanh::lean_ctor_get(v_toApplicative_4987_, 4);
                v___f_4992_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2;
                v___f_4993_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_4988_, 2);
                v___f_4994_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4994_, 0, v_toFunctor_4988_);
                v___f_4995_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4995_, 0, v_toFunctor_4988_);
                v___x_4996_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4996_, 0, v___f_4994_);
                leanh::lean_ctor_set(v___x_4996_, 1, v___f_4995_);
                leanh::lean_inc(v_toSeqRight_4991_);
                v___f_4997_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4997_, 0, v_toSeqRight_4991_);
                leanh::lean_inc(v_toSeqLeft_4990_);
                v___f_4998_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4998_, 0, v_toSeqLeft_4990_);
                leanh::lean_inc(v_toSeq_4989_);
                v___f_4999_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4999_, 0, v_toSeq_4989_);
                v___x_5000_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5000_, 0, v___x_4996_);
                leanh::lean_ctor_set(v___x_5000_, 1, v___f_4992_);
                leanh::lean_ctor_set(v___x_5000_, 2, v___f_4999_);
                leanh::lean_ctor_set(v___x_5000_, 3, v___f_4998_);
                leanh::lean_ctor_set(v___x_5000_, 4, v___f_4997_);
                v___x_5001_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5001_, 0, v___x_5000_);
                leanh::lean_ctor_set(v___x_5001_, 1, v___f_4993_);
                v___x_5002_ = l_StateRefT_x27_instMonad___redArg(v___x_5001_);
                v_toApplicative_5003_ = leanh::lean_ctor_get(v___x_5002_, 0);
                v_isSharedCheck_5076_ = (!leanh::lean_is_exclusive(v___x_5002_)) as u8;
                if v_isSharedCheck_5076_ == 0 {
                    v_unused_5077_ = leanh::lean_ctor_get(v___x_5002_, 1);
                    leanh::lean_dec(v_unused_5077_);
                    v___x_5005_ = v___x_5002_;
                    v_isShared_5006_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_5003_);
                    leanh::lean_dec(v___x_5002_);
                    v___x_5005_ = leanh::lean_box(0);
                    v_isShared_5006_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5007_ = leanh::lean_ctor_get(v_toApplicative_5003_, 0);
                v_toSeq_5008_ = leanh::lean_ctor_get(v_toApplicative_5003_, 2);
                v_toSeqLeft_5009_ = leanh::lean_ctor_get(v_toApplicative_5003_, 3);
                v_toSeqRight_5010_ = leanh::lean_ctor_get(v_toApplicative_5003_, 4);
                v_isSharedCheck_5074_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_5003_)) as u8;
                if v_isSharedCheck_5074_ == 0 {
                    v_unused_5075_ = leanh::lean_ctor_get(v_toApplicative_5003_, 1);
                    leanh::lean_dec(v_unused_5075_);
                    v___x_5012_ = v_toApplicative_5003_;
                    v_isShared_5013_ = v_isSharedCheck_5074_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_5010_);
                    leanh::lean_inc(v_toSeqLeft_5009_);
                    leanh::lean_inc(v_toSeq_5008_);
                    leanh::lean_inc(v_toFunctor_5007_);
                    leanh::lean_dec(v_toApplicative_5003_);
                    v___x_5012_ = leanh::lean_box(0);
                    v_isShared_5013_ = v_isSharedCheck_5074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5014_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4;
                v___f_5015_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5;
                v___f_5016_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6;
                leanh::lean_inc_ref(v_toFunctor_5007_);
                v___f_5017_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5017_, 0, v_toFunctor_5007_);
                v___f_5018_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5018_, 0, v_toFunctor_5007_);
                v___x_5019_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5019_, 0, v___f_5017_);
                leanh::lean_ctor_set(v___x_5019_, 1, v___f_5018_);
                v___f_5020_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5020_, 0, v_toSeqRight_5010_);
                v___f_5021_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5021_, 0, v_toSeqLeft_5009_);
                v___f_5022_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5022_, 0, v_toSeq_5008_);
                if v_isShared_5013_ == 0 {
                    leanh::lean_ctor_set(v___x_5012_, 4, v___f_5020_);
                    leanh::lean_ctor_set(v___x_5012_, 3, v___f_5021_);
                    leanh::lean_ctor_set(v___x_5012_, 2, v___f_5022_);
                    leanh::lean_ctor_set(v___x_5012_, 1, v___f_5015_);
                    leanh::lean_ctor_set(v___x_5012_, 0, v___x_5019_);
                    v___x_5024_ = v___x_5012_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5073_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 1, v___f_5015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 2, v___f_5022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 3, v___f_5021_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5073_, 4, v___f_5020_);
                    v___x_5024_ = v_reuseFailAlloc_5073_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5006_ == 0 {
                    leanh::lean_ctor_set(v___x_5005_, 1, v___f_5016_);
                    leanh::lean_ctor_set(v___x_5005_, 0, v___x_5024_);
                    v___x_5026_ = v___x_5005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___f_5016_);
                    v___x_5026_ = v_reuseFailAlloc_5072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5027_ = l_ReaderT_instMonad___redArg(v___x_5026_);
                v___x_5028_ = l_StateRefT_x27_instMonad___redArg(v___x_5027_);
                v___x_5029_ = l_ReaderT_instMonad___redArg(v___x_5028_);
                v___x_5030_ = leanh::lean_unsigned_to_nat(0);
                v___x_5031_ = lean_array_get_size(v_params_4976_);
                v___x_5060_ = lean_nat_dec_lt(v___x_5030_, v___x_5031_);
                if v___x_5060_ == 0 {
                    leanh::lean_dec_ref(v___x_5029_);
                    state = 5;
                    continue;
                } else {
                    v___f_5061_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17;
                    v___x_5062_ = leanh::lean_box(0);
                    v___x_5063_ = lean_nat_dec_le(v___x_5031_, v___x_5031_);
                    if v___x_5063_ == 0 {
                        if v___x_5060_ == 0 {
                            leanh::lean_dec_ref(v___x_5029_);
                            state = 5;
                            continue;
                        } else {
                            v___x_5064_ = 0usize;
                            v___x_5065_ = lean_usize_of_nat(v___x_5031_);
                            leanh::lean_inc_ref(v_params_4976_);
                            v___x_1277__overap_5066_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_5029_,
                                    v___f_5061_,
                                    v_params_4976_,
                                    v___x_5064_,
                                    v___x_5065_,
                                    v___x_5062_,
                                );
                            leanh::lean_inc(v_a_4984_);
                            leanh::lean_inc_ref(v_a_4983_);
                            leanh::lean_inc(v_a_4982_);
                            leanh::lean_inc_ref(v_a_4981_);
                            leanh::lean_inc_ref(v_a_4980_);
                            leanh::lean_inc(v_a_4979_);
                            leanh::lean_inc_ref(v_a_4978_);
                            v___x_5067_ = leanh::lean_apply_8(
                                v___x_1277__overap_5066_,
                                v_a_4978_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                leanh::lean_box(0),
                            );
                            v___y_5051_ = v___x_5067_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_5068_ = 0usize;
                        v___x_5069_ = lean_usize_of_nat(v___x_5031_);
                        leanh::lean_inc_ref(v_params_4976_);
                        v___x_1281__overap_5070_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_5029_,
                                v___f_5061_,
                                v_params_4976_,
                                v___x_5068_,
                                v___x_5069_,
                                v___x_5062_,
                            );
                        leanh::lean_inc(v_a_4984_);
                        leanh::lean_inc_ref(v_a_4983_);
                        leanh::lean_inc(v_a_4982_);
                        leanh::lean_inc_ref(v_a_4981_);
                        leanh::lean_inc_ref(v_a_4980_);
                        leanh::lean_inc(v_a_4979_);
                        leanh::lean_inc_ref(v_a_4978_);
                        v___x_5071_ = leanh::lean_apply_8(
                            v___x_1281__overap_5070_,
                            v_a_4978_,
                            v_a_4979_,
                            v_a_4980_,
                            v_a_4981_,
                            v_a_4982_,
                            v_a_4983_,
                            v_a_4984_,
                            leanh::lean_box(0),
                        );
                        v___y_5051_ = v___x_5071_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_jps_5033_ = leanh::lean_ctor_get(v_a_4978_, 0);
                v_vars_5034_ = leanh::lean_ctor_get(v_a_4978_, 1);
                v___x_5035_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16;
                v___x_5036_ = lean_nat_dec_lt(v___x_5030_, v___x_5031_);
                if v___x_5036_ == 0 {
                    leanh::lean_dec_ref(v_params_4976_);
                    leanh::lean_inc(v_a_4984_);
                    leanh::lean_inc_ref(v_a_4983_);
                    leanh::lean_inc(v_a_4982_);
                    leanh::lean_inc_ref(v_a_4981_);
                    leanh::lean_inc_ref(v_a_4980_);
                    leanh::lean_inc(v_a_4979_);
                    leanh::lean_inc_ref(v_a_4978_);
                    v___x_5037_ = leanh::lean_apply_8(
                        v_x_4977_,
                        v_a_4978_,
                        v_a_4979_,
                        v_a_4980_,
                        v_a_4981_,
                        v_a_4982_,
                        v_a_4983_,
                        v_a_4984_,
                        leanh::lean_box(0),
                    );
                    return v___x_5037_;
                } else {
                    v___x_5038_ = lean_nat_dec_le(v___x_5031_, v___x_5031_);
                    if v___x_5038_ == 0 {
                        if v___x_5036_ == 0 {
                            leanh::lean_dec_ref(v_params_4976_);
                            leanh::lean_inc(v_a_4984_);
                            leanh::lean_inc_ref(v_a_4983_);
                            leanh::lean_inc(v_a_4982_);
                            leanh::lean_inc_ref(v_a_4981_);
                            leanh::lean_inc_ref(v_a_4980_);
                            leanh::lean_inc(v_a_4979_);
                            leanh::lean_inc_ref(v_a_4978_);
                            v___x_5039_ = leanh::lean_apply_8(
                                v_x_4977_,
                                v_a_4978_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                leanh::lean_box(0),
                            );
                            return v___x_5039_;
                        } else {
                            v___x_5040_ = 0usize;
                            v___x_5041_ = lean_usize_of_nat(v___x_5031_);
                            leanh::lean_inc(v_vars_5034_);
                            v___x_5042_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_5035_,
                                    v___f_5014_,
                                    v_params_4976_,
                                    v___x_5040_,
                                    v___x_5041_,
                                    v_vars_5034_,
                                );
                            leanh::lean_inc(v_jps_5033_);
                            v___x_5043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5043_, 0, v_jps_5033_);
                            leanh::lean_ctor_set(v___x_5043_, 1, v___x_5042_);
                            leanh::lean_inc(v_a_4984_);
                            leanh::lean_inc_ref(v_a_4983_);
                            leanh::lean_inc(v_a_4982_);
                            leanh::lean_inc_ref(v_a_4981_);
                            leanh::lean_inc_ref(v_a_4980_);
                            leanh::lean_inc(v_a_4979_);
                            v___x_5044_ = leanh::lean_apply_8(
                                v_x_4977_,
                                v___x_5043_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                leanh::lean_box(0),
                            );
                            return v___x_5044_;
                        }
                    } else {
                        v___x_5045_ = 0usize;
                        v___x_5046_ = lean_usize_of_nat(v___x_5031_);
                        leanh::lean_inc(v_vars_5034_);
                        v___x_5047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_5035_,
                            v___f_5014_,
                            v_params_4976_,
                            v___x_5045_,
                            v___x_5046_,
                            v_vars_5034_,
                        );
                        leanh::lean_inc(v_jps_5033_);
                        v___x_5048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5048_, 0, v_jps_5033_);
                        leanh::lean_ctor_set(v___x_5048_, 1, v___x_5047_);
                        leanh::lean_inc(v_a_4984_);
                        leanh::lean_inc_ref(v_a_4983_);
                        leanh::lean_inc(v_a_4982_);
                        leanh::lean_inc_ref(v_a_4981_);
                        leanh::lean_inc_ref(v_a_4980_);
                        leanh::lean_inc(v_a_4979_);
                        v___x_5049_ = leanh::lean_apply_8(
                            v_x_4977_,
                            v___x_5048_,
                            v_a_4979_,
                            v_a_4980_,
                            v_a_4981_,
                            v_a_4982_,
                            v_a_4983_,
                            v_a_4984_,
                            leanh::lean_box(0),
                        );
                        return v___x_5049_;
                    }
                }
            }
            6 => {
                if leanh::lean_obj_tag(v___y_5051_) == 0 {
                    leanh::lean_dec_ref_known(v___y_5051_, 1);
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_x_4977_);
                    leanh::lean_dec_ref(v_params_4976_);
                    v_a_5052_ = leanh::lean_ctor_get(v___y_5051_, 0);
                    v_isSharedCheck_5059_ = (!leanh::lean_is_exclusive(v___y_5051_)) as u8;
                    if v_isSharedCheck_5059_ == 0 {
                        v___x_5054_ = v___y_5051_;
                        v_isShared_5055_ = v_isSharedCheck_5059_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5052_);
                        leanh::lean_dec(v___y_5051_);
                        v___x_5054_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5058_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
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
    mut v_params_5078_: *mut leanh::LeanObject,
    mut v_x_5079_: *mut leanh::LeanObject,
    mut v_a_5080_: *mut leanh::LeanObject,
    mut v_a_5081_: *mut leanh::LeanObject,
    mut v_a_5082_: *mut leanh::LeanObject,
    mut v_a_5083_: *mut leanh::LeanObject,
    mut v_a_5084_: *mut leanh::LeanObject,
    mut v_a_5085_: *mut leanh::LeanObject,
    mut v_a_5086_: *mut leanh::LeanObject,
    mut v_a_5087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5086_);
    leanh::lean_dec_ref(v_a_5085_);
    leanh::lean_dec(v_a_5084_);
    leanh::lean_dec_ref(v_a_5083_);
    leanh::lean_dec_ref(v_a_5082_);
    leanh::lean_dec(v_a_5081_);
    leanh::lean_dec_ref(v_a_5080_);
    return v_res_5088_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams(
    mut v_00_u03b1_5089_: *mut leanh::LeanObject,
    mut v_params_5090_: *mut leanh::LeanObject,
    mut v_x_5091_: *mut leanh::LeanObject,
    mut v_a_5092_: *mut leanh::LeanObject,
    mut v_a_5093_: *mut leanh::LeanObject,
    mut v_a_5094_: *mut leanh::LeanObject,
    mut v_a_5095_: *mut leanh::LeanObject,
    mut v_a_5096_: *mut leanh::LeanObject,
    mut v_a_5097_: *mut leanh::LeanObject,
    mut v_a_5098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v_toFunctor_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v___f_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: u8 = 0;
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: usize = 0;
    let mut v___x_5155_: usize = 0;
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: usize = 0;
    let mut v___x_5160_: usize = 0;
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5169_: u8 = 0;
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v___x_5174_: u8 = 0;
    let mut v___f_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: u8 = 0;
    let mut v___x_5178_: usize = 0;
    let mut v___x_5179_: usize = 0;
    let mut v___x_1403__overap_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: usize = 0;
    let mut v___x_5183_: usize = 0;
    let mut v___x_1406__overap_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v_unused_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5190_: u8 = 0;
    let mut v_unused_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5100_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1,
                );
                v_toApplicative_5101_ = leanh::lean_ctor_get(v___x_5100_, 0);
                v_toFunctor_5102_ = leanh::lean_ctor_get(v_toApplicative_5101_, 0);
                v_toSeq_5103_ = leanh::lean_ctor_get(v_toApplicative_5101_, 2);
                v_toSeqLeft_5104_ = leanh::lean_ctor_get(v_toApplicative_5101_, 3);
                v_toSeqRight_5105_ = leanh::lean_ctor_get(v_toApplicative_5101_, 4);
                v___f_5106_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2;
                v___f_5107_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_5102_, 2);
                v___f_5108_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5108_, 0, v_toFunctor_5102_);
                v___f_5109_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5109_, 0, v_toFunctor_5102_);
                v___x_5110_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5110_, 0, v___f_5108_);
                leanh::lean_ctor_set(v___x_5110_, 1, v___f_5109_);
                leanh::lean_inc(v_toSeqRight_5105_);
                v___f_5111_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5111_, 0, v_toSeqRight_5105_);
                leanh::lean_inc(v_toSeqLeft_5104_);
                v___f_5112_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5112_, 0, v_toSeqLeft_5104_);
                leanh::lean_inc(v_toSeq_5103_);
                v___f_5113_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5113_, 0, v_toSeq_5103_);
                v___x_5114_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5114_, 0, v___x_5110_);
                leanh::lean_ctor_set(v___x_5114_, 1, v___f_5106_);
                leanh::lean_ctor_set(v___x_5114_, 2, v___f_5113_);
                leanh::lean_ctor_set(v___x_5114_, 3, v___f_5112_);
                leanh::lean_ctor_set(v___x_5114_, 4, v___f_5111_);
                v___x_5115_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5115_, 0, v___x_5114_);
                leanh::lean_ctor_set(v___x_5115_, 1, v___f_5107_);
                v___x_5116_ = l_StateRefT_x27_instMonad___redArg(v___x_5115_);
                v_toApplicative_5117_ = leanh::lean_ctor_get(v___x_5116_, 0);
                v_isSharedCheck_5190_ = (!leanh::lean_is_exclusive(v___x_5116_)) as u8;
                if v_isSharedCheck_5190_ == 0 {
                    v_unused_5191_ = leanh::lean_ctor_get(v___x_5116_, 1);
                    leanh::lean_dec(v_unused_5191_);
                    v___x_5119_ = v___x_5116_;
                    v_isShared_5120_ = v_isSharedCheck_5190_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_5117_);
                    leanh::lean_dec(v___x_5116_);
                    v___x_5119_ = leanh::lean_box(0);
                    v_isShared_5120_ = v_isSharedCheck_5190_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5121_ = leanh::lean_ctor_get(v_toApplicative_5117_, 0);
                v_toSeq_5122_ = leanh::lean_ctor_get(v_toApplicative_5117_, 2);
                v_toSeqLeft_5123_ = leanh::lean_ctor_get(v_toApplicative_5117_, 3);
                v_toSeqRight_5124_ = leanh::lean_ctor_get(v_toApplicative_5117_, 4);
                v_isSharedCheck_5188_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_5117_)) as u8;
                if v_isSharedCheck_5188_ == 0 {
                    v_unused_5189_ = leanh::lean_ctor_get(v_toApplicative_5117_, 1);
                    leanh::lean_dec(v_unused_5189_);
                    v___x_5126_ = v_toApplicative_5117_;
                    v_isShared_5127_ = v_isSharedCheck_5188_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_5124_);
                    leanh::lean_inc(v_toSeqLeft_5123_);
                    leanh::lean_inc(v_toSeq_5122_);
                    leanh::lean_inc(v_toFunctor_5121_);
                    leanh::lean_dec(v_toApplicative_5117_);
                    v___x_5126_ = leanh::lean_box(0);
                    v_isShared_5127_ = v_isSharedCheck_5188_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5128_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4;
                v___f_5129_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5;
                v___f_5130_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6;
                leanh::lean_inc_ref(v_toFunctor_5121_);
                v___f_5131_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5131_, 0, v_toFunctor_5121_);
                v___f_5132_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5132_, 0, v_toFunctor_5121_);
                v___x_5133_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5133_, 0, v___f_5131_);
                leanh::lean_ctor_set(v___x_5133_, 1, v___f_5132_);
                v___f_5134_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5134_, 0, v_toSeqRight_5124_);
                v___f_5135_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5135_, 0, v_toSeqLeft_5123_);
                v___f_5136_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5136_, 0, v_toSeq_5122_);
                if v_isShared_5127_ == 0 {
                    leanh::lean_ctor_set(v___x_5126_, 4, v___f_5134_);
                    leanh::lean_ctor_set(v___x_5126_, 3, v___f_5135_);
                    leanh::lean_ctor_set(v___x_5126_, 2, v___f_5136_);
                    leanh::lean_ctor_set(v___x_5126_, 1, v___f_5129_);
                    leanh::lean_ctor_set(v___x_5126_, 0, v___x_5133_);
                    v___x_5138_ = v___x_5126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 1, v___f_5129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 2, v___f_5136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 3, v___f_5135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 4, v___f_5134_);
                    v___x_5138_ = v_reuseFailAlloc_5187_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5120_ == 0 {
                    leanh::lean_ctor_set(v___x_5119_, 1, v___f_5130_);
                    leanh::lean_ctor_set(v___x_5119_, 0, v___x_5138_);
                    v___x_5140_ = v___x_5119_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5186_, 1, v___f_5130_);
                    v___x_5140_ = v_reuseFailAlloc_5186_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5141_ = l_ReaderT_instMonad___redArg(v___x_5140_);
                v___x_5142_ = l_StateRefT_x27_instMonad___redArg(v___x_5141_);
                v___x_5143_ = l_ReaderT_instMonad___redArg(v___x_5142_);
                v___x_5144_ = leanh::lean_unsigned_to_nat(0);
                v___x_5145_ = lean_array_get_size(v_params_5090_);
                v___x_5174_ = lean_nat_dec_lt(v___x_5144_, v___x_5145_);
                if v___x_5174_ == 0 {
                    leanh::lean_dec_ref(v___x_5143_);
                    state = 5;
                    continue;
                } else {
                    v___f_5175_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17;
                    v___x_5176_ = leanh::lean_box(0);
                    v___x_5177_ = lean_nat_dec_le(v___x_5145_, v___x_5145_);
                    if v___x_5177_ == 0 {
                        if v___x_5174_ == 0 {
                            leanh::lean_dec_ref(v___x_5143_);
                            state = 5;
                            continue;
                        } else {
                            v___x_5178_ = 0usize;
                            v___x_5179_ = lean_usize_of_nat(v___x_5145_);
                            leanh::lean_inc_ref(v_params_5090_);
                            v___x_1403__overap_5180_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_5143_,
                                    v___f_5175_,
                                    v_params_5090_,
                                    v___x_5178_,
                                    v___x_5179_,
                                    v___x_5176_,
                                );
                            leanh::lean_inc(v_a_5098_);
                            leanh::lean_inc_ref(v_a_5097_);
                            leanh::lean_inc(v_a_5096_);
                            leanh::lean_inc_ref(v_a_5095_);
                            leanh::lean_inc_ref(v_a_5094_);
                            leanh::lean_inc(v_a_5093_);
                            leanh::lean_inc_ref(v_a_5092_);
                            v___x_5181_ = leanh::lean_apply_8(
                                v___x_1403__overap_5180_,
                                v_a_5092_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                leanh::lean_box(0),
                            );
                            v___y_5165_ = v___x_5181_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_5182_ = 0usize;
                        v___x_5183_ = lean_usize_of_nat(v___x_5145_);
                        leanh::lean_inc_ref(v_params_5090_);
                        v___x_1406__overap_5184_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_5143_,
                                v___f_5175_,
                                v_params_5090_,
                                v___x_5182_,
                                v___x_5183_,
                                v___x_5176_,
                            );
                        leanh::lean_inc(v_a_5098_);
                        leanh::lean_inc_ref(v_a_5097_);
                        leanh::lean_inc(v_a_5096_);
                        leanh::lean_inc_ref(v_a_5095_);
                        leanh::lean_inc_ref(v_a_5094_);
                        leanh::lean_inc(v_a_5093_);
                        leanh::lean_inc_ref(v_a_5092_);
                        v___x_5185_ = leanh::lean_apply_8(
                            v___x_1406__overap_5184_,
                            v_a_5092_,
                            v_a_5093_,
                            v_a_5094_,
                            v_a_5095_,
                            v_a_5096_,
                            v_a_5097_,
                            v_a_5098_,
                            leanh::lean_box(0),
                        );
                        v___y_5165_ = v___x_5185_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_jps_5147_ = leanh::lean_ctor_get(v_a_5092_, 0);
                v_vars_5148_ = leanh::lean_ctor_get(v_a_5092_, 1);
                v___x_5149_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16;
                v___x_5150_ = lean_nat_dec_lt(v___x_5144_, v___x_5145_);
                if v___x_5150_ == 0 {
                    leanh::lean_dec_ref(v_params_5090_);
                    leanh::lean_inc(v_a_5098_);
                    leanh::lean_inc_ref(v_a_5097_);
                    leanh::lean_inc(v_a_5096_);
                    leanh::lean_inc_ref(v_a_5095_);
                    leanh::lean_inc_ref(v_a_5094_);
                    leanh::lean_inc(v_a_5093_);
                    leanh::lean_inc_ref(v_a_5092_);
                    v___x_5151_ = leanh::lean_apply_8(
                        v_x_5091_,
                        v_a_5092_,
                        v_a_5093_,
                        v_a_5094_,
                        v_a_5095_,
                        v_a_5096_,
                        v_a_5097_,
                        v_a_5098_,
                        leanh::lean_box(0),
                    );
                    return v___x_5151_;
                } else {
                    v___x_5152_ = lean_nat_dec_le(v___x_5145_, v___x_5145_);
                    if v___x_5152_ == 0 {
                        if v___x_5150_ == 0 {
                            leanh::lean_dec_ref(v_params_5090_);
                            leanh::lean_inc(v_a_5098_);
                            leanh::lean_inc_ref(v_a_5097_);
                            leanh::lean_inc(v_a_5096_);
                            leanh::lean_inc_ref(v_a_5095_);
                            leanh::lean_inc_ref(v_a_5094_);
                            leanh::lean_inc(v_a_5093_);
                            leanh::lean_inc_ref(v_a_5092_);
                            v___x_5153_ = leanh::lean_apply_8(
                                v_x_5091_,
                                v_a_5092_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                leanh::lean_box(0),
                            );
                            return v___x_5153_;
                        } else {
                            v___x_5154_ = 0usize;
                            v___x_5155_ = lean_usize_of_nat(v___x_5145_);
                            leanh::lean_inc(v_vars_5148_);
                            v___x_5156_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_5149_,
                                    v___f_5128_,
                                    v_params_5090_,
                                    v___x_5154_,
                                    v___x_5155_,
                                    v_vars_5148_,
                                );
                            leanh::lean_inc(v_jps_5147_);
                            v___x_5157_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5157_, 0, v_jps_5147_);
                            leanh::lean_ctor_set(v___x_5157_, 1, v___x_5156_);
                            leanh::lean_inc(v_a_5098_);
                            leanh::lean_inc_ref(v_a_5097_);
                            leanh::lean_inc(v_a_5096_);
                            leanh::lean_inc_ref(v_a_5095_);
                            leanh::lean_inc_ref(v_a_5094_);
                            leanh::lean_inc(v_a_5093_);
                            v___x_5158_ = leanh::lean_apply_8(
                                v_x_5091_,
                                v___x_5157_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                leanh::lean_box(0),
                            );
                            return v___x_5158_;
                        }
                    } else {
                        v___x_5159_ = 0usize;
                        v___x_5160_ = lean_usize_of_nat(v___x_5145_);
                        leanh::lean_inc(v_vars_5148_);
                        v___x_5161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_5149_,
                            v___f_5128_,
                            v_params_5090_,
                            v___x_5159_,
                            v___x_5160_,
                            v_vars_5148_,
                        );
                        leanh::lean_inc(v_jps_5147_);
                        v___x_5162_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5162_, 0, v_jps_5147_);
                        leanh::lean_ctor_set(v___x_5162_, 1, v___x_5161_);
                        leanh::lean_inc(v_a_5098_);
                        leanh::lean_inc_ref(v_a_5097_);
                        leanh::lean_inc(v_a_5096_);
                        leanh::lean_inc_ref(v_a_5095_);
                        leanh::lean_inc_ref(v_a_5094_);
                        leanh::lean_inc(v_a_5093_);
                        v___x_5163_ = leanh::lean_apply_8(
                            v_x_5091_,
                            v___x_5162_,
                            v_a_5093_,
                            v_a_5094_,
                            v_a_5095_,
                            v_a_5096_,
                            v_a_5097_,
                            v_a_5098_,
                            leanh::lean_box(0),
                        );
                        return v___x_5163_;
                    }
                }
            }
            6 => {
                if leanh::lean_obj_tag(v___y_5165_) == 0 {
                    leanh::lean_dec_ref_known(v___y_5165_, 1);
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_x_5091_);
                    leanh::lean_dec_ref(v_params_5090_);
                    v_a_5166_ = leanh::lean_ctor_get(v___y_5165_, 0);
                    v_isSharedCheck_5173_ = (!leanh::lean_is_exclusive(v___y_5165_)) as u8;
                    if v_isSharedCheck_5173_ == 0 {
                        v___x_5168_ = v___y_5165_;
                        v_isShared_5169_ = v_isSharedCheck_5173_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5166_);
                        leanh::lean_dec(v___y_5165_);
                        v___x_5168_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5172_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
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
    mut v_00_u03b1_5192_: *mut leanh::LeanObject,
    mut v_params_5193_: *mut leanh::LeanObject,
    mut v_x_5194_: *mut leanh::LeanObject,
    mut v_a_5195_: *mut leanh::LeanObject,
    mut v_a_5196_: *mut leanh::LeanObject,
    mut v_a_5197_: *mut leanh::LeanObject,
    mut v_a_5198_: *mut leanh::LeanObject,
    mut v_a_5199_: *mut leanh::LeanObject,
    mut v_a_5200_: *mut leanh::LeanObject,
    mut v_a_5201_: *mut leanh::LeanObject,
    mut v_a_5202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5201_);
    leanh::lean_dec_ref(v_a_5200_);
    leanh::lean_dec(v_a_5199_);
    leanh::lean_dec_ref(v_a_5198_);
    leanh::lean_dec_ref(v_a_5197_);
    leanh::lean_dec(v_a_5196_);
    leanh::lean_dec_ref(v_a_5195_);
    return v_res_5203_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(
    mut v_ref_5204_: *mut leanh::LeanObject,
    mut v_msg_5205_: *mut leanh::LeanObject,
    mut v___y_5206_: *mut leanh::LeanObject,
    mut v___y_5207_: *mut leanh::LeanObject,
    mut v___y_5208_: *mut leanh::LeanObject,
    mut v___y_5209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5223_: u8 = 0;
    let mut v_cancelTk_x3f_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5225_: u8 = 0;
    let mut v_inheritedTraceOptions_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5211_ = leanh::lean_ctor_get(v___y_5208_, 0);
    v_fileMap_5212_ = leanh::lean_ctor_get(v___y_5208_, 1);
    v_options_5213_ = leanh::lean_ctor_get(v___y_5208_, 2);
    v_currRecDepth_5214_ = leanh::lean_ctor_get(v___y_5208_, 3);
    v_maxRecDepth_5215_ = leanh::lean_ctor_get(v___y_5208_, 4);
    v_ref_5216_ = leanh::lean_ctor_get(v___y_5208_, 5);
    v_currNamespace_5217_ = leanh::lean_ctor_get(v___y_5208_, 6);
    v_openDecls_5218_ = leanh::lean_ctor_get(v___y_5208_, 7);
    v_initHeartbeats_5219_ = leanh::lean_ctor_get(v___y_5208_, 8);
    v_maxHeartbeats_5220_ = leanh::lean_ctor_get(v___y_5208_, 9);
    v_quotContext_5221_ = leanh::lean_ctor_get(v___y_5208_, 10);
    v_currMacroScope_5222_ = leanh::lean_ctor_get(v___y_5208_, 11);
    v_diag_5223_ = leanh::lean_ctor_get_uint8(
        v___y_5208_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5224_ = leanh::lean_ctor_get(v___y_5208_, 12);
    v_suppressElabErrors_5225_ = leanh::lean_ctor_get_uint8(
        v___y_5208_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5226_ = leanh::lean_ctor_get(v___y_5208_, 13);
    v_ref_5227_ = l_Lean_replaceRef(v_ref_5204_, v_ref_5216_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_5226_);
    leanh::lean_inc(v_cancelTk_x3f_5224_);
    leanh::lean_inc(v_currMacroScope_5222_);
    leanh::lean_inc(v_quotContext_5221_);
    leanh::lean_inc(v_maxHeartbeats_5220_);
    leanh::lean_inc(v_initHeartbeats_5219_);
    leanh::lean_inc(v_openDecls_5218_);
    leanh::lean_inc(v_currNamespace_5217_);
    leanh::lean_inc(v_maxRecDepth_5215_);
    leanh::lean_inc(v_currRecDepth_5214_);
    leanh::lean_inc_ref(v_options_5213_);
    leanh::lean_inc_ref(v_fileMap_5212_);
    leanh::lean_inc_ref(v_fileName_5211_);
    v___x_5228_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_5228_, 0, v_fileName_5211_);
    leanh::lean_ctor_set(v___x_5228_, 1, v_fileMap_5212_);
    leanh::lean_ctor_set(v___x_5228_, 2, v_options_5213_);
    leanh::lean_ctor_set(v___x_5228_, 3, v_currRecDepth_5214_);
    leanh::lean_ctor_set(v___x_5228_, 4, v_maxRecDepth_5215_);
    leanh::lean_ctor_set(v___x_5228_, 5, v_ref_5227_);
    leanh::lean_ctor_set(v___x_5228_, 6, v_currNamespace_5217_);
    leanh::lean_ctor_set(v___x_5228_, 7, v_openDecls_5218_);
    leanh::lean_ctor_set(v___x_5228_, 8, v_initHeartbeats_5219_);
    leanh::lean_ctor_set(v___x_5228_, 9, v_maxHeartbeats_5220_);
    leanh::lean_ctor_set(v___x_5228_, 10, v_quotContext_5221_);
    leanh::lean_ctor_set(v___x_5228_, 11, v_currMacroScope_5222_);
    leanh::lean_ctor_set(v___x_5228_, 12, v_cancelTk_x3f_5224_);
    leanh::lean_ctor_set(v___x_5228_, 13, v_inheritedTraceOptions_5226_);
    leanh::lean_ctor_set_uint8(
        v___x_5228_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_5223_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_5228_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
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
    leanh::lean_dec_ref_known(v___x_5228_, 14);
    return v___x_5229_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg___boxed(
    mut v_ref_5230_: *mut leanh::LeanObject,
    mut v_msg_5231_: *mut leanh::LeanObject,
    mut v___y_5232_: *mut leanh::LeanObject,
    mut v___y_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5237_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_5230_, v_msg_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
    leanh::lean_dec(v___y_5235_);
    leanh::lean_dec_ref(v___y_5234_);
    leanh::lean_dec(v___y_5233_);
    leanh::lean_dec_ref(v___y_5232_);
    leanh::lean_dec(v_ref_5230_);
    return v_res_5237_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(
    mut v_msg_5238_: *mut leanh::LeanObject,
    mut v_declHint_5239_: *mut leanh::LeanObject,
    mut v___y_5240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: u8 = 0;
    let mut v_isExporting_5245_: u8 = 0;
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u8 = 0;
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: u8 = 0;
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5242_ = lean_st_ref_get(v___y_5240_);
                v_env_5243_ = leanh::lean_ctor_get(v___x_5242_, 0);
                leanh::lean_inc_ref(v_env_5243_);
                leanh::lean_dec(v___x_5242_);
                v___x_5244_ = l_Lean_Name_isAnonymous(v_declHint_5239_);
                if v___x_5244_ == 0 {
                    v_isExporting_5245_ = leanh::lean_ctor_get_uint8(
                        v_env_5243_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5245_ == 0 {
                        leanh::lean_dec_ref(v_env_5243_);
                        leanh::lean_dec(v_declHint_5239_);
                        v___x_5246_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5246_, 0, v_msg_5238_);
                        return v___x_5246_;
                    } else {
                        leanh::lean_inc_ref(v_env_5243_);
                        v___x_5247_ = l_Lean_Environment_setExporting(v_env_5243_, v___x_5244_);
                        leanh::lean_inc(v_declHint_5239_);
                        leanh::lean_inc_ref(v___x_5247_);
                        v___x_5248_ = l_Lean_Environment_contains(
                            v___x_5247_,
                            v_declHint_5239_,
                            v_isExporting_5245_,
                        );
                        if v___x_5248_ == 0 {
                            leanh::lean_dec_ref(v___x_5247_);
                            leanh::lean_dec_ref(v_env_5243_);
                            leanh::lean_dec(v_declHint_5239_);
                            v___x_5249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5249_, 0, v_msg_5238_);
                            return v___x_5249_;
                        } else {
                            v___x_5250_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                            v___x_5251_ = leanh::lean_unsigned_to_nat(32);
                            v___x_5252_ = lean_mk_empty_array_with_capacity(v___x_5251_);
                            leanh::lean_dec_ref(v___x_5252_);
                            v___x_5253_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_5254_ = l_Lean_Options_empty;
                            v___x_5255_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_5255_, 0, v___x_5247_);
                            leanh::lean_ctor_set(v___x_5255_, 1, v___x_5250_);
                            leanh::lean_ctor_set(v___x_5255_, 2, v___x_5253_);
                            leanh::lean_ctor_set(v___x_5255_, 3, v___x_5254_);
                            leanh::lean_inc(v_declHint_5239_);
                            v___x_5256_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5239_, v___x_5244_);
                            v_c_5257_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_5257_, 0, v___x_5255_);
                            leanh::lean_ctor_set(v_c_5257_, 1, v___x_5256_);
                            v___x_5258_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5243_,
                                v_declHint_5239_,
                            );
                            if leanh::lean_obj_tag(v___x_5258_) == 0 {
                                leanh::lean_dec_ref(v_env_5243_);
                                leanh::lean_dec(v_declHint_5239_);
                                v___x_5259_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_5260_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5260_, 0, v___x_5259_);
                                leanh::lean_ctor_set(v___x_5260_, 1, v_c_5257_);
                                v___x_5261_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_5262_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5262_, 0, v___x_5260_);
                                leanh::lean_ctor_set(v___x_5262_, 1, v___x_5261_);
                                v___x_5263_ = l_Lean_MessageData_note(v___x_5262_);
                                v___x_5264_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5264_, 0, v_msg_5238_);
                                leanh::lean_ctor_set(v___x_5264_, 1, v___x_5263_);
                                v___x_5265_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_5265_, 0, v___x_5264_);
                                return v___x_5265_;
                            } else {
                                v_val_5266_ = leanh::lean_ctor_get(v___x_5258_, 0);
                                v_isSharedCheck_5301_ =
                                    (!leanh::lean_is_exclusive(v___x_5258_)) as u8;
                                if v_isSharedCheck_5301_ == 0 {
                                    v___x_5268_ = v___x_5258_;
                                    v_isShared_5269_ = v_isSharedCheck_5301_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_5266_);
                                    leanh::lean_dec(v___x_5258_);
                                    v___x_5268_ = leanh::lean_box(0);
                                    v_isShared_5269_ = v_isSharedCheck_5301_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_5243_);
                    leanh::lean_dec(v_declHint_5239_);
                    v___x_5302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5302_, 0, v_msg_5238_);
                    return v___x_5302_;
                }
            }
            1 => {
                v___x_5270_ = leanh::lean_box(0);
                v___x_5271_ = l_Lean_Environment_header(v_env_5243_);
                leanh::lean_dec_ref(v_env_5243_);
                v___x_5272_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5271_);
                v_mod_5273_ = lean_array_get(v___x_5270_, v___x_5272_, v_val_5266_);
                leanh::lean_dec(v_val_5266_);
                leanh::lean_dec_ref(v___x_5272_);
                v___x_5274_ = l_Lean_isPrivateName(v_declHint_5239_);
                leanh::lean_dec(v_declHint_5239_);
                if v___x_5274_ == 0 {
                    v___x_5275_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_5276_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5276_, 0, v___x_5275_);
                    leanh::lean_ctor_set(v___x_5276_, 1, v_c_5257_);
                    v___x_5277_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_5278_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5278_, 0, v___x_5276_);
                    leanh::lean_ctor_set(v___x_5278_, 1, v___x_5277_);
                    v___x_5279_ = l_Lean_MessageData_ofName(v_mod_5273_);
                    v___x_5280_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5280_, 0, v___x_5278_);
                    leanh::lean_ctor_set(v___x_5280_, 1, v___x_5279_);
                    v___x_5281_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_5282_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5282_, 0, v___x_5280_);
                    leanh::lean_ctor_set(v___x_5282_, 1, v___x_5281_);
                    v___x_5283_ = l_Lean_MessageData_note(v___x_5282_);
                    v___x_5284_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5284_, 0, v_msg_5238_);
                    leanh::lean_ctor_set(v___x_5284_, 1, v___x_5283_);
                    if v_isShared_5269_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5268_, 0);
                        leanh::lean_ctor_set(v___x_5268_, 0, v___x_5284_);
                        v___x_5286_ = v___x_5268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5284_);
                        v___x_5286_ = v_reuseFailAlloc_5287_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5288_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_5289_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5289_, 0, v___x_5288_);
                    leanh::lean_ctor_set(v___x_5289_, 1, v_c_5257_);
                    v___x_5290_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_5291_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5291_, 0, v___x_5289_);
                    leanh::lean_ctor_set(v___x_5291_, 1, v___x_5290_);
                    v___x_5292_ = l_Lean_MessageData_ofName(v_mod_5273_);
                    v___x_5293_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5293_, 0, v___x_5291_);
                    leanh::lean_ctor_set(v___x_5293_, 1, v___x_5292_);
                    v___x_5294_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_5295_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5295_, 0, v___x_5293_);
                    leanh::lean_ctor_set(v___x_5295_, 1, v___x_5294_);
                    v___x_5296_ = l_Lean_MessageData_note(v___x_5295_);
                    v___x_5297_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5297_, 0, v_msg_5238_);
                    leanh::lean_ctor_set(v___x_5297_, 1, v___x_5296_);
                    if v_isShared_5269_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5268_, 0);
                        leanh::lean_ctor_set(v___x_5268_, 0, v___x_5297_);
                        v___x_5299_ = v___x_5268_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5300_, 0, v___x_5297_);
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
    mut v_msg_5303_: *mut leanh::LeanObject,
    mut v_declHint_5304_: *mut leanh::LeanObject,
    mut v___y_5305_: *mut leanh::LeanObject,
    mut v___y_5306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_5303_, v_declHint_5304_, v___y_5305_);
    leanh::lean_dec(v___y_5305_);
    return v_res_5307_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(
    mut v_msg_5308_: *mut leanh::LeanObject,
    mut v_declHint_5309_: *mut leanh::LeanObject,
    mut v___y_5310_: *mut leanh::LeanObject,
    mut v___y_5311_: *mut leanh::LeanObject,
    mut v___y_5312_: *mut leanh::LeanObject,
    mut v___y_5313_: *mut leanh::LeanObject,
    mut v___y_5314_: *mut leanh::LeanObject,
    mut v___y_5315_: *mut leanh::LeanObject,
    mut v___y_5316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5318_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_5308_, v_declHint_5309_, v___y_5316_);
                v_a_5319_ = leanh::lean_ctor_get(v___x_5318_, 0);
                v_isSharedCheck_5328_ = (!leanh::lean_is_exclusive(v___x_5318_)) as u8;
                if v_isSharedCheck_5328_ == 0 {
                    v___x_5321_ = v___x_5318_;
                    v_isShared_5322_ = v_isSharedCheck_5328_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5319_);
                    leanh::lean_dec(v___x_5318_);
                    v___x_5321_ = leanh::lean_box(0);
                    v_isShared_5322_ = v_isSharedCheck_5328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5323_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5324_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5324_, 0, v___x_5323_);
                leanh::lean_ctor_set(v___x_5324_, 1, v_a_5319_);
                if v_isShared_5322_ == 0 {
                    leanh::lean_ctor_set(v___x_5321_, 0, v___x_5324_);
                    v___x_5326_ = v___x_5321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
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
    mut v_msg_5329_: *mut leanh::LeanObject,
    mut v_declHint_5330_: *mut leanh::LeanObject,
    mut v___y_5331_: *mut leanh::LeanObject,
    mut v___y_5332_: *mut leanh::LeanObject,
    mut v___y_5333_: *mut leanh::LeanObject,
    mut v___y_5334_: *mut leanh::LeanObject,
    mut v___y_5335_: *mut leanh::LeanObject,
    mut v___y_5336_: *mut leanh::LeanObject,
    mut v___y_5337_: *mut leanh::LeanObject,
    mut v___y_5338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5339_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(v_msg_5329_, v_declHint_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
    leanh::lean_dec(v___y_5337_);
    leanh::lean_dec_ref(v___y_5336_);
    leanh::lean_dec(v___y_5335_);
    leanh::lean_dec_ref(v___y_5334_);
    leanh::lean_dec_ref(v___y_5333_);
    leanh::lean_dec(v___y_5332_);
    leanh::lean_dec_ref(v___y_5331_);
    return v_res_5339_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(
    mut v_ref_5340_: *mut leanh::LeanObject,
    mut v_msg_5341_: *mut leanh::LeanObject,
    mut v_declHint_5342_: *mut leanh::LeanObject,
    mut v___y_5343_: *mut leanh::LeanObject,
    mut v___y_5344_: *mut leanh::LeanObject,
    mut v___y_5345_: *mut leanh::LeanObject,
    mut v___y_5346_: *mut leanh::LeanObject,
    mut v___y_5347_: *mut leanh::LeanObject,
    mut v___y_5348_: *mut leanh::LeanObject,
    mut v___y_5349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5351_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(v_msg_5341_, v_declHint_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
    v_a_5352_ = leanh::lean_ctor_get(v___x_5351_, 0);
    leanh::lean_inc(v_a_5352_);
    leanh::lean_dec_ref(v___x_5351_);
    v___x_5353_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_5340_, v_a_5352_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
    return v___x_5353_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_ref_5354_: *mut leanh::LeanObject,
    mut v_msg_5355_: *mut leanh::LeanObject,
    mut v_declHint_5356_: *mut leanh::LeanObject,
    mut v___y_5357_: *mut leanh::LeanObject,
    mut v___y_5358_: *mut leanh::LeanObject,
    mut v___y_5359_: *mut leanh::LeanObject,
    mut v___y_5360_: *mut leanh::LeanObject,
    mut v___y_5361_: *mut leanh::LeanObject,
    mut v___y_5362_: *mut leanh::LeanObject,
    mut v___y_5363_: *mut leanh::LeanObject,
    mut v___y_5364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5365_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_5354_, v_msg_5355_, v_declHint_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
    leanh::lean_dec(v___y_5363_);
    leanh::lean_dec_ref(v___y_5362_);
    leanh::lean_dec(v___y_5361_);
    leanh::lean_dec_ref(v___y_5360_);
    leanh::lean_dec_ref(v___y_5359_);
    leanh::lean_dec(v___y_5358_);
    leanh::lean_dec_ref(v___y_5357_);
    leanh::lean_dec(v_ref_5354_);
    return v_res_5365_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(
    mut v_ref_5366_: *mut leanh::LeanObject,
    mut v_constName_5367_: *mut leanh::LeanObject,
    mut v___y_5368_: *mut leanh::LeanObject,
    mut v___y_5369_: *mut leanh::LeanObject,
    mut v___y_5370_: *mut leanh::LeanObject,
    mut v___y_5371_: *mut leanh::LeanObject,
    mut v___y_5372_: *mut leanh::LeanObject,
    mut v___y_5373_: *mut leanh::LeanObject,
    mut v___y_5374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5376_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_5377_ = 0;
    leanh::lean_inc(v_constName_5367_);
    v___x_5378_ = l_Lean_MessageData_ofConstName(v_constName_5367_, v___x_5377_);
    v___x_5379_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5379_, 0, v___x_5376_);
    leanh::lean_ctor_set(v___x_5379_, 1, v___x_5378_);
    v___x_5380_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_5381_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5381_, 0, v___x_5379_);
    leanh::lean_ctor_set(v___x_5381_, 1, v___x_5380_);
    v___x_5382_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_5366_, v___x_5381_, v_constName_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
    return v___x_5382_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg___boxed(
    mut v_ref_5383_: *mut leanh::LeanObject,
    mut v_constName_5384_: *mut leanh::LeanObject,
    mut v___y_5385_: *mut leanh::LeanObject,
    mut v___y_5386_: *mut leanh::LeanObject,
    mut v___y_5387_: *mut leanh::LeanObject,
    mut v___y_5388_: *mut leanh::LeanObject,
    mut v___y_5389_: *mut leanh::LeanObject,
    mut v___y_5390_: *mut leanh::LeanObject,
    mut v___y_5391_: *mut leanh::LeanObject,
    mut v___y_5392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5393_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_5383_, v_constName_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
    leanh::lean_dec(v___y_5391_);
    leanh::lean_dec_ref(v___y_5390_);
    leanh::lean_dec(v___y_5389_);
    leanh::lean_dec_ref(v___y_5388_);
    leanh::lean_dec_ref(v___y_5387_);
    leanh::lean_dec(v___y_5386_);
    leanh::lean_dec_ref(v___y_5385_);
    leanh::lean_dec(v_ref_5383_);
    return v_res_5393_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(
    mut v_constName_5394_: *mut leanh::LeanObject,
    mut v___y_5395_: *mut leanh::LeanObject,
    mut v___y_5396_: *mut leanh::LeanObject,
    mut v___y_5397_: *mut leanh::LeanObject,
    mut v___y_5398_: *mut leanh::LeanObject,
    mut v___y_5399_: *mut leanh::LeanObject,
    mut v___y_5400_: *mut leanh::LeanObject,
    mut v___y_5401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_5403_ = leanh::lean_ctor_get(v___y_5400_, 5);
    v___x_5404_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_5403_, v_constName_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
    return v___x_5404_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg___boxed(
    mut v_constName_5405_: *mut leanh::LeanObject,
    mut v___y_5406_: *mut leanh::LeanObject,
    mut v___y_5407_: *mut leanh::LeanObject,
    mut v___y_5408_: *mut leanh::LeanObject,
    mut v___y_5409_: *mut leanh::LeanObject,
    mut v___y_5410_: *mut leanh::LeanObject,
    mut v___y_5411_: *mut leanh::LeanObject,
    mut v___y_5412_: *mut leanh::LeanObject,
    mut v___y_5413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_);
    leanh::lean_dec(v___y_5412_);
    leanh::lean_dec_ref(v___y_5411_);
    leanh::lean_dec(v___y_5410_);
    leanh::lean_dec_ref(v___y_5409_);
    leanh::lean_dec_ref(v___y_5408_);
    leanh::lean_dec(v___y_5407_);
    leanh::lean_dec_ref(v___y_5406_);
    return v_res_5414_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(
    mut v_constName_5415_: *mut leanh::LeanObject,
    mut v___y_5416_: *mut leanh::LeanObject,
    mut v___y_5417_: *mut leanh::LeanObject,
    mut v___y_5418_: *mut leanh::LeanObject,
    mut v___y_5419_: *mut leanh::LeanObject,
    mut v___y_5420_: *mut leanh::LeanObject,
    mut v___y_5421_: *mut leanh::LeanObject,
    mut v___y_5422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: u8 = 0;
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___x_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5424_ = lean_st_ref_get(v___y_5422_);
                v_env_5425_ = leanh::lean_ctor_get(v___x_5424_, 0);
                leanh::lean_inc_ref(v_env_5425_);
                leanh::lean_dec(v___x_5424_);
                v___x_5426_ = 0;
                leanh::lean_inc(v_constName_5415_);
                v___x_5427_ =
                    l_Lean_Environment_find_x3f(v_env_5425_, v_constName_5415_, v___x_5426_);
                if leanh::lean_obj_tag(v___x_5427_) == 0 {
                    v___x_5428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
                    return v___x_5428_;
                } else {
                    leanh::lean_dec(v_constName_5415_);
                    v_val_5429_ = leanh::lean_ctor_get(v___x_5427_, 0);
                    v_isSharedCheck_5436_ = (!leanh::lean_is_exclusive(v___x_5427_)) as u8;
                    if v_isSharedCheck_5436_ == 0 {
                        v___x_5431_ = v___x_5427_;
                        v_isShared_5432_ = v_isSharedCheck_5436_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5429_);
                        leanh::lean_dec(v___x_5427_);
                        v___x_5431_ = leanh::lean_box(0);
                        v_isShared_5432_ = v_isSharedCheck_5436_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5432_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5431_, 0);
                    v___x_5434_ = v___x_5431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_val_5429_);
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
    mut v_constName_5437_: *mut leanh::LeanObject,
    mut v___y_5438_: *mut leanh::LeanObject,
    mut v___y_5439_: *mut leanh::LeanObject,
    mut v___y_5440_: *mut leanh::LeanObject,
    mut v___y_5441_: *mut leanh::LeanObject,
    mut v___y_5442_: *mut leanh::LeanObject,
    mut v___y_5443_: *mut leanh::LeanObject,
    mut v___y_5444_: *mut leanh::LeanObject,
    mut v___y_5445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_5444_);
    leanh::lean_dec_ref(v___y_5443_);
    leanh::lean_dec(v___y_5442_);
    leanh::lean_dec_ref(v___y_5441_);
    leanh::lean_dec_ref(v___y_5440_);
    leanh::lean_dec(v___y_5439_);
    leanh::lean_dec_ref(v___y_5438_);
    return v_res_5446_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(
    mut v_as_5447_: *mut leanh::LeanObject,
    mut v_i_5448_: usize,
    mut v_stop_5449_: usize,
    mut v_b_5450_: *mut leanh::LeanObject,
    mut v___y_5451_: *mut leanh::LeanObject,
    mut v___y_5452_: *mut leanh::LeanObject,
    mut v___y_5453_: *mut leanh::LeanObject,
    mut v___y_5454_: *mut leanh::LeanObject,
    mut v___y_5455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5457_: u8 = 0;
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: usize = 0;
    let mut v___x_5463_: usize = 0;
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5457_ = lean_usize_dec_eq(v_i_5448_, v_stop_5449_);
                if v___x_5457_ == 0 {
                    v___x_5458_ = lean_array_uget_borrowed(v_as_5447_, v_i_5448_);
                    v_fvarId_5459_ = leanh::lean_ctor_get(v___x_5458_, 0);
                    leanh::lean_inc(v_fvarId_5459_);
                    v___x_5460_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_5459_,
                        v___y_5451_,
                        v___y_5452_,
                        v___y_5453_,
                        v___y_5454_,
                        v___y_5455_,
                    );
                    if leanh::lean_obj_tag(v___x_5460_) == 0 {
                        v_a_5461_ = leanh::lean_ctor_get(v___x_5460_, 0);
                        leanh::lean_inc(v_a_5461_);
                        leanh::lean_dec_ref_known(v___x_5460_, 1);
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
                    v___x_5465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5465_, 0, v_b_5450_);
                    return v___x_5465_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg___boxed(
    mut v_as_5466_: *mut leanh::LeanObject,
    mut v_i_5467_: *mut leanh::LeanObject,
    mut v_stop_5468_: *mut leanh::LeanObject,
    mut v_b_5469_: *mut leanh::LeanObject,
    mut v___y_5470_: *mut leanh::LeanObject,
    mut v___y_5471_: *mut leanh::LeanObject,
    mut v___y_5472_: *mut leanh::LeanObject,
    mut v___y_5473_: *mut leanh::LeanObject,
    mut v___y_5474_: *mut leanh::LeanObject,
    mut v___y_5475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5476_: usize = 0;
    let mut v_stop_boxed_5477_: usize = 0;
    let mut v_res_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5476_ = leanh::lean_unbox_usize(v_i_5467_);
    leanh::lean_dec(v_i_5467_);
    v_stop_boxed_5477_ = leanh::lean_unbox_usize(v_stop_5468_);
    leanh::lean_dec(v_stop_5468_);
    v_res_5478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_as_5466_, v_i_boxed_5476_, v_stop_boxed_5477_, v_b_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_);
    leanh::lean_dec(v___y_5474_);
    leanh::lean_dec_ref(v___y_5473_);
    leanh::lean_dec(v___y_5472_);
    leanh::lean_dec_ref(v___y_5471_);
    leanh::lean_dec(v___y_5470_);
    leanh::lean_dec_ref(v_as_5466_);
    return v_res_5478_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(
    mut v_as_5479_: *mut leanh::LeanObject,
    mut v_i_5480_: usize,
    mut v_stop_5481_: usize,
    mut v_b_5482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: usize = 0;
    let mut v___x_5488_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5483_ = lean_usize_dec_eq(v_i_5480_, v_stop_5481_);
                if v___x_5483_ == 0 {
                    v___x_5484_ = lean_array_uget_borrowed(v_as_5479_, v_i_5480_);
                    v_fvarId_5485_ = leanh::lean_ctor_get(v___x_5484_, 0);
                    leanh::lean_inc(v_fvarId_5485_);
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
    mut v_as_5490_: *mut leanh::LeanObject,
    mut v_i_5491_: *mut leanh::LeanObject,
    mut v_stop_5492_: *mut leanh::LeanObject,
    mut v_b_5493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5494_: usize = 0;
    let mut v_stop_boxed_5495_: usize = 0;
    let mut v_res_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5494_ = leanh::lean_unbox_usize(v_i_5491_);
    leanh::lean_dec(v_i_5491_);
    v_stop_boxed_5495_ = leanh::lean_unbox_usize(v_stop_5492_);
    leanh::lean_dec(v_stop_5492_);
    v_res_5496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_as_5490_, v_i_boxed_5494_, v_stop_boxed_5495_, v_b_5493_);
    leanh::lean_dec_ref(v_as_5490_);
    return v_res_5496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(
    mut v_declName_5498_: *mut leanh::LeanObject,
    mut v_params_5499_: *mut leanh::LeanObject,
    mut v_type_5500_: *mut leanh::LeanObject,
    mut v_value_5501_: *mut leanh::LeanObject,
    mut v_a_5502_: *mut leanh::LeanObject,
    mut v_a_5503_: *mut leanh::LeanObject,
    mut v_a_5504_: *mut leanh::LeanObject,
    mut v_a_5505_: *mut leanh::LeanObject,
    mut v_a_5506_: *mut leanh::LeanObject,
    mut v_a_5507_: *mut leanh::LeanObject,
    mut v_a_5508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5520_: u8 = 0;
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: u8 = 0;
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5536_: u8 = 0;
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5554_: u8 = 0;
    let mut v_a_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5558_: u8 = 0;
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5562_: u8 = 0;
    let mut v_a_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5570_: u8 = 0;
    let mut v_a_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_a_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: u8 = 0;
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5610_: u8 = 0;
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: u8 = 0;
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5627_: u8 = 0;
    let mut v_a_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5643_: u8 = 0;
    let mut v_a_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5647_: u8 = 0;
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_a_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5656_: u8 = 0;
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: usize = 0;
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: usize = 0;
    let mut v___x_5676_: usize = 0;
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: u8 = 0;
    let mut v___x_5683_: u8 = 0;
    let mut v___x_5684_: usize = 0;
    let mut v___x_5685_: usize = 0;
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: usize = 0;
    let mut v___x_5688_: usize = 0;
    let mut v___x_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5588_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5588_, 1);
                    v___x_5589_ = leanh::lean_box(0);
                    v___x_5661_ = leanh::lean_unsigned_to_nat(0);
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
                    leanh::lean_dec_ref(v_value_5501_);
                    leanh::lean_dec_ref(v_type_5500_);
                    leanh::lean_dec_ref(v_params_5499_);
                    leanh::lean_dec(v_declName_5498_);
                    return v___x_5588_;
                }
            }
            1 => {
                v___x_5516_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v___y_5512_);
                if leanh::lean_obj_tag(v___x_5516_) == 0 {
                    v_a_5517_ = leanh::lean_ctor_get(v___x_5516_, 0);
                    v_isSharedCheck_5579_ = (!leanh::lean_is_exclusive(v___x_5516_)) as u8;
                    if v_isSharedCheck_5579_ == 0 {
                        v___x_5519_ = v___x_5516_;
                        v_isShared_5520_ = v_isSharedCheck_5579_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5517_);
                        leanh::lean_dec(v___x_5516_);
                        v___x_5519_ = leanh::lean_box(0);
                        v_isShared_5520_ = v_isSharedCheck_5579_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_value_5501_);
                    leanh::lean_dec_ref(v_type_5500_);
                    leanh::lean_dec_ref(v_params_5499_);
                    leanh::lean_dec(v_declName_5498_);
                    v_a_5580_ = leanh::lean_ctor_get(v___x_5516_, 0);
                    v_isSharedCheck_5587_ = (!leanh::lean_is_exclusive(v___x_5516_)) as u8;
                    if v_isSharedCheck_5587_ == 0 {
                        v___x_5582_ = v___x_5516_;
                        v_isShared_5583_ = v_isSharedCheck_5587_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5580_);
                        leanh::lean_dec(v___x_5516_);
                        v___x_5582_ = leanh::lean_box(0);
                        v_isShared_5583_ = v_isSharedCheck_5587_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5521_ = (leanh::lean_unbox(v_a_5517_) as u8);
                leanh::lean_dec(v_a_5517_);
                if v___x_5521_ == 0 {
                    leanh::lean_dec_ref(v_value_5501_);
                    leanh::lean_dec_ref(v_type_5500_);
                    leanh::lean_dec_ref(v_params_5499_);
                    leanh::lean_dec(v_declName_5498_);
                    v___x_5522_ = leanh::lean_box(0);
                    if v_isShared_5520_ == 0 {
                        leanh::lean_ctor_set(v___x_5519_, 0, v___x_5522_);
                        v___x_5524_ = v___x_5519_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5525_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5525_, 0, v___x_5522_);
                        v___x_5524_ = v_reuseFailAlloc_5525_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5519_);
                    v___x_5526_ = 0;
                    v___x_5527_ = l_Lean_Compiler_LCNF_Code_inferType(
                        v___x_5526_,
                        v_value_5501_,
                        v___y_5512_,
                        v___y_5513_,
                        v___y_5514_,
                        v___y_5515_,
                    );
                    if leanh::lean_obj_tag(v___x_5527_) == 0 {
                        v_a_5528_ = leanh::lean_ctor_get(v___x_5527_, 0);
                        leanh::lean_inc(v_a_5528_);
                        leanh::lean_dec_ref_known(v___x_5527_, 1);
                        v___x_5529_ = l_Lean_Compiler_LCNF_mkForallParams(
                            v___x_5526_,
                            v_params_5499_,
                            v_a_5528_,
                            v___y_5512_,
                            v___y_5513_,
                            v___y_5514_,
                            v___y_5515_,
                        );
                        leanh::lean_dec(v_a_5528_);
                        if leanh::lean_obj_tag(v___x_5529_) == 0 {
                            v_a_5530_ = leanh::lean_ctor_get(v___x_5529_, 0);
                            leanh::lean_inc_n(v_a_5530_, 2);
                            leanh::lean_dec_ref_known(v___x_5529_, 1);
                            leanh::lean_inc_ref(v_type_5500_);
                            v___x_5531_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_type_5500_,
                                v_a_5530_,
                                v___y_5511_,
                                v___y_5512_,
                                v___y_5513_,
                                v___y_5514_,
                                v___y_5515_,
                            );
                            if leanh::lean_obj_tag(v___x_5531_) == 0 {
                                v_a_5532_ = leanh::lean_ctor_get(v___x_5531_, 0);
                                v_isSharedCheck_5554_ =
                                    (!leanh::lean_is_exclusive(v___x_5531_)) as u8;
                                if v_isSharedCheck_5554_ == 0 {
                                    v___x_5534_ = v___x_5531_;
                                    v_isShared_5535_ = v_isSharedCheck_5554_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5532_);
                                    leanh::lean_dec(v___x_5531_);
                                    v___x_5534_ = leanh::lean_box(0);
                                    v_isShared_5535_ = v_isSharedCheck_5554_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5530_);
                                leanh::lean_dec_ref(v_type_5500_);
                                leanh::lean_dec(v_declName_5498_);
                                v_a_5555_ = leanh::lean_ctor_get(v___x_5531_, 0);
                                v_isSharedCheck_5562_ =
                                    (!leanh::lean_is_exclusive(v___x_5531_)) as u8;
                                if v_isSharedCheck_5562_ == 0 {
                                    v___x_5557_ = v___x_5531_;
                                    v_isShared_5558_ = v_isSharedCheck_5562_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5555_);
                                    leanh::lean_dec(v___x_5531_);
                                    v___x_5557_ = leanh::lean_box(0);
                                    v_isShared_5558_ = v_isSharedCheck_5562_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_type_5500_);
                            leanh::lean_dec(v_declName_5498_);
                            v_a_5563_ = leanh::lean_ctor_get(v___x_5529_, 0);
                            v_isSharedCheck_5570_ =
                                (!leanh::lean_is_exclusive(v___x_5529_)) as u8;
                            if v_isSharedCheck_5570_ == 0 {
                                v___x_5565_ = v___x_5529_;
                                v_isShared_5566_ = v_isSharedCheck_5570_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5563_);
                                leanh::lean_dec(v___x_5529_);
                                v___x_5565_ = leanh::lean_box(0);
                                v_isShared_5566_ = v_isSharedCheck_5570_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_type_5500_);
                        leanh::lean_dec_ref(v_params_5499_);
                        leanh::lean_dec(v_declName_5498_);
                        v_a_5571_ = leanh::lean_ctor_get(v___x_5527_, 0);
                        v_isSharedCheck_5578_ =
                            (!leanh::lean_is_exclusive(v___x_5527_)) as u8;
                        if v_isSharedCheck_5578_ == 0 {
                            v___x_5573_ = v___x_5527_;
                            v_isShared_5574_ = v_isSharedCheck_5578_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5571_);
                            leanh::lean_dec(v___x_5527_);
                            v___x_5573_ = leanh::lean_box(0);
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
                v___x_5536_ = (leanh::lean_unbox(v_a_5532_) as u8);
                if v___x_5536_ == 0 {
                    leanh::lean_del_object(v___x_5534_);
                    v___x_5537_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5,
                    );
                    v___x_5538_ = (leanh::lean_unbox(v_a_5532_) as u8);
                    leanh::lean_dec(v_a_5532_);
                    v___x_5539_ = l_Lean_MessageData_ofConstName(v_declName_5498_, v___x_5538_);
                    v___x_5540_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5540_, 0, v___x_5537_);
                    leanh::lean_ctor_set(v___x_5540_, 1, v___x_5539_);
                    v___x_5541_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7,
                    );
                    v___x_5542_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5542_, 0, v___x_5540_);
                    leanh::lean_ctor_set(v___x_5542_, 1, v___x_5541_);
                    v___x_5543_ = l_Lean_indentExpr(v_a_5530_);
                    v___x_5544_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5544_, 0, v___x_5542_);
                    leanh::lean_ctor_set(v___x_5544_, 1, v___x_5543_);
                    v___x_5545_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                    v___x_5546_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5546_, 0, v___x_5544_);
                    leanh::lean_ctor_set(v___x_5546_, 1, v___x_5545_);
                    v___x_5547_ = l_Lean_indentExpr(v_type_5500_);
                    v___x_5548_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5548_, 0, v___x_5546_);
                    leanh::lean_ctor_set(v___x_5548_, 1, v___x_5547_);
                    v___x_5549_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5548_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_);
                    return v___x_5549_;
                } else {
                    leanh::lean_dec(v_a_5532_);
                    leanh::lean_dec(v_a_5530_);
                    leanh::lean_dec_ref(v_type_5500_);
                    leanh::lean_dec(v_declName_5498_);
                    v___x_5550_ = leanh::lean_box(0);
                    if v_isShared_5535_ == 0 {
                        leanh::lean_ctor_set(v___x_5534_, 0, v___x_5550_);
                        v___x_5552_ = v___x_5534_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5553_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5550_);
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
                    v_reuseFailAlloc_5561_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
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
                    v_reuseFailAlloc_5569_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5563_);
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
                    v_reuseFailAlloc_5577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5571_);
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
                    v_reuseFailAlloc_5586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_a_5580_);
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
                if leanh::lean_obj_tag(v___x_5591_) == 0 {
                    v_a_5592_ = leanh::lean_ctor_get(v___x_5591_, 0);
                    v_isSharedCheck_5652_ = (!leanh::lean_is_exclusive(v___x_5591_)) as u8;
                    if v_isSharedCheck_5652_ == 0 {
                        v___x_5594_ = v___x_5591_;
                        v_isShared_5595_ = v_isSharedCheck_5652_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5592_);
                        leanh::lean_dec(v___x_5591_);
                        v___x_5594_ = leanh::lean_box(0);
                        v_isShared_5595_ = v_isSharedCheck_5652_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_value_5501_);
                    leanh::lean_dec_ref(v_type_5500_);
                    leanh::lean_dec_ref(v_params_5499_);
                    leanh::lean_dec(v_declName_5498_);
                    v_a_5653_ = leanh::lean_ctor_get(v___x_5591_, 0);
                    v_isSharedCheck_5660_ = (!leanh::lean_is_exclusive(v___x_5591_)) as u8;
                    if v_isSharedCheck_5660_ == 0 {
                        v___x_5655_ = v___x_5591_;
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5653_);
                        leanh::lean_dec(v___x_5591_);
                        v___x_5655_ = leanh::lean_box(0);
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 25;
                        continue;
                    }
                }
            }
            15 => {
                v___x_5596_ = (leanh::lean_unbox(v_a_5592_) as u8);
                leanh::lean_dec(v_a_5592_);
                if v___x_5596_ == 0 {
                    leanh::lean_dec_ref(v_value_5501_);
                    leanh::lean_dec_ref(v_type_5500_);
                    leanh::lean_dec_ref(v_params_5499_);
                    leanh::lean_dec(v_declName_5498_);
                    if v_isShared_5595_ == 0 {
                        leanh::lean_ctor_set(v___x_5594_, 0, v___x_5589_);
                        v___x_5598_ = v___x_5594_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5599_, 0, v___x_5589_);
                        v___x_5598_ = v_reuseFailAlloc_5599_;
                        state = 16;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5594_);
                    v___x_5600_ = 0;
                    v___x_5601_ = l_Lean_Compiler_LCNF_Code_inferType(
                        v___x_5600_,
                        v_value_5501_,
                        v_a_5505_,
                        v_a_5506_,
                        v_a_5507_,
                        v_a_5508_,
                    );
                    if leanh::lean_obj_tag(v___x_5601_) == 0 {
                        v_a_5602_ = leanh::lean_ctor_get(v___x_5601_, 0);
                        leanh::lean_inc(v_a_5602_);
                        leanh::lean_dec_ref_known(v___x_5601_, 1);
                        v___x_5603_ = l_Lean_Compiler_LCNF_mkForallParams(
                            v___x_5600_,
                            v_params_5499_,
                            v_a_5602_,
                            v_a_5505_,
                            v_a_5506_,
                            v_a_5507_,
                            v_a_5508_,
                        );
                        leanh::lean_dec(v_a_5602_);
                        if leanh::lean_obj_tag(v___x_5603_) == 0 {
                            v_a_5604_ = leanh::lean_ctor_get(v___x_5603_, 0);
                            leanh::lean_inc_n(v_a_5604_, 2);
                            leanh::lean_dec_ref_known(v___x_5603_, 1);
                            leanh::lean_inc_ref(v_type_5500_);
                            v___x_5605_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_type_5500_,
                                v_a_5604_,
                                v_a_5504_,
                                v_a_5505_,
                                v_a_5506_,
                                v_a_5507_,
                                v_a_5508_,
                            );
                            if leanh::lean_obj_tag(v___x_5605_) == 0 {
                                v_a_5606_ = leanh::lean_ctor_get(v___x_5605_, 0);
                                v_isSharedCheck_5627_ =
                                    (!leanh::lean_is_exclusive(v___x_5605_)) as u8;
                                if v_isSharedCheck_5627_ == 0 {
                                    v___x_5608_ = v___x_5605_;
                                    v_isShared_5609_ = v_isSharedCheck_5627_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5606_);
                                    leanh::lean_dec(v___x_5605_);
                                    v___x_5608_ = leanh::lean_box(0);
                                    v_isShared_5609_ = v_isSharedCheck_5627_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5604_);
                                leanh::lean_dec_ref(v_type_5500_);
                                leanh::lean_dec(v_declName_5498_);
                                v_a_5628_ = leanh::lean_ctor_get(v___x_5605_, 0);
                                v_isSharedCheck_5635_ =
                                    (!leanh::lean_is_exclusive(v___x_5605_)) as u8;
                                if v_isSharedCheck_5635_ == 0 {
                                    v___x_5630_ = v___x_5605_;
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5628_);
                                    leanh::lean_dec(v___x_5605_);
                                    v___x_5630_ = leanh::lean_box(0);
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_type_5500_);
                            leanh::lean_dec(v_declName_5498_);
                            v_a_5636_ = leanh::lean_ctor_get(v___x_5603_, 0);
                            v_isSharedCheck_5643_ =
                                (!leanh::lean_is_exclusive(v___x_5603_)) as u8;
                            if v_isSharedCheck_5643_ == 0 {
                                v___x_5638_ = v___x_5603_;
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5636_);
                                leanh::lean_dec(v___x_5603_);
                                v___x_5638_ = leanh::lean_box(0);
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_type_5500_);
                        leanh::lean_dec_ref(v_params_5499_);
                        leanh::lean_dec(v_declName_5498_);
                        v_a_5644_ = leanh::lean_ctor_get(v___x_5601_, 0);
                        v_isSharedCheck_5651_ =
                            (!leanh::lean_is_exclusive(v___x_5601_)) as u8;
                        if v_isSharedCheck_5651_ == 0 {
                            v___x_5646_ = v___x_5601_;
                            v_isShared_5647_ = v_isSharedCheck_5651_;
                            state = 23;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5644_);
                            leanh::lean_dec(v___x_5601_);
                            v___x_5646_ = leanh::lean_box(0);
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
                v___x_5610_ = (leanh::lean_unbox(v_a_5606_) as u8);
                if v___x_5610_ == 0 {
                    leanh::lean_del_object(v___x_5608_);
                    v___x_5611_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5,
                    );
                    v___x_5612_ = (leanh::lean_unbox(v_a_5606_) as u8);
                    leanh::lean_dec(v_a_5606_);
                    v___x_5613_ = l_Lean_MessageData_ofConstName(v_declName_5498_, v___x_5612_);
                    v___x_5614_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5614_, 0, v___x_5611_);
                    leanh::lean_ctor_set(v___x_5614_, 1, v___x_5613_);
                    v___x_5615_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7,
                    );
                    v___x_5616_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5616_, 0, v___x_5614_);
                    leanh::lean_ctor_set(v___x_5616_, 1, v___x_5615_);
                    v___x_5617_ = l_Lean_indentExpr(v_a_5604_);
                    v___x_5618_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5618_, 0, v___x_5616_);
                    leanh::lean_ctor_set(v___x_5618_, 1, v___x_5617_);
                    v___x_5619_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                    v___x_5620_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5620_, 0, v___x_5618_);
                    leanh::lean_ctor_set(v___x_5620_, 1, v___x_5619_);
                    v___x_5621_ = l_Lean_indentExpr(v_type_5500_);
                    v___x_5622_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5622_, 0, v___x_5620_);
                    leanh::lean_ctor_set(v___x_5622_, 1, v___x_5621_);
                    v___x_5623_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5622_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
                    return v___x_5623_;
                } else {
                    leanh::lean_dec(v_a_5606_);
                    leanh::lean_dec(v_a_5604_);
                    leanh::lean_dec_ref(v_type_5500_);
                    leanh::lean_dec(v_declName_5498_);
                    if v_isShared_5609_ == 0 {
                        leanh::lean_ctor_set(v___x_5608_, 0, v___x_5589_);
                        v___x_5625_ = v___x_5608_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_5626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5626_, 0, v___x_5589_);
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
                    v_reuseFailAlloc_5634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
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
                    v_reuseFailAlloc_5642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_a_5636_);
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
                    v_reuseFailAlloc_5650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_a_5644_);
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
                    v_reuseFailAlloc_5659_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
                    v___x_5658_ = v_reuseFailAlloc_5659_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5658_;
            }
            27 => {
                v_jps_5664_ = leanh::lean_ctor_get(v_a_5502_, 0);
                v_vars_5665_ = leanh::lean_ctor_get(v_a_5502_, 1);
                v___x_5666_ = lean_nat_dec_lt(v___x_5661_, v___x_5662_);
                if v___x_5666_ == 0 {
                    leanh::lean_inc_ref(v_a_5502_);
                    leanh::lean_inc_ref(v_value_5501_);
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
                    if leanh::lean_obj_tag(v___x_5667_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5667_, 1);
                        state = 14;
                        continue;
                    } else {
                        if leanh::lean_obj_tag(v___x_5667_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5667_, 1);
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_value_5501_);
                            leanh::lean_dec_ref(v_type_5500_);
                            leanh::lean_dec_ref(v_params_5499_);
                            leanh::lean_dec(v_declName_5498_);
                            return v___x_5667_;
                        }
                    }
                } else {
                    v___x_5668_ = lean_nat_dec_le(v___x_5662_, v___x_5662_);
                    if v___x_5668_ == 0 {
                        if v___x_5666_ == 0 {
                            leanh::lean_inc_ref(v_a_5502_);
                            leanh::lean_inc_ref(v_value_5501_);
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
                            if leanh::lean_obj_tag(v___x_5669_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5669_, 1);
                                v___y_5511_ = v_a_5504_;
                                v___y_5512_ = v_a_5505_;
                                v___y_5513_ = v_a_5506_;
                                v___y_5514_ = v_a_5507_;
                                v___y_5515_ = v_a_5508_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_value_5501_);
                                leanh::lean_dec_ref(v_type_5500_);
                                leanh::lean_dec_ref(v_params_5499_);
                                leanh::lean_dec(v_declName_5498_);
                                return v___x_5669_;
                            }
                        } else {
                            v___x_5670_ = 0usize;
                            v___x_5671_ = lean_usize_of_nat(v___x_5662_);
                            leanh::lean_inc(v_vars_5665_);
                            v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5499_, v___x_5670_, v___x_5671_, v_vars_5665_);
                            leanh::lean_inc(v_jps_5664_);
                            v___x_5673_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5673_, 0, v_jps_5664_);
                            leanh::lean_ctor_set(v___x_5673_, 1, v___x_5672_);
                            leanh::lean_inc_ref(v_value_5501_);
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
                            if leanh::lean_obj_tag(v___x_5674_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5674_, 1);
                                v___y_5511_ = v_a_5504_;
                                v___y_5512_ = v_a_5505_;
                                v___y_5513_ = v_a_5506_;
                                v___y_5514_ = v_a_5507_;
                                v___y_5515_ = v_a_5508_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_value_5501_);
                                leanh::lean_dec_ref(v_type_5500_);
                                leanh::lean_dec_ref(v_params_5499_);
                                leanh::lean_dec(v_declName_5498_);
                                return v___x_5674_;
                            }
                        }
                    } else {
                        v___x_5675_ = 0usize;
                        v___x_5676_ = lean_usize_of_nat(v___x_5662_);
                        leanh::lean_inc(v_vars_5665_);
                        v___x_5677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5499_, v___x_5675_, v___x_5676_, v_vars_5665_);
                        leanh::lean_inc(v_jps_5664_);
                        v___x_5678_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5678_, 0, v_jps_5664_);
                        leanh::lean_ctor_set(v___x_5678_, 1, v___x_5677_);
                        leanh::lean_inc_ref(v_value_5501_);
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
                        if leanh::lean_obj_tag(v___x_5679_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5679_, 1);
                            v___y_5511_ = v_a_5504_;
                            v___y_5512_ = v_a_5505_;
                            v___y_5513_ = v_a_5506_;
                            v___y_5514_ = v_a_5507_;
                            v___y_5515_ = v_a_5508_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_value_5501_);
                            leanh::lean_dec_ref(v_type_5500_);
                            leanh::lean_dec_ref(v_params_5499_);
                            leanh::lean_dec(v_declName_5498_);
                            return v___x_5679_;
                        }
                    }
                }
            }
            28 => {
                if leanh::lean_obj_tag(v___y_5681_) == 0 {
                    leanh::lean_dec_ref_known(v___y_5681_, 1);
                    state = 27;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_value_5501_);
                    leanh::lean_dec_ref(v_type_5500_);
                    leanh::lean_dec_ref(v_params_5499_);
                    leanh::lean_dec(v_declName_5498_);
                    return v___y_5681_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5691_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0;
    v___x_5692_ = l_Lean_stringToMessageData(v___x_5691_);
    return v___x_5692_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5694_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2;
    v___x_5695_ = l_Lean_stringToMessageData(v___x_5694_);
    return v___x_5695_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5697_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4;
    v___x_5698_ = l_Lean_stringToMessageData(v___x_5697_);
    return v___x_5698_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5700_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6;
    v___x_5701_ = l_Lean_stringToMessageData(v___x_5700_);
    return v___x_5701_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5703_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8;
    v___x_5704_ = l_Lean_stringToMessageData(v___x_5703_);
    return v___x_5704_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(
    mut v_funDecl_5705_: *mut leanh::LeanObject,
    mut v_a_5706_: *mut leanh::LeanObject,
    mut v_a_5707_: *mut leanh::LeanObject,
    mut v_a_5708_: *mut leanh::LeanObject,
    mut v_a_5709_: *mut leanh::LeanObject,
    mut v_a_5710_: *mut leanh::LeanObject,
    mut v_a_5711_: *mut leanh::LeanObject,
    mut v_a_5712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: u8 = 0;
    let mut v___y_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5730_: u8 = 0;
    let mut v___x_5731_: u8 = 0;
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5742_: u8 = 0;
    let mut v_a_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5746_: u8 = 0;
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5750_: u8 = 0;
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: u8 = 0;
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_5714_ = leanh::lean_ctor_get(v_funDecl_5705_, 0);
                v_binderName_5715_ = leanh::lean_ctor_get(v_funDecl_5705_, 1);
                leanh::lean_inc_n(v_binderName_5715_, 2);
                v_params_5716_ = leanh::lean_ctor_get(v_funDecl_5705_, 2);
                v_type_5717_ = leanh::lean_ctor_get(v_funDecl_5705_, 3);
                v_value_5718_ = leanh::lean_ctor_get(v_funDecl_5705_, 4);
                leanh::lean_inc_ref(v_value_5718_);
                leanh::lean_inc_ref(v_type_5717_);
                leanh::lean_inc_ref(v_params_5716_);
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
                if leanh::lean_obj_tag(v___x_5719_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5719_, 1);
                    v___x_5720_ = 0;
                    leanh::lean_inc(v_fvarId_5714_);
                    v___x_5751_ = l_Lean_Compiler_LCNF_getFunDecl(
                        v___x_5720_,
                        v_fvarId_5714_,
                        v_a_5709_,
                        v_a_5710_,
                        v_a_5711_,
                        v_a_5712_,
                    );
                    if leanh::lean_obj_tag(v___x_5751_) == 0 {
                        v_a_5752_ = leanh::lean_ctor_get(v___x_5751_, 0);
                        leanh::lean_inc(v_a_5752_);
                        leanh::lean_dec_ref_known(v___x_5751_, 1);
                        v_binderName_5753_ = leanh::lean_ctor_get(v_a_5752_, 1);
                        leanh::lean_inc(v_binderName_5753_);
                        v_type_5754_ = leanh::lean_ctor_get(v_a_5752_, 3);
                        leanh::lean_inc_ref(v_type_5754_);
                        leanh::lean_dec(v_a_5752_);
                        v___x_5773_ = lean_name_eq(v_binderName_5753_, v_binderName_5715_);
                        if v___x_5773_ == 0 {
                            v___x_5774_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                            );
                            leanh::lean_inc(v_binderName_5715_);
                            v___x_5775_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                            v___x_5776_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5776_, 0, v___x_5774_);
                            leanh::lean_ctor_set(v___x_5776_, 1, v___x_5775_);
                            v___x_5777_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9,
                            );
                            v___x_5778_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5778_, 0, v___x_5776_);
                            leanh::lean_ctor_set(v___x_5778_, 1, v___x_5777_);
                            v___x_5779_ = l_Lean_MessageData_ofName(v_binderName_5753_);
                            v___x_5780_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5780_, 0, v___x_5778_);
                            leanh::lean_ctor_set(v___x_5780_, 1, v___x_5779_);
                            v___x_5781_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                            v___x_5782_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5782_, 0, v___x_5780_);
                            leanh::lean_ctor_set(v___x_5782_, 1, v___x_5781_);
                            v___x_5783_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5782_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_);
                            if leanh::lean_obj_tag(v___x_5783_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5783_, 1);
                                v___y_5756_ = v_a_5709_;
                                v___y_5757_ = v_a_5710_;
                                v___y_5758_ = v_a_5711_;
                                v___y_5759_ = v_a_5712_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_type_5754_);
                                leanh::lean_dec(v_binderName_5715_);
                                leanh::lean_dec_ref(v_funDecl_5705_);
                                return v___x_5783_;
                            }
                        } else {
                            leanh::lean_dec(v_binderName_5753_);
                            v___y_5756_ = v_a_5709_;
                            v___y_5757_ = v_a_5710_;
                            v___y_5758_ = v_a_5711_;
                            v___y_5759_ = v_a_5712_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_binderName_5715_);
                        leanh::lean_dec_ref(v_funDecl_5705_);
                        v_a_5784_ = leanh::lean_ctor_get(v___x_5751_, 0);
                        v_isSharedCheck_5791_ =
                            (!leanh::lean_is_exclusive(v___x_5751_)) as u8;
                        if v_isSharedCheck_5791_ == 0 {
                            v___x_5786_ = v___x_5751_;
                            v_isShared_5787_ = v_isSharedCheck_5791_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5784_);
                            leanh::lean_dec(v___x_5751_);
                            v___x_5786_ = leanh::lean_box(0);
                            v_isShared_5787_ = v_isSharedCheck_5791_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_binderName_5715_);
                    leanh::lean_dec_ref(v_funDecl_5705_);
                    return v___x_5719_;
                }
            }
            1 => {
                leanh::lean_inc(v_fvarId_5714_);
                v___x_5726_ = l_Lean_Compiler_LCNF_getFunDecl(
                    v___x_5720_,
                    v_fvarId_5714_,
                    v___y_5722_,
                    v___y_5723_,
                    v___y_5724_,
                    v___y_5725_,
                );
                if leanh::lean_obj_tag(v___x_5726_) == 0 {
                    v_a_5727_ = leanh::lean_ctor_get(v___x_5726_, 0);
                    v_isSharedCheck_5742_ = (!leanh::lean_is_exclusive(v___x_5726_)) as u8;
                    if v_isSharedCheck_5742_ == 0 {
                        v___x_5729_ = v___x_5726_;
                        v_isShared_5730_ = v_isSharedCheck_5742_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5727_);
                        leanh::lean_dec(v___x_5726_);
                        v___x_5729_ = leanh::lean_box(0);
                        v_isShared_5730_ = v_isSharedCheck_5742_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_binderName_5715_);
                    leanh::lean_dec_ref(v_funDecl_5705_);
                    v_a_5743_ = leanh::lean_ctor_get(v___x_5726_, 0);
                    v_isSharedCheck_5750_ = (!leanh::lean_is_exclusive(v___x_5726_)) as u8;
                    if v_isSharedCheck_5750_ == 0 {
                        v___x_5745_ = v___x_5726_;
                        v_isShared_5746_ = v_isSharedCheck_5750_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5743_);
                        leanh::lean_dec(v___x_5726_);
                        v___x_5745_ = leanh::lean_box(0);
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
                leanh::lean_dec_ref(v_funDecl_5705_);
                leanh::lean_dec(v_a_5727_);
                if v___x_5731_ == 0 {
                    leanh::lean_del_object(v___x_5729_);
                    v___x_5732_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                    );
                    v___x_5733_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                    v___x_5734_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5734_, 0, v___x_5732_);
                    leanh::lean_ctor_set(v___x_5734_, 1, v___x_5733_);
                    v___x_5735_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3,
                    );
                    v___x_5736_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5736_, 0, v___x_5734_);
                    leanh::lean_ctor_set(v___x_5736_, 1, v___x_5735_);
                    v___x_5737_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5736_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
                    return v___x_5737_;
                } else {
                    leanh::lean_dec(v_binderName_5715_);
                    v___x_5738_ = leanh::lean_box(0);
                    if v_isShared_5730_ == 0 {
                        leanh::lean_ctor_set(v___x_5729_, 0, v___x_5738_);
                        v___x_5740_ = v___x_5729_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5738_);
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
                    v_reuseFailAlloc_5749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_a_5743_);
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
                    v___x_5761_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                    );
                    leanh::lean_inc(v_binderName_5715_);
                    v___x_5762_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                    v___x_5763_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5763_, 0, v___x_5761_);
                    leanh::lean_ctor_set(v___x_5763_, 1, v___x_5762_);
                    v___x_5764_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5,
                    );
                    v___x_5765_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5765_, 0, v___x_5763_);
                    leanh::lean_ctor_set(v___x_5765_, 1, v___x_5764_);
                    v___x_5766_ = l_Lean_indentExpr(v_type_5754_);
                    v___x_5767_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5767_, 0, v___x_5765_);
                    leanh::lean_ctor_set(v___x_5767_, 1, v___x_5766_);
                    v___x_5768_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7,
                    );
                    v___x_5769_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5769_, 0, v___x_5767_);
                    leanh::lean_ctor_set(v___x_5769_, 1, v___x_5768_);
                    leanh::lean_inc_ref(v_type_5717_);
                    v___x_5770_ = l_Lean_indentExpr(v_type_5717_);
                    v___x_5771_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5771_, 0, v___x_5769_);
                    leanh::lean_ctor_set(v___x_5771_, 1, v___x_5770_);
                    v___x_5772_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5771_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_);
                    if leanh::lean_obj_tag(v___x_5772_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5772_, 1);
                        v___y_5722_ = v___y_5756_;
                        v___y_5723_ = v___y_5757_;
                        v___y_5724_ = v___y_5758_;
                        v___y_5725_ = v___y_5759_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_binderName_5715_);
                        leanh::lean_dec_ref(v_funDecl_5705_);
                        return v___x_5772_;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_5754_);
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
                    v_reuseFailAlloc_5790_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
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
-> *mut leanh::LeanObject {
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5793_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__1;
    v___x_5794_ = l_Lean_stringToMessageData(v___x_5793_);
    return v___x_5794_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5796_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__3;
    v___x_5797_ = l_Lean_stringToMessageData(v___x_5796_);
    return v___x_5797_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5799_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__5;
    v___x_5800_ = l_Lean_stringToMessageData(v___x_5799_);
    return v___x_5800_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5802_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__7;
    v___x_5803_ = l_Lean_stringToMessageData(v___x_5802_);
    return v___x_5803_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0()
-> *mut leanh::LeanObject {
    let mut v_hasDefault_5804_: u8 = 0;
    let mut v_ctorNames_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hasDefault_5804_ = 0;
    v_ctorNames_5805_ = l_Lean_NameSet_empty;
    v___x_5806_ = leanh::lean_box((v_hasDefault_5804_) as usize);
    v___x_5807_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5807_, 0, v_ctorNames_5805_);
    leanh::lean_ctor_set(v___x_5807_, 1, v___x_5806_);
    return v___x_5807_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0;
    v___x_5810_ = l_Lean_stringToMessageData(v___x_5809_);
    return v___x_5810_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2;
    v___x_5813_ = l_Lean_stringToMessageData(v___x_5812_);
    return v___x_5813_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4;
    v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6;
    v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
    return v___x_5819_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8;
    v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10;
    v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
    return v___x_5825_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12;
    v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14;
    v___x_5831_ = l_Lean_stringToMessageData(v___x_5830_);
    return v___x_5831_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5(
    mut v_typeName_5832_: *mut leanh::LeanObject,
    mut v_as_5833_: *mut leanh::LeanObject,
    mut v_sz_5834_: usize,
    mut v_i_5835_: usize,
    mut v_b_5836_: *mut leanh::LeanObject,
    mut v___y_5837_: *mut leanh::LeanObject,
    mut v___y_5838_: *mut leanh::LeanObject,
    mut v___y_5839_: *mut leanh::LeanObject,
    mut v___y_5840_: *mut leanh::LeanObject,
    mut v___y_5841_: *mut leanh::LeanObject,
    mut v___y_5842_: *mut leanh::LeanObject,
    mut v___y_5843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: usize = 0;
    let mut v___x_5848_: usize = 0;
    let mut v___x_5850_: u8 = 0;
    let mut v___x_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___y_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5866_: u8 = 0;
    let mut v___x_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_a_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: u8 = 0;
    let mut v___x_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: u8 = 0;
    let mut v___x_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: usize = 0;
    let mut v___x_5895_: usize = 0;
    let mut v___x_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: usize = 0;
    let mut v___x_5900_: usize = 0;
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5919_: u8 = 0;
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5923_: u8 = 0;
    let mut v___y_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: u8 = 0;
    let mut v___x_5938_: usize = 0;
    let mut v___x_5939_: usize = 0;
    let mut v___x_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: usize = 0;
    let mut v___x_5942_: usize = 0;
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u8 = 0;
    let mut v___x_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5977_: u8 = 0;
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v___y_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: u8 = 0;
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6010_: u8 = 0;
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6014_: u8 = 0;
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6025_: u8 = 0;
    let mut v___x_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6029_: u8 = 0;
    let mut v_a_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6033_: u8 = 0;
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6037_: u8 = 0;
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: u8 = 0;
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6049_: u8 = 0;
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6053_: u8 = 0;
    let mut v_a_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6057_: u8 = 0;
    let mut v___x_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6061_: u8 = 0;
    let mut v_code_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_isSharedCheck_6074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5850_ = lean_usize_dec_lt(v_i_5835_, v_sz_5834_);
                if v___x_5850_ == 0 {
                    leanh::lean_dec(v_typeName_5832_);
                    v___x_5851_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5851_, 0, v_b_5836_);
                    return v___x_5851_;
                } else {
                    v_fst_5852_ = leanh::lean_ctor_get(v_b_5836_, 0);
                    v_snd_5853_ = leanh::lean_ctor_get(v_b_5836_, 1);
                    v_isSharedCheck_6074_ = (!leanh::lean_is_exclusive(v_b_5836_)) as u8;
                    if v_isSharedCheck_6074_ == 0 {
                        v___x_5855_ = v_b_5836_;
                        v_isShared_5856_ = v_isSharedCheck_6074_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5853_);
                        leanh::lean_inc(v_fst_5852_);
                        leanh::lean_dec(v_b_5836_);
                        v___x_5855_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v_a_5871_) == 0 {
                    v_ctorName_5872_ = leanh::lean_ctor_get(v_a_5871_, 0);
                    v_params_5873_ = leanh::lean_ctor_get(v_a_5871_, 1);
                    v_code_5874_ = leanh::lean_ctor_get(v_a_5871_, 2);
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
                    if leanh::lean_obj_tag(v___x_6038_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6038_, 1);
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
                            v___x_6040_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13);
                            leanh::lean_inc(v_ctorName_5872_);
                            v___x_6041_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                            v___x_6042_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6042_, 0, v___x_6040_);
                            leanh::lean_ctor_set(v___x_6042_, 1, v___x_6041_);
                            v___x_6043_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15);
                            v___x_6044_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6044_, 0, v___x_6042_);
                            leanh::lean_ctor_set(v___x_6044_, 1, v___x_6043_);
                            v___x_6045_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6044_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
                            if leanh::lean_obj_tag(v___x_6045_) == 0 {
                                leanh::lean_dec_ref_known(v___x_6045_, 1);
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
                                leanh::lean_del_object(v___x_5855_);
                                leanh::lean_dec(v_snd_5853_);
                                leanh::lean_dec(v_fst_5852_);
                                leanh::lean_dec(v_typeName_5832_);
                                v_a_6046_ = leanh::lean_ctor_get(v___x_6045_, 0);
                                v_isSharedCheck_6053_ =
                                    (!leanh::lean_is_exclusive(v___x_6045_)) as u8;
                                if v_isSharedCheck_6053_ == 0 {
                                    v___x_6048_ = v___x_6045_;
                                    v_isShared_6049_ = v_isSharedCheck_6053_;
                                    state = 22;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6046_);
                                    leanh::lean_dec(v___x_6045_);
                                    v___x_6048_ = leanh::lean_box(0);
                                    v_isShared_6049_ = v_isSharedCheck_6053_;
                                    state = 22;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_5855_);
                        leanh::lean_dec(v_snd_5853_);
                        leanh::lean_dec(v_fst_5852_);
                        leanh::lean_dec(v_typeName_5832_);
                        v_a_6054_ = leanh::lean_ctor_get(v___x_6038_, 0);
                        v_isSharedCheck_6061_ =
                            (!leanh::lean_is_exclusive(v___x_6038_)) as u8;
                        if v_isSharedCheck_6061_ == 0 {
                            v___x_6056_ = v___x_6038_;
                            v_isShared_6057_ = v_isSharedCheck_6061_;
                            state = 24;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6054_);
                            leanh::lean_dec(v___x_6038_);
                            v___x_6056_ = leanh::lean_box(0);
                            v_isShared_6057_ = v_isSharedCheck_6061_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5855_);
                    leanh::lean_dec(v_snd_5853_);
                    v_code_6062_ = leanh::lean_ctor_get(v_a_5871_, 0);
                    leanh::lean_inc_ref(v___y_5837_);
                    leanh::lean_inc_ref(v_code_6062_);
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
                    if leanh::lean_obj_tag(v___x_6063_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6063_, 1);
                        v___x_6064_ = leanh::lean_box((v___x_5850_) as usize);
                        v___x_6065_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6065_, 0, v_fst_5852_);
                        leanh::lean_ctor_set(v___x_6065_, 1, v___x_6064_);
                        v_a_5846_ = v___x_6065_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_5852_);
                        leanh::lean_dec(v_typeName_5832_);
                        v_a_6066_ = leanh::lean_ctor_get(v___x_6063_, 0);
                        v_isSharedCheck_6073_ =
                            (!leanh::lean_is_exclusive(v___x_6063_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6063_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 26;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6066_);
                            leanh::lean_dec(v___x_6063_);
                            v___x_6068_ = leanh::lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v___y_5859_) == 0 {
                    leanh::lean_dec_ref_known(v___y_5859_, 1);
                    if v_isShared_5856_ == 0 {
                        leanh::lean_ctor_set(v___x_5855_, 0, v___y_5858_);
                        v___x_5861_ = v___x_5855_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5862_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___y_5858_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5862_, 1, v_snd_5853_);
                        v___x_5861_ = v_reuseFailAlloc_5862_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_5858_);
                    leanh::lean_del_object(v___x_5855_);
                    leanh::lean_dec(v_snd_5853_);
                    leanh::lean_dec(v_typeName_5832_);
                    v_a_5863_ = leanh::lean_ctor_get(v___y_5859_, 0);
                    v_isSharedCheck_5870_ = (!leanh::lean_is_exclusive(v___y_5859_)) as u8;
                    if v_isSharedCheck_5870_ == 0 {
                        v___x_5865_ = v___y_5859_;
                        v_isShared_5866_ = v_isSharedCheck_5870_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5863_);
                        leanh::lean_dec(v___y_5859_);
                        v___x_5865_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
                    v___x_5868_ = v_reuseFailAlloc_5869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5868_;
            }
            7 => {
                v_jps_5886_ = leanh::lean_ctor_get(v___y_5880_, 0);
                v_vars_5887_ = leanh::lean_ctor_get(v___y_5880_, 1);
                v___x_5888_ = lean_nat_dec_lt(v___y_5876_, v___y_5885_);
                if v___x_5888_ == 0 {
                    leanh::lean_dec(v___y_5885_);
                    leanh::lean_inc(v_vars_5887_);
                    leanh::lean_inc(v_jps_5886_);
                    v___x_5889_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5889_, 0, v_jps_5886_);
                    leanh::lean_ctor_set(v___x_5889_, 1, v_vars_5887_);
                    leanh::lean_inc_ref(v_code_5874_);
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
                            leanh::lean_dec(v___y_5885_);
                            leanh::lean_inc(v_vars_5887_);
                            leanh::lean_inc(v_jps_5886_);
                            v___x_5892_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5892_, 0, v_jps_5886_);
                            leanh::lean_ctor_set(v___x_5892_, 1, v_vars_5887_);
                            leanh::lean_inc_ref(v_code_5874_);
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
                            leanh::lean_dec(v___y_5885_);
                            leanh::lean_inc(v_vars_5887_);
                            v___x_5896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5873_, v___x_5894_, v___x_5895_, v_vars_5887_);
                            leanh::lean_inc(v_jps_5886_);
                            v___x_5897_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5897_, 0, v_jps_5886_);
                            leanh::lean_ctor_set(v___x_5897_, 1, v___x_5896_);
                            leanh::lean_inc_ref(v_code_5874_);
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
                        leanh::lean_dec(v___y_5885_);
                        leanh::lean_inc(v_vars_5887_);
                        v___x_5901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5873_, v___x_5899_, v___x_5900_, v_vars_5887_);
                        leanh::lean_inc(v_jps_5886_);
                        v___x_5902_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5902_, 0, v_jps_5886_);
                        leanh::lean_ctor_set(v___x_5902_, 1, v___x_5901_);
                        leanh::lean_inc_ref(v_code_5874_);
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
                if leanh::lean_obj_tag(v___y_5915_) == 0 {
                    leanh::lean_dec_ref_known(v___y_5915_, 1);
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
                    leanh::lean_dec(v___y_5914_);
                    leanh::lean_dec(v___y_5911_);
                    leanh::lean_del_object(v___x_5855_);
                    leanh::lean_dec(v_snd_5853_);
                    leanh::lean_dec(v_typeName_5832_);
                    v_a_5916_ = leanh::lean_ctor_get(v___y_5915_, 0);
                    v_isSharedCheck_5923_ = (!leanh::lean_is_exclusive(v___y_5915_)) as u8;
                    if v_isSharedCheck_5923_ == 0 {
                        v___x_5918_ = v___y_5915_;
                        v_isShared_5919_ = v_isSharedCheck_5923_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5916_);
                        leanh::lean_dec(v___y_5915_);
                        v___x_5918_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_a_5916_);
                    v___x_5921_ = v_reuseFailAlloc_5922_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5921_;
            }
            11 => {
                v___x_5933_ = leanh::lean_unsigned_to_nat(0);
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
                    v___x_5936_ = leanh::lean_box(0);
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
                    v___x_5956_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                    leanh::lean_inc(v_ctorName_5872_);
                    v___x_5957_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                    v___x_5958_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5958_, 0, v___x_5956_);
                    leanh::lean_ctor_set(v___x_5958_, 1, v___x_5957_);
                    v___x_5959_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3);
                    v___x_5960_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5960_, 0, v___x_5958_);
                    leanh::lean_ctor_set(v___x_5960_, 1, v___x_5959_);
                    v___x_5961_ = l_Nat_reprFast(v_numFields_5945_);
                    v___x_5962_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5962_, 0, v___x_5961_);
                    v___x_5963_ = l_Lean_MessageData_ofFormat(v___x_5962_);
                    v___x_5964_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5964_, 0, v___x_5960_);
                    leanh::lean_ctor_set(v___x_5964_, 1, v___x_5963_);
                    v___x_5965_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5);
                    v___x_5966_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5966_, 0, v___x_5964_);
                    leanh::lean_ctor_set(v___x_5966_, 1, v___x_5965_);
                    v___x_5967_ = l_Nat_reprFast(v___x_5954_);
                    v___x_5968_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5968_, 0, v___x_5967_);
                    v___x_5969_ = l_Lean_MessageData_ofFormat(v___x_5968_);
                    v___x_5970_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5970_, 0, v___x_5966_);
                    leanh::lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                    v___x_5971_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7);
                    v___x_5972_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5972_, 0, v___x_5970_);
                    leanh::lean_ctor_set(v___x_5972_, 1, v___x_5971_);
                    v___x_5973_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5972_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_);
                    if leanh::lean_obj_tag(v___x_5973_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5973_, 1);
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
                        leanh::lean_dec(v___y_5946_);
                        leanh::lean_del_object(v___x_5855_);
                        leanh::lean_dec(v_snd_5853_);
                        leanh::lean_dec(v_typeName_5832_);
                        v_a_5974_ = leanh::lean_ctor_get(v___x_5973_, 0);
                        v_isSharedCheck_5981_ =
                            (!leanh::lean_is_exclusive(v___x_5973_)) as u8;
                        if v_isSharedCheck_5981_ == 0 {
                            v___x_5976_ = v___x_5973_;
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5974_);
                            leanh::lean_dec(v___x_5973_);
                            v___x_5976_ = leanh::lean_box(0);
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_numFields_5945_);
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
                    v_reuseFailAlloc_5980_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
                    v___x_5979_ = v_reuseFailAlloc_5980_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5979_;
            }
            15 => {
                leanh::lean_inc_n(v_ctorName_5872_, 2);
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
                if leanh::lean_obj_tag(v___x_5991_) == 0 {
                    v_a_5992_ = leanh::lean_ctor_get(v___x_5991_, 0);
                    leanh::lean_inc(v_a_5992_);
                    leanh::lean_dec_ref_known(v___x_5991_, 1);
                    if leanh::lean_obj_tag(v_a_5992_) == 6 {
                        v_val_5993_ = leanh::lean_ctor_get(v_a_5992_, 0);
                        leanh::lean_inc_ref(v_val_5993_);
                        leanh::lean_dec_ref_known(v_a_5992_, 1);
                        v_induct_5994_ = leanh::lean_ctor_get(v_val_5993_, 1);
                        leanh::lean_inc(v_induct_5994_);
                        v_numFields_5995_ = leanh::lean_ctor_get(v_val_5993_, 4);
                        leanh::lean_inc(v_numFields_5995_);
                        leanh::lean_dec_ref(v_val_5993_);
                        v___x_5996_ = lean_name_eq(v_induct_5994_, v_typeName_5832_);
                        leanh::lean_dec(v_induct_5994_);
                        if v___x_5996_ == 0 {
                            v___x_5997_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                            leanh::lean_inc(v_ctorName_5872_);
                            v___x_5998_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                            v___x_5999_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5999_, 0, v___x_5997_);
                            leanh::lean_ctor_set(v___x_5999_, 1, v___x_5998_);
                            v___x_6000_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9);
                            v___x_6001_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6001_, 0, v___x_5999_);
                            leanh::lean_ctor_set(v___x_6001_, 1, v___x_6000_);
                            leanh::lean_inc(v_typeName_5832_);
                            v___x_6002_ = l_Lean_MessageData_ofName(v_typeName_5832_);
                            v___x_6003_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6003_, 0, v___x_6001_);
                            leanh::lean_ctor_set(v___x_6003_, 1, v___x_6002_);
                            v___x_6004_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                            v___x_6005_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6005_, 0, v___x_6003_);
                            leanh::lean_ctor_set(v___x_6005_, 1, v___x_6004_);
                            v___x_6006_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6005_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
                            if leanh::lean_obj_tag(v___x_6006_) == 0 {
                                leanh::lean_dec_ref_known(v___x_6006_, 1);
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
                                leanh::lean_dec(v_numFields_5995_);
                                leanh::lean_dec(v___x_5990_);
                                leanh::lean_del_object(v___x_5855_);
                                leanh::lean_dec(v_snd_5853_);
                                leanh::lean_dec(v_typeName_5832_);
                                v_a_6007_ = leanh::lean_ctor_get(v___x_6006_, 0);
                                v_isSharedCheck_6014_ =
                                    (!leanh::lean_is_exclusive(v___x_6006_)) as u8;
                                if v_isSharedCheck_6014_ == 0 {
                                    v___x_6009_ = v___x_6006_;
                                    v_isShared_6010_ = v_isSharedCheck_6014_;
                                    state = 16;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6007_);
                                    leanh::lean_dec(v___x_6006_);
                                    v___x_6009_ = leanh::lean_box(0);
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
                        leanh::lean_dec(v_a_5992_);
                        leanh::lean_del_object(v___x_5855_);
                        v___x_6015_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                        leanh::lean_inc(v_ctorName_5872_);
                        v___x_6016_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                        v___x_6017_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6017_, 0, v___x_6015_);
                        leanh::lean_ctor_set(v___x_6017_, 1, v___x_6016_);
                        v___x_6018_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11);
                        v___x_6019_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6019_, 0, v___x_6017_);
                        leanh::lean_ctor_set(v___x_6019_, 1, v___x_6018_);
                        v___x_6020_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6019_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
                        if leanh::lean_obj_tag(v___x_6020_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6020_, 1);
                            v___x_6021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6021_, 0, v___x_5990_);
                            leanh::lean_ctor_set(v___x_6021_, 1, v_snd_5853_);
                            v_a_5846_ = v___x_6021_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5990_);
                            leanh::lean_dec(v_snd_5853_);
                            leanh::lean_dec(v_typeName_5832_);
                            v_a_6022_ = leanh::lean_ctor_get(v___x_6020_, 0);
                            v_isSharedCheck_6029_ =
                                (!leanh::lean_is_exclusive(v___x_6020_)) as u8;
                            if v_isSharedCheck_6029_ == 0 {
                                v___x_6024_ = v___x_6020_;
                                v_isShared_6025_ = v_isSharedCheck_6029_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6022_);
                                leanh::lean_dec(v___x_6020_);
                                v___x_6024_ = leanh::lean_box(0);
                                v_isShared_6025_ = v_isSharedCheck_6029_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5990_);
                    leanh::lean_del_object(v___x_5855_);
                    leanh::lean_dec(v_snd_5853_);
                    leanh::lean_dec(v_typeName_5832_);
                    v_a_6030_ = leanh::lean_ctor_get(v___x_5991_, 0);
                    v_isSharedCheck_6037_ = (!leanh::lean_is_exclusive(v___x_5991_)) as u8;
                    if v_isSharedCheck_6037_ == 0 {
                        v___x_6032_ = v___x_5991_;
                        v_isShared_6033_ = v_isSharedCheck_6037_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6030_);
                        leanh::lean_dec(v___x_5991_);
                        v___x_6032_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6013_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_a_6007_);
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
                    v_reuseFailAlloc_6028_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
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
                    v_reuseFailAlloc_6036_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_a_6030_);
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
                    v_reuseFailAlloc_6052_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_a_6046_);
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
                    v_reuseFailAlloc_6060_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6060_, 0, v_a_6054_);
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
                    v_reuseFailAlloc_6072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
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
    mut v_c_6075_: *mut leanh::LeanObject,
    mut v_a_6076_: *mut leanh::LeanObject,
    mut v_a_6077_: *mut leanh::LeanObject,
    mut v_a_6078_: *mut leanh::LeanObject,
    mut v_a_6079_: *mut leanh::LeanObject,
    mut v_a_6080_: *mut leanh::LeanObject,
    mut v_a_6081_: *mut leanh::LeanObject,
    mut v_a_6082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_typeName_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6089_: usize = 0;
    let mut v___x_6090_: usize = 0;
    let mut v___x_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6094_: u8 = 0;
    let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut v_unused_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6104_: u8 = 0;
    let mut v___x_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_6084_ = leanh::lean_ctor_get(v_c_6075_, 0);
                leanh::lean_inc(v_typeName_6084_);
                v_discr_6085_ = leanh::lean_ctor_get(v_c_6075_, 2);
                leanh::lean_inc(v_discr_6085_);
                v_alts_6086_ = leanh::lean_ctor_get(v_c_6075_, 3);
                leanh::lean_inc_ref(v_alts_6086_);
                leanh::lean_dec_ref(v_c_6075_);
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
                if leanh::lean_obj_tag(v___x_6087_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6087_, 1);
                    v___x_6088_ = leanh::lean_obj_once(
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
                    leanh::lean_dec_ref(v_alts_6086_);
                    if leanh::lean_obj_tag(v___x_6091_) == 0 {
                        v_isSharedCheck_6099_ =
                            (!leanh::lean_is_exclusive(v___x_6091_)) as u8;
                        if v_isSharedCheck_6099_ == 0 {
                            v_unused_6100_ = leanh::lean_ctor_get(v___x_6091_, 0);
                            leanh::lean_dec(v_unused_6100_);
                            v___x_6093_ = v___x_6091_;
                            v_isShared_6094_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6091_);
                            v___x_6093_ = leanh::lean_box(0);
                            v_isShared_6094_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6101_ = leanh::lean_ctor_get(v___x_6091_, 0);
                        v_isSharedCheck_6108_ =
                            (!leanh::lean_is_exclusive(v___x_6091_)) as u8;
                        if v_isSharedCheck_6108_ == 0 {
                            v___x_6103_ = v___x_6091_;
                            v_isShared_6104_ = v_isSharedCheck_6108_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6101_);
                            leanh::lean_dec(v___x_6091_);
                            v___x_6103_ = leanh::lean_box(0);
                            v_isShared_6104_ = v_isSharedCheck_6108_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_alts_6086_);
                    leanh::lean_dec(v_typeName_6084_);
                    return v___x_6087_;
                }
            }
            1 => {
                v___x_6095_ = leanh::lean_box(0);
                if v_isShared_6094_ == 0 {
                    leanh::lean_ctor_set(v___x_6093_, 0, v___x_6095_);
                    v___x_6097_ = v___x_6093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6098_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6098_, 0, v___x_6095_);
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
                    v_reuseFailAlloc_6107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6107_, 0, v_a_6101_);
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
    mut v_code_6109_: *mut leanh::LeanObject,
    mut v_a_6110_: *mut leanh::LeanObject,
    mut v_a_6111_: *mut leanh::LeanObject,
    mut v_a_6112_: *mut leanh::LeanObject,
    mut v_a_6113_: *mut leanh::LeanObject,
    mut v_a_6114_: *mut leanh::LeanObject,
    mut v_a_6115_: *mut leanh::LeanObject,
    mut v_a_6116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6122_: u8 = 0;
    let mut v_decl_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6127_: u8 = 0;
    let mut v___x_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v_decl_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6143_: u8 = 0;
    let mut v_jps_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6156_: u8 = 0;
    let mut v_decl_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6161_: u8 = 0;
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6172_: u8 = 0;
    let mut v_fvarId_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___y_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6191_: u8 = 0;
    let mut v___x_6192_: u8 = 0;
    let mut v___x_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: u8 = 0;
    let mut v_binderName_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6224_: u8 = 0;
    let mut v___x_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6228_: u8 = 0;
    let mut v_isSharedCheck_6229_: u8 = 0;
    let mut v_unused_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut v_cases_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6240_: u8 = 0;
    let mut v_unused_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6118_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__0;
                v___x_6119_ = l_Lean_Core_checkSystem(v___x_6118_, v_a_6115_, v_a_6116_);
                if leanh::lean_obj_tag(v___x_6119_) == 0 {
                    v_isSharedCheck_6240_ = (!leanh::lean_is_exclusive(v___x_6119_)) as u8;
                    if v_isSharedCheck_6240_ == 0 {
                        v_unused_6241_ = leanh::lean_ctor_get(v___x_6119_, 0);
                        leanh::lean_dec(v_unused_6241_);
                        v___x_6121_ = v___x_6119_;
                        v_isShared_6122_ = v_isSharedCheck_6240_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6119_);
                        v___x_6121_ = leanh::lean_box(0);
                        v_isShared_6122_ = v_isSharedCheck_6240_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_6110_);
                    leanh::lean_dec_ref(v_code_6109_);
                    return v___x_6119_;
                }
            }
            1 => match leanh::lean_obj_tag(v_code_6109_) {
                0 => {
                    leanh::lean_del_object(v___x_6121_);
                    v_decl_6123_ = leanh::lean_ctor_get(v_code_6109_, 0);
                    v_k_6124_ = leanh::lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6138_ = (!leanh::lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6138_ == 0 {
                        v___x_6126_ = v_code_6109_;
                        v_isShared_6127_ = v_isSharedCheck_6138_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_6124_);
                        leanh::lean_inc(v_decl_6123_);
                        leanh::lean_dec(v_code_6109_);
                        v___x_6126_ = leanh::lean_box(0);
                        v_isShared_6127_ = v_isSharedCheck_6138_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_6121_);
                    v_decl_6139_ = leanh::lean_ctor_get(v_code_6109_, 0);
                    v_k_6140_ = leanh::lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6156_ = (!leanh::lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6156_ == 0 {
                        v___x_6142_ = v_code_6109_;
                        v_isShared_6143_ = v_isSharedCheck_6156_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_6140_);
                        leanh::lean_inc(v_decl_6139_);
                        leanh::lean_dec(v_code_6109_);
                        v___x_6142_ = leanh::lean_box(0);
                        v_isShared_6143_ = v_isSharedCheck_6156_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    leanh::lean_del_object(v___x_6121_);
                    v_decl_6157_ = leanh::lean_ctor_get(v_code_6109_, 0);
                    v_k_6158_ = leanh::lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6172_ = (!leanh::lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6172_ == 0 {
                        v___x_6160_ = v_code_6109_;
                        v_isShared_6161_ = v_isSharedCheck_6172_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_6158_);
                        leanh::lean_inc(v_decl_6157_);
                        leanh::lean_dec(v_code_6109_);
                        v___x_6160_ = leanh::lean_box(0);
                        v_isShared_6161_ = v_isSharedCheck_6172_;
                        state = 6;
                        continue;
                    }
                }
                3 => {
                    leanh::lean_del_object(v___x_6121_);
                    v_fvarId_6173_ = leanh::lean_ctor_get(v_code_6109_, 0);
                    v_args_6174_ = leanh::lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6231_ = (!leanh::lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6231_ == 0 {
                        v___x_6176_ = v_code_6109_;
                        v_isShared_6177_ = v_isSharedCheck_6231_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_args_6174_);
                        leanh::lean_inc(v_fvarId_6173_);
                        leanh::lean_dec(v_code_6109_);
                        v___x_6176_ = leanh::lean_box(0);
                        v_isShared_6177_ = v_isSharedCheck_6231_;
                        state = 8;
                        continue;
                    }
                }
                4 => {
                    leanh::lean_del_object(v___x_6121_);
                    v_cases_6232_ = leanh::lean_ctor_get(v_code_6109_, 0);
                    leanh::lean_inc_ref(v_cases_6232_);
                    leanh::lean_dec_ref_known(v_code_6109_, 1);
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
                    leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6233_;
                }
                5 => {
                    leanh::lean_del_object(v___x_6121_);
                    v_fvarId_6234_ = leanh::lean_ctor_get(v_code_6109_, 0);
                    leanh::lean_inc(v_fvarId_6234_);
                    leanh::lean_dec_ref_known(v_code_6109_, 1);
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
                    leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6235_;
                }
                _ => {
                    leanh::lean_dec_ref_known(v_code_6109_, 1);
                    leanh::lean_dec_ref(v_a_6110_);
                    v___x_6236_ = leanh::lean_box(0);
                    if v_isShared_6122_ == 0 {
                        leanh::lean_ctor_set(v___x_6121_, 0, v___x_6236_);
                        v___x_6238_ = v___x_6121_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_6239_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6239_, 0, v___x_6236_);
                        v___x_6238_ = v_reuseFailAlloc_6239_;
                        state = 15;
                        continue;
                    }
                }
            },
            2 => {
                leanh::lean_inc_ref(v_decl_6123_);
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
                if leanh::lean_obj_tag(v___x_6128_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6128_, 1);
                    v_fvarId_6129_ = leanh::lean_ctor_get(v_decl_6123_, 0);
                    leanh::lean_inc_n(v_fvarId_6129_, 2);
                    leanh::lean_dec_ref(v_decl_6123_);
                    v___x_6130_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6129_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if leanh::lean_obj_tag(v___x_6130_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6130_, 1);
                        v_jps_6131_ = leanh::lean_ctor_get(v_a_6110_, 0);
                        leanh::lean_inc(v_jps_6131_);
                        v_vars_6132_ = leanh::lean_ctor_get(v_a_6110_, 1);
                        leanh::lean_inc(v_vars_6132_);
                        leanh::lean_dec_ref(v_a_6110_);
                        v___x_6133_ = l_Lean_FVarIdSet_insert(v_vars_6132_, v_fvarId_6129_);
                        if v_isShared_6127_ == 0 {
                            leanh::lean_ctor_set(v___x_6126_, 1, v___x_6133_);
                            leanh::lean_ctor_set(v___x_6126_, 0, v_jps_6131_);
                            v___x_6135_ = v___x_6126_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6137_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_jps_6131_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6137_, 1, v___x_6133_);
                            v___x_6135_ = v_reuseFailAlloc_6137_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fvarId_6129_);
                        leanh::lean_del_object(v___x_6126_);
                        leanh::lean_dec_ref(v_k_6124_);
                        leanh::lean_dec_ref(v_a_6110_);
                        return v___x_6130_;
                    }
                } else {
                    leanh::lean_del_object(v___x_6126_);
                    leanh::lean_dec_ref(v_k_6124_);
                    leanh::lean_dec_ref(v_decl_6123_);
                    leanh::lean_dec_ref(v_a_6110_);
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
                v_jps_6144_ = leanh::lean_ctor_get(v_a_6110_, 0);
                leanh::lean_inc(v_jps_6144_);
                v_vars_6145_ = leanh::lean_ctor_get(v_a_6110_, 1);
                leanh::lean_inc_n(v_vars_6145_, 2);
                leanh::lean_dec_ref(v_a_6110_);
                v___x_6146_ = leanh::lean_box(1);
                if v_isShared_6143_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6142_, 0);
                    leanh::lean_ctor_set(v___x_6142_, 1, v_vars_6145_);
                    leanh::lean_ctor_set(v___x_6142_, 0, v___x_6146_);
                    v___x_6148_ = v___x_6142_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6155_, 0, v___x_6146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6155_, 1, v_vars_6145_);
                    v___x_6148_ = v_reuseFailAlloc_6155_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v_decl_6139_);
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
                leanh::lean_dec_ref(v___x_6148_);
                if leanh::lean_obj_tag(v___x_6149_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6149_, 1);
                    v_fvarId_6150_ = leanh::lean_ctor_get(v_decl_6139_, 0);
                    leanh::lean_inc_n(v_fvarId_6150_, 2);
                    leanh::lean_dec_ref(v_decl_6139_);
                    v___x_6151_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6150_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if leanh::lean_obj_tag(v___x_6151_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6151_, 1);
                        v___x_6152_ = l_Lean_FVarIdSet_insert(v_vars_6145_, v_fvarId_6150_);
                        v___x_6153_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6153_, 0, v_jps_6144_);
                        leanh::lean_ctor_set(v___x_6153_, 1, v___x_6152_);
                        v_code_6109_ = v_k_6140_;
                        v_a_6110_ = v___x_6153_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_fvarId_6150_);
                        leanh::lean_dec(v_vars_6145_);
                        leanh::lean_dec(v_jps_6144_);
                        leanh::lean_dec_ref(v_k_6140_);
                        return v___x_6151_;
                    }
                } else {
                    leanh::lean_dec(v_vars_6145_);
                    leanh::lean_dec(v_jps_6144_);
                    leanh::lean_dec_ref(v_k_6140_);
                    leanh::lean_dec_ref(v_decl_6139_);
                    return v___x_6149_;
                }
            }
            6 => {
                leanh::lean_inc_ref(v_decl_6157_);
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
                if leanh::lean_obj_tag(v___x_6162_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6162_, 1);
                    v_fvarId_6163_ = leanh::lean_ctor_get(v_decl_6157_, 0);
                    leanh::lean_inc_n(v_fvarId_6163_, 2);
                    leanh::lean_dec_ref(v_decl_6157_);
                    v___x_6164_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6163_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if leanh::lean_obj_tag(v___x_6164_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6164_, 1);
                        v_jps_6165_ = leanh::lean_ctor_get(v_a_6110_, 0);
                        leanh::lean_inc(v_jps_6165_);
                        v_vars_6166_ = leanh::lean_ctor_get(v_a_6110_, 1);
                        leanh::lean_inc(v_vars_6166_);
                        leanh::lean_dec_ref(v_a_6110_);
                        v___x_6167_ = l_Lean_FVarIdSet_insert(v_jps_6165_, v_fvarId_6163_);
                        if v_isShared_6161_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_6160_, 0);
                            leanh::lean_ctor_set(v___x_6160_, 1, v_vars_6166_);
                            leanh::lean_ctor_set(v___x_6160_, 0, v___x_6167_);
                            v___x_6169_ = v___x_6160_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_6171_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6171_, 0, v___x_6167_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6171_, 1, v_vars_6166_);
                            v___x_6169_ = v_reuseFailAlloc_6171_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fvarId_6163_);
                        leanh::lean_del_object(v___x_6160_);
                        leanh::lean_dec_ref(v_k_6158_);
                        leanh::lean_dec_ref(v_a_6110_);
                        return v___x_6164_;
                    }
                } else {
                    leanh::lean_del_object(v___x_6160_);
                    leanh::lean_dec_ref(v_k_6158_);
                    leanh::lean_dec_ref(v_decl_6157_);
                    leanh::lean_dec_ref(v_a_6110_);
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
                leanh::lean_inc(v_fvarId_6173_);
                v___x_6188_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
                    v_fvarId_6173_,
                    v_a_6110_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                if leanh::lean_obj_tag(v___x_6188_) == 0 {
                    v_isSharedCheck_6229_ = (!leanh::lean_is_exclusive(v___x_6188_)) as u8;
                    if v_isSharedCheck_6229_ == 0 {
                        v_unused_6230_ = leanh::lean_ctor_get(v___x_6188_, 0);
                        leanh::lean_dec(v_unused_6230_);
                        v___x_6190_ = v___x_6188_;
                        v_isShared_6191_ = v_isSharedCheck_6229_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6188_);
                        v___x_6190_ = leanh::lean_box(0);
                        v_isShared_6191_ = v_isSharedCheck_6229_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6176_);
                    leanh::lean_dec_ref(v_args_6174_);
                    leanh::lean_dec(v_fvarId_6173_);
                    leanh::lean_dec_ref(v_a_6110_);
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
                leanh::lean_dec_ref(v___y_6179_);
                return v___x_6187_;
            }
            10 => {
                v___x_6192_ = 0;
                leanh::lean_inc(v_fvarId_6173_);
                v___x_6193_ = l_Lean_Compiler_LCNF_getFunDecl(
                    v___x_6192_,
                    v_fvarId_6173_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                if leanh::lean_obj_tag(v___x_6193_) == 0 {
                    v_a_6194_ = leanh::lean_ctor_get(v___x_6193_, 0);
                    leanh::lean_inc(v_a_6194_);
                    leanh::lean_dec_ref_known(v___x_6193_, 1);
                    v___x_6195_ = l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(v_a_6194_);
                    v___x_6196_ = lean_array_get_size(v_args_6174_);
                    v___x_6197_ = lean_nat_dec_eq(v___x_6195_, v___x_6196_);
                    if v___x_6197_ == 0 {
                        v_binderName_6198_ = leanh::lean_ctor_get(v_a_6194_, 1);
                        leanh::lean_inc(v_binderName_6198_);
                        leanh::lean_dec(v_a_6194_);
                        v___x_6199_ = leanh::lean_obj_once(
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
                            leanh::lean_ctor_set_tag(v___x_6176_, 7);
                            leanh::lean_ctor_set(v___x_6176_, 1, v___x_6200_);
                            leanh::lean_ctor_set(v___x_6176_, 0, v___x_6199_);
                            v___x_6202_ = v___x_6176_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_6220_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6220_, 0, v___x_6199_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6220_, 1, v___x_6200_);
                            v___x_6202_ = v_reuseFailAlloc_6220_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_6195_);
                        leanh::lean_dec(v_a_6194_);
                        leanh::lean_del_object(v___x_6190_);
                        leanh::lean_del_object(v___x_6176_);
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
                    leanh::lean_del_object(v___x_6190_);
                    leanh::lean_del_object(v___x_6176_);
                    leanh::lean_dec_ref(v_args_6174_);
                    leanh::lean_dec(v_fvarId_6173_);
                    leanh::lean_dec_ref(v_a_6110_);
                    v_a_6221_ = leanh::lean_ctor_get(v___x_6193_, 0);
                    v_isSharedCheck_6228_ = (!leanh::lean_is_exclusive(v___x_6193_)) as u8;
                    if v_isSharedCheck_6228_ == 0 {
                        v___x_6223_ = v___x_6193_;
                        v_isShared_6224_ = v_isSharedCheck_6228_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6221_);
                        leanh::lean_dec(v___x_6193_);
                        v___x_6223_ = leanh::lean_box(0);
                        v_isShared_6224_ = v_isSharedCheck_6228_;
                        state = 13;
                        continue;
                    }
                }
            }
            11 => {
                v___x_6203_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__4_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__4,
                );
                v___x_6204_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6204_, 0, v___x_6202_);
                leanh::lean_ctor_set(v___x_6204_, 1, v___x_6203_);
                v___x_6205_ = l_Nat_reprFast(v___x_6195_);
                if v_isShared_6191_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6190_, 3);
                    leanh::lean_ctor_set(v___x_6190_, 0, v___x_6205_);
                    v___x_6207_ = v___x_6190_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6219_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6219_, 0, v___x_6205_);
                    v___x_6207_ = v_reuseFailAlloc_6219_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6208_ = l_Lean_MessageData_ofFormat(v___x_6207_);
                v___x_6209_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6209_, 0, v___x_6204_);
                leanh::lean_ctor_set(v___x_6209_, 1, v___x_6208_);
                v___x_6210_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__6_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__6,
                );
                v___x_6211_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6211_, 0, v___x_6209_);
                leanh::lean_ctor_set(v___x_6211_, 1, v___x_6210_);
                v___x_6212_ = l_Nat_reprFast(v___x_6196_);
                v___x_6213_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6213_, 0, v___x_6212_);
                v___x_6214_ = l_Lean_MessageData_ofFormat(v___x_6213_);
                v___x_6215_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6215_, 0, v___x_6211_);
                leanh::lean_ctor_set(v___x_6215_, 1, v___x_6214_);
                v___x_6216_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__8_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__8,
                );
                v___x_6217_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6217_, 0, v___x_6215_);
                leanh::lean_ctor_set(v___x_6217_, 1, v___x_6216_);
                v___x_6218_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6217_, v_a_6113_, v_a_6114_, v_a_6115_, v_a_6116_);
                if leanh::lean_obj_tag(v___x_6218_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6218_, 1);
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
                    leanh::lean_dec_ref(v_args_6174_);
                    leanh::lean_dec(v_fvarId_6173_);
                    leanh::lean_dec_ref(v_a_6110_);
                    return v___x_6218_;
                }
            }
            13 => {
                if v_isShared_6224_ == 0 {
                    v___x_6226_ = v___x_6223_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_a_6221_);
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
    mut v_value_6242_: *mut leanh::LeanObject,
    mut v___x_6243_: *mut leanh::LeanObject,
    mut v___y_6244_: *mut leanh::LeanObject,
    mut v___y_6245_: *mut leanh::LeanObject,
    mut v___y_6246_: *mut leanh::LeanObject,
    mut v___y_6247_: *mut leanh::LeanObject,
    mut v___y_6248_: *mut leanh::LeanObject,
    mut v___y_6249_: *mut leanh::LeanObject,
    mut v___y_6250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v___x_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6259_: u8 = 0;
    let mut v_unused_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_6252_) == 0 {
                    v_isSharedCheck_6259_ = (!leanh::lean_is_exclusive(v___x_6252_)) as u8;
                    if v_isSharedCheck_6259_ == 0 {
                        v_unused_6260_ = leanh::lean_ctor_get(v___x_6252_, 0);
                        leanh::lean_dec(v_unused_6260_);
                        v___x_6254_ = v___x_6252_;
                        v_isShared_6255_ = v_isSharedCheck_6259_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6252_);
                        v___x_6254_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_6254_, 0, v___x_6243_);
                    v___x_6257_ = v___x_6254_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6258_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6258_, 0, v___x_6243_);
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
    mut v_value_6261_: *mut leanh::LeanObject,
    mut v___x_6262_: *mut leanh::LeanObject,
    mut v___y_6263_: *mut leanh::LeanObject,
    mut v___y_6264_: *mut leanh::LeanObject,
    mut v___y_6265_: *mut leanh::LeanObject,
    mut v___y_6266_: *mut leanh::LeanObject,
    mut v___y_6267_: *mut leanh::LeanObject,
    mut v___y_6268_: *mut leanh::LeanObject,
    mut v___y_6269_: *mut leanh::LeanObject,
    mut v___y_6270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_6269_);
    leanh::lean_dec_ref(v___y_6268_);
    leanh::lean_dec(v___y_6267_);
    leanh::lean_dec_ref(v___y_6266_);
    leanh::lean_dec_ref(v___y_6265_);
    leanh::lean_dec(v___y_6264_);
    return v_res_6271_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkCases___boxed(
    mut v_c_6272_: *mut leanh::LeanObject,
    mut v_a_6273_: *mut leanh::LeanObject,
    mut v_a_6274_: *mut leanh::LeanObject,
    mut v_a_6275_: *mut leanh::LeanObject,
    mut v_a_6276_: *mut leanh::LeanObject,
    mut v_a_6277_: *mut leanh::LeanObject,
    mut v_a_6278_: *mut leanh::LeanObject,
    mut v_a_6279_: *mut leanh::LeanObject,
    mut v_a_6280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6281_ = l_Lean_Compiler_LCNF_Check_Pure_checkCases(
        v_c_6272_, v_a_6273_, v_a_6274_, v_a_6275_, v_a_6276_, v_a_6277_, v_a_6278_, v_a_6279_,
    );
    leanh::lean_dec(v_a_6279_);
    leanh::lean_dec_ref(v_a_6278_);
    leanh::lean_dec(v_a_6277_);
    leanh::lean_dec_ref(v_a_6276_);
    leanh::lean_dec_ref(v_a_6275_);
    leanh::lean_dec(v_a_6274_);
    leanh::lean_dec_ref(v_a_6273_);
    return v_res_6281_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___boxed(
    mut v_funDecl_6282_: *mut leanh::LeanObject,
    mut v_a_6283_: *mut leanh::LeanObject,
    mut v_a_6284_: *mut leanh::LeanObject,
    mut v_a_6285_: *mut leanh::LeanObject,
    mut v_a_6286_: *mut leanh::LeanObject,
    mut v_a_6287_: *mut leanh::LeanObject,
    mut v_a_6288_: *mut leanh::LeanObject,
    mut v_a_6289_: *mut leanh::LeanObject,
    mut v_a_6290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_6289_);
    leanh::lean_dec_ref(v_a_6288_);
    leanh::lean_dec(v_a_6287_);
    leanh::lean_dec_ref(v_a_6286_);
    leanh::lean_dec_ref(v_a_6285_);
    leanh::lean_dec(v_a_6284_);
    leanh::lean_dec_ref(v_a_6283_);
    return v_res_6291_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_check___boxed(
    mut v_code_6292_: *mut leanh::LeanObject,
    mut v_a_6293_: *mut leanh::LeanObject,
    mut v_a_6294_: *mut leanh::LeanObject,
    mut v_a_6295_: *mut leanh::LeanObject,
    mut v_a_6296_: *mut leanh::LeanObject,
    mut v_a_6297_: *mut leanh::LeanObject,
    mut v_a_6298_: *mut leanh::LeanObject,
    mut v_a_6299_: *mut leanh::LeanObject,
    mut v_a_6300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_6299_);
    leanh::lean_dec_ref(v_a_6298_);
    leanh::lean_dec(v_a_6297_);
    leanh::lean_dec_ref(v_a_6296_);
    leanh::lean_dec_ref(v_a_6295_);
    leanh::lean_dec(v_a_6294_);
    return v_res_6301_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed(
    mut v_declName_6302_: *mut leanh::LeanObject,
    mut v_params_6303_: *mut leanh::LeanObject,
    mut v_type_6304_: *mut leanh::LeanObject,
    mut v_value_6305_: *mut leanh::LeanObject,
    mut v_a_6306_: *mut leanh::LeanObject,
    mut v_a_6307_: *mut leanh::LeanObject,
    mut v_a_6308_: *mut leanh::LeanObject,
    mut v_a_6309_: *mut leanh::LeanObject,
    mut v_a_6310_: *mut leanh::LeanObject,
    mut v_a_6311_: *mut leanh::LeanObject,
    mut v_a_6312_: *mut leanh::LeanObject,
    mut v_a_6313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_6312_);
    leanh::lean_dec_ref(v_a_6311_);
    leanh::lean_dec(v_a_6310_);
    leanh::lean_dec_ref(v_a_6309_);
    leanh::lean_dec_ref(v_a_6308_);
    leanh::lean_dec(v_a_6307_);
    leanh::lean_dec_ref(v_a_6306_);
    return v_res_6314_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___boxed(
    mut v_typeName_6315_: *mut leanh::LeanObject,
    mut v_as_6316_: *mut leanh::LeanObject,
    mut v_sz_6317_: *mut leanh::LeanObject,
    mut v_i_6318_: *mut leanh::LeanObject,
    mut v_b_6319_: *mut leanh::LeanObject,
    mut v___y_6320_: *mut leanh::LeanObject,
    mut v___y_6321_: *mut leanh::LeanObject,
    mut v___y_6322_: *mut leanh::LeanObject,
    mut v___y_6323_: *mut leanh::LeanObject,
    mut v___y_6324_: *mut leanh::LeanObject,
    mut v___y_6325_: *mut leanh::LeanObject,
    mut v___y_6326_: *mut leanh::LeanObject,
    mut v___y_6327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6328_: usize = 0;
    let mut v_i_boxed_6329_: usize = 0;
    let mut v_res_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6328_ = leanh::lean_unbox_usize(v_sz_6317_);
    leanh::lean_dec(v_sz_6317_);
    v_i_boxed_6329_ = leanh::lean_unbox_usize(v_i_6318_);
    leanh::lean_dec(v_i_6318_);
    v_res_6330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5(v_typeName_6315_, v_as_6316_, v_sz_boxed_6328_, v_i_boxed_6329_, v_b_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_, v___y_6324_, v___y_6325_, v___y_6326_);
    leanh::lean_dec(v___y_6326_);
    leanh::lean_dec_ref(v___y_6325_);
    leanh::lean_dec(v___y_6324_);
    leanh::lean_dec_ref(v___y_6323_);
    leanh::lean_dec_ref(v___y_6322_);
    leanh::lean_dec(v___y_6321_);
    leanh::lean_dec_ref(v___y_6320_);
    leanh::lean_dec_ref(v_as_6316_);
    return v_res_6330_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(
    mut v_as_6331_: *mut leanh::LeanObject,
    mut v_i_6332_: usize,
    mut v_stop_6333_: usize,
    mut v_b_6334_: *mut leanh::LeanObject,
    mut v___y_6335_: *mut leanh::LeanObject,
    mut v___y_6336_: *mut leanh::LeanObject,
    mut v___y_6337_: *mut leanh::LeanObject,
    mut v___y_6338_: *mut leanh::LeanObject,
    mut v___y_6339_: *mut leanh::LeanObject,
    mut v___y_6340_: *mut leanh::LeanObject,
    mut v___y_6341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_as_6331_, v_i_6332_, v_stop_6333_, v_b_6334_, v___y_6336_, v___y_6338_, v___y_6339_, v___y_6340_, v___y_6341_);
    return v___x_6343_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___boxed(
    mut v_as_6344_: *mut leanh::LeanObject,
    mut v_i_6345_: *mut leanh::LeanObject,
    mut v_stop_6346_: *mut leanh::LeanObject,
    mut v_b_6347_: *mut leanh::LeanObject,
    mut v___y_6348_: *mut leanh::LeanObject,
    mut v___y_6349_: *mut leanh::LeanObject,
    mut v___y_6350_: *mut leanh::LeanObject,
    mut v___y_6351_: *mut leanh::LeanObject,
    mut v___y_6352_: *mut leanh::LeanObject,
    mut v___y_6353_: *mut leanh::LeanObject,
    mut v___y_6354_: *mut leanh::LeanObject,
    mut v___y_6355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6356_: usize = 0;
    let mut v_stop_boxed_6357_: usize = 0;
    let mut v_res_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6356_ = leanh::lean_unbox_usize(v_i_6345_);
    leanh::lean_dec(v_i_6345_);
    v_stop_boxed_6357_ = leanh::lean_unbox_usize(v_stop_6346_);
    leanh::lean_dec(v_stop_6346_);
    v_res_6358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(v_as_6344_, v_i_boxed_6356_, v_stop_boxed_6357_, v_b_6347_, v___y_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_);
    leanh::lean_dec(v___y_6354_);
    leanh::lean_dec_ref(v___y_6353_);
    leanh::lean_dec(v___y_6352_);
    leanh::lean_dec_ref(v___y_6351_);
    leanh::lean_dec_ref(v___y_6350_);
    leanh::lean_dec(v___y_6349_);
    leanh::lean_dec_ref(v___y_6348_);
    leanh::lean_dec_ref(v_as_6344_);
    return v_res_6358_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4(
    mut v_00_u03b1_6359_: *mut leanh::LeanObject,
    mut v_constName_6360_: *mut leanh::LeanObject,
    mut v___y_6361_: *mut leanh::LeanObject,
    mut v___y_6362_: *mut leanh::LeanObject,
    mut v___y_6363_: *mut leanh::LeanObject,
    mut v___y_6364_: *mut leanh::LeanObject,
    mut v___y_6365_: *mut leanh::LeanObject,
    mut v___y_6366_: *mut leanh::LeanObject,
    mut v___y_6367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6369_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_6360_, v___y_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_, v___y_6367_);
    return v___x_6369_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___boxed(
    mut v_00_u03b1_6370_: *mut leanh::LeanObject,
    mut v_constName_6371_: *mut leanh::LeanObject,
    mut v___y_6372_: *mut leanh::LeanObject,
    mut v___y_6373_: *mut leanh::LeanObject,
    mut v___y_6374_: *mut leanh::LeanObject,
    mut v___y_6375_: *mut leanh::LeanObject,
    mut v___y_6376_: *mut leanh::LeanObject,
    mut v___y_6377_: *mut leanh::LeanObject,
    mut v___y_6378_: *mut leanh::LeanObject,
    mut v___y_6379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6380_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4(v_00_u03b1_6370_, v_constName_6371_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_);
    leanh::lean_dec(v___y_6378_);
    leanh::lean_dec_ref(v___y_6377_);
    leanh::lean_dec(v___y_6376_);
    leanh::lean_dec_ref(v___y_6375_);
    leanh::lean_dec_ref(v___y_6374_);
    leanh::lean_dec(v___y_6373_);
    leanh::lean_dec_ref(v___y_6372_);
    return v_res_6380_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6(
    mut v_00_u03b1_6381_: *mut leanh::LeanObject,
    mut v_ref_6382_: *mut leanh::LeanObject,
    mut v_constName_6383_: *mut leanh::LeanObject,
    mut v___y_6384_: *mut leanh::LeanObject,
    mut v___y_6385_: *mut leanh::LeanObject,
    mut v___y_6386_: *mut leanh::LeanObject,
    mut v___y_6387_: *mut leanh::LeanObject,
    mut v___y_6388_: *mut leanh::LeanObject,
    mut v___y_6389_: *mut leanh::LeanObject,
    mut v___y_6390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6392_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_6382_, v_constName_6383_, v___y_6384_, v___y_6385_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
    return v___x_6392_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___boxed(
    mut v_00_u03b1_6393_: *mut leanh::LeanObject,
    mut v_ref_6394_: *mut leanh::LeanObject,
    mut v_constName_6395_: *mut leanh::LeanObject,
    mut v___y_6396_: *mut leanh::LeanObject,
    mut v___y_6397_: *mut leanh::LeanObject,
    mut v___y_6398_: *mut leanh::LeanObject,
    mut v___y_6399_: *mut leanh::LeanObject,
    mut v___y_6400_: *mut leanh::LeanObject,
    mut v___y_6401_: *mut leanh::LeanObject,
    mut v___y_6402_: *mut leanh::LeanObject,
    mut v___y_6403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6404_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6(v_00_u03b1_6393_, v_ref_6394_, v_constName_6395_, v___y_6396_, v___y_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_);
    leanh::lean_dec(v___y_6402_);
    leanh::lean_dec_ref(v___y_6401_);
    leanh::lean_dec(v___y_6400_);
    leanh::lean_dec_ref(v___y_6399_);
    leanh::lean_dec_ref(v___y_6398_);
    leanh::lean_dec(v___y_6397_);
    leanh::lean_dec_ref(v___y_6396_);
    leanh::lean_dec(v_ref_6394_);
    return v_res_6404_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8(
    mut v_00_u03b1_6405_: *mut leanh::LeanObject,
    mut v_ref_6406_: *mut leanh::LeanObject,
    mut v_msg_6407_: *mut leanh::LeanObject,
    mut v_declHint_6408_: *mut leanh::LeanObject,
    mut v___y_6409_: *mut leanh::LeanObject,
    mut v___y_6410_: *mut leanh::LeanObject,
    mut v___y_6411_: *mut leanh::LeanObject,
    mut v___y_6412_: *mut leanh::LeanObject,
    mut v___y_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6417_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_6406_, v_msg_6407_, v_declHint_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_);
    return v___x_6417_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_6418_: *mut leanh::LeanObject,
    mut v_ref_6419_: *mut leanh::LeanObject,
    mut v_msg_6420_: *mut leanh::LeanObject,
    mut v_declHint_6421_: *mut leanh::LeanObject,
    mut v___y_6422_: *mut leanh::LeanObject,
    mut v___y_6423_: *mut leanh::LeanObject,
    mut v___y_6424_: *mut leanh::LeanObject,
    mut v___y_6425_: *mut leanh::LeanObject,
    mut v___y_6426_: *mut leanh::LeanObject,
    mut v___y_6427_: *mut leanh::LeanObject,
    mut v___y_6428_: *mut leanh::LeanObject,
    mut v___y_6429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6430_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8(v_00_u03b1_6418_, v_ref_6419_, v_msg_6420_, v_declHint_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_);
    leanh::lean_dec(v___y_6428_);
    leanh::lean_dec_ref(v___y_6427_);
    leanh::lean_dec(v___y_6426_);
    leanh::lean_dec_ref(v___y_6425_);
    leanh::lean_dec_ref(v___y_6424_);
    leanh::lean_dec(v___y_6423_);
    leanh::lean_dec_ref(v___y_6422_);
    leanh::lean_dec(v_ref_6419_);
    return v_res_6430_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10(
    mut v_msg_6431_: *mut leanh::LeanObject,
    mut v_declHint_6432_: *mut leanh::LeanObject,
    mut v___y_6433_: *mut leanh::LeanObject,
    mut v___y_6434_: *mut leanh::LeanObject,
    mut v___y_6435_: *mut leanh::LeanObject,
    mut v___y_6436_: *mut leanh::LeanObject,
    mut v___y_6437_: *mut leanh::LeanObject,
    mut v___y_6438_: *mut leanh::LeanObject,
    mut v___y_6439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6441_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_6431_, v_declHint_6432_, v___y_6439_);
    return v___x_6441_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___boxed(
    mut v_msg_6442_: *mut leanh::LeanObject,
    mut v_declHint_6443_: *mut leanh::LeanObject,
    mut v___y_6444_: *mut leanh::LeanObject,
    mut v___y_6445_: *mut leanh::LeanObject,
    mut v___y_6446_: *mut leanh::LeanObject,
    mut v___y_6447_: *mut leanh::LeanObject,
    mut v___y_6448_: *mut leanh::LeanObject,
    mut v___y_6449_: *mut leanh::LeanObject,
    mut v___y_6450_: *mut leanh::LeanObject,
    mut v___y_6451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6452_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10(v_msg_6442_, v_declHint_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_);
    leanh::lean_dec(v___y_6450_);
    leanh::lean_dec_ref(v___y_6449_);
    leanh::lean_dec(v___y_6448_);
    leanh::lean_dec_ref(v___y_6447_);
    leanh::lean_dec_ref(v___y_6446_);
    leanh::lean_dec(v___y_6445_);
    leanh::lean_dec_ref(v___y_6444_);
    return v_res_6452_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10(
    mut v_00_u03b1_6453_: *mut leanh::LeanObject,
    mut v_ref_6454_: *mut leanh::LeanObject,
    mut v_msg_6455_: *mut leanh::LeanObject,
    mut v___y_6456_: *mut leanh::LeanObject,
    mut v___y_6457_: *mut leanh::LeanObject,
    mut v___y_6458_: *mut leanh::LeanObject,
    mut v___y_6459_: *mut leanh::LeanObject,
    mut v___y_6460_: *mut leanh::LeanObject,
    mut v___y_6461_: *mut leanh::LeanObject,
    mut v___y_6462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6464_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_6454_, v_msg_6455_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_);
    return v___x_6464_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___boxed(
    mut v_00_u03b1_6465_: *mut leanh::LeanObject,
    mut v_ref_6466_: *mut leanh::LeanObject,
    mut v_msg_6467_: *mut leanh::LeanObject,
    mut v___y_6468_: *mut leanh::LeanObject,
    mut v___y_6469_: *mut leanh::LeanObject,
    mut v___y_6470_: *mut leanh::LeanObject,
    mut v___y_6471_: *mut leanh::LeanObject,
    mut v___y_6472_: *mut leanh::LeanObject,
    mut v___y_6473_: *mut leanh::LeanObject,
    mut v___y_6474_: *mut leanh::LeanObject,
    mut v___y_6475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6476_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_6465_, v_ref_6466_, v_msg_6467_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_);
    leanh::lean_dec(v___y_6474_);
    leanh::lean_dec_ref(v___y_6473_);
    leanh::lean_dec(v___y_6472_);
    leanh::lean_dec_ref(v___y_6471_);
    leanh::lean_dec_ref(v___y_6470_);
    leanh::lean_dec(v___y_6469_);
    leanh::lean_dec_ref(v___y_6468_);
    leanh::lean_dec(v_ref_6466_);
    return v_res_6476_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6479_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6479_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6480_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1_once),
        _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1,
    );
    v___x_6481_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6481_, 0, v___x_6480_);
    return v___x_6481_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6482_ = leanh::lean_box(1);
    v___x_6483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_6484_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2_once),
        _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2,
    );
    v___x_6485_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6485_, 0, v___x_6484_);
    leanh::lean_ctor_set(v___x_6485_, 1, v___x_6483_);
    leanh::lean_ctor_set(v___x_6485_, 2, v___x_6482_);
    return v___x_6485_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
    mut v_x_6486_: *mut leanh::LeanObject,
    mut v_a_6487_: *mut leanh::LeanObject,
    mut v_a_6488_: *mut leanh::LeanObject,
    mut v_a_6489_: *mut leanh::LeanObject,
    mut v_a_6490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6500_: u8 = 0;
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6492_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v___x_6493_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0;
                v___x_6494_ = lean_st_mk_ref(v___x_6492_);
                v___x_6495_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3,
                );
                leanh::lean_inc(v_a_6490_);
                leanh::lean_inc_ref(v_a_6489_);
                leanh::lean_inc(v_a_6488_);
                leanh::lean_inc_ref(v_a_6487_);
                leanh::lean_inc(v___x_6494_);
                v___x_6496_ = leanh::lean_apply_8(
                    v_x_6486_,
                    v___x_6493_,
                    v___x_6494_,
                    v___x_6495_,
                    v_a_6487_,
                    v_a_6488_,
                    v_a_6489_,
                    v_a_6490_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6496_) == 0 {
                    v_a_6497_ = leanh::lean_ctor_get(v___x_6496_, 0);
                    v_isSharedCheck_6505_ = (!leanh::lean_is_exclusive(v___x_6496_)) as u8;
                    if v_isSharedCheck_6505_ == 0 {
                        v___x_6499_ = v___x_6496_;
                        v_isShared_6500_ = v_isSharedCheck_6505_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6497_);
                        leanh::lean_dec(v___x_6496_);
                        v___x_6499_ = leanh::lean_box(0);
                        v_isShared_6500_ = v_isSharedCheck_6505_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_6494_);
                    return v___x_6496_;
                }
            }
            1 => {
                v___x_6501_ = lean_st_ref_get(v___x_6494_);
                leanh::lean_dec(v___x_6494_);
                leanh::lean_dec(v___x_6501_);
                if v_isShared_6500_ == 0 {
                    v___x_6503_ = v___x_6499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6504_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6497_);
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
    mut v_x_6506_: *mut leanh::LeanObject,
    mut v_a_6507_: *mut leanh::LeanObject,
    mut v_a_6508_: *mut leanh::LeanObject,
    mut v_a_6509_: *mut leanh::LeanObject,
    mut v_a_6510_: *mut leanh::LeanObject,
    mut v_a_6511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6512_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
        v_x_6506_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_,
    );
    leanh::lean_dec(v_a_6510_);
    leanh::lean_dec_ref(v_a_6509_);
    leanh::lean_dec(v_a_6508_);
    leanh::lean_dec_ref(v_a_6507_);
    return v_res_6512_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run(
    mut v_00_u03b1_6513_: *mut leanh::LeanObject,
    mut v_x_6514_: *mut leanh::LeanObject,
    mut v_a_6515_: *mut leanh::LeanObject,
    mut v_a_6516_: *mut leanh::LeanObject,
    mut v_a_6517_: *mut leanh::LeanObject,
    mut v_a_6518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6520_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
        v_x_6514_, v_a_6515_, v_a_6516_, v_a_6517_, v_a_6518_,
    );
    return v___x_6520_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run___boxed(
    mut v_00_u03b1_6521_: *mut leanh::LeanObject,
    mut v_x_6522_: *mut leanh::LeanObject,
    mut v_a_6523_: *mut leanh::LeanObject,
    mut v_a_6524_: *mut leanh::LeanObject,
    mut v_a_6525_: *mut leanh::LeanObject,
    mut v_a_6526_: *mut leanh::LeanObject,
    mut v_a_6527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6528_ = l_Lean_Compiler_LCNF_Check_Pure_run(
        v_00_u03b1_6521_,
        v_x_6522_,
        v_a_6523_,
        v_a_6524_,
        v_a_6525_,
        v_a_6526_,
    );
    leanh::lean_dec(v_a_6526_);
    leanh::lean_dec_ref(v_a_6525_);
    leanh::lean_dec(v_a_6524_);
    leanh::lean_dec_ref(v_a_6523_);
    return v_res_6528_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(
    mut v_f_6529_: *mut leanh::LeanObject,
    mut v_v_6530_: *mut leanh::LeanObject,
    mut v___y_6531_: *mut leanh::LeanObject,
    mut v___y_6532_: *mut leanh::LeanObject,
    mut v___y_6533_: *mut leanh::LeanObject,
    mut v___y_6534_: *mut leanh::LeanObject,
    mut v___y_6535_: *mut leanh::LeanObject,
    mut v___y_6536_: *mut leanh::LeanObject,
    mut v___y_6537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6543_: u8 = 0;
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6548_: u8 = 0;
    let mut v_unused_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_v_6530_) == 0 {
                    v_code_6539_ = leanh::lean_ctor_get(v_v_6530_, 0);
                    leanh::lean_inc_ref(v_code_6539_);
                    leanh::lean_dec_ref_known(v_v_6530_, 1);
                    leanh::lean_inc(v___y_6537_);
                    leanh::lean_inc_ref(v___y_6536_);
                    leanh::lean_inc(v___y_6535_);
                    leanh::lean_inc_ref(v___y_6534_);
                    leanh::lean_inc_ref(v___y_6533_);
                    leanh::lean_inc(v___y_6532_);
                    leanh::lean_inc_ref(v___y_6531_);
                    v___x_6540_ = leanh::lean_apply_9(
                        v_f_6529_,
                        v_code_6539_,
                        v___y_6531_,
                        v___y_6532_,
                        v___y_6533_,
                        v___y_6534_,
                        v___y_6535_,
                        v___y_6536_,
                        v___y_6537_,
                        leanh::lean_box(0),
                    );
                    return v___x_6540_;
                } else {
                    leanh::lean_dec_ref(v_f_6529_);
                    v_isSharedCheck_6548_ = (!leanh::lean_is_exclusive(v_v_6530_)) as u8;
                    if v_isSharedCheck_6548_ == 0 {
                        v_unused_6549_ = leanh::lean_ctor_get(v_v_6530_, 0);
                        leanh::lean_dec(v_unused_6549_);
                        v___x_6542_ = v_v_6530_;
                        v_isShared_6543_ = v_isSharedCheck_6548_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_v_6530_);
                        v___x_6542_ = leanh::lean_box(0);
                        v_isShared_6543_ = v_isSharedCheck_6548_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6544_ = leanh::lean_box(0);
                if v_isShared_6543_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6542_, 0);
                    leanh::lean_ctor_set(v___x_6542_, 0, v___x_6544_);
                    v___x_6546_ = v___x_6542_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6547_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6547_, 0, v___x_6544_);
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
    mut v_f_6550_: *mut leanh::LeanObject,
    mut v_v_6551_: *mut leanh::LeanObject,
    mut v___y_6552_: *mut leanh::LeanObject,
    mut v___y_6553_: *mut leanh::LeanObject,
    mut v___y_6554_: *mut leanh::LeanObject,
    mut v___y_6555_: *mut leanh::LeanObject,
    mut v___y_6556_: *mut leanh::LeanObject,
    mut v___y_6557_: *mut leanh::LeanObject,
    mut v___y_6558_: *mut leanh::LeanObject,
    mut v___y_6559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6560_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(v_f_6550_, v_v_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
    leanh::lean_dec(v___y_6558_);
    leanh::lean_dec_ref(v___y_6557_);
    leanh::lean_dec(v___y_6556_);
    leanh::lean_dec_ref(v___y_6555_);
    leanh::lean_dec_ref(v___y_6554_);
    leanh::lean_dec(v___y_6553_);
    leanh::lean_dec_ref(v___y_6552_);
    return v_res_6560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0(
    mut v_pu_6561_: u8,
    mut v_f_6562_: *mut leanh::LeanObject,
    mut v_v_6563_: *mut leanh::LeanObject,
    mut v___y_6564_: *mut leanh::LeanObject,
    mut v___y_6565_: *mut leanh::LeanObject,
    mut v___y_6566_: *mut leanh::LeanObject,
    mut v___y_6567_: *mut leanh::LeanObject,
    mut v___y_6568_: *mut leanh::LeanObject,
    mut v___y_6569_: *mut leanh::LeanObject,
    mut v___y_6570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6572_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(v_f_6562_, v_v_6563_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_);
    return v___x_6572_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed(
    mut v_pu_6573_: *mut leanh::LeanObject,
    mut v_f_6574_: *mut leanh::LeanObject,
    mut v_v_6575_: *mut leanh::LeanObject,
    mut v___y_6576_: *mut leanh::LeanObject,
    mut v___y_6577_: *mut leanh::LeanObject,
    mut v___y_6578_: *mut leanh::LeanObject,
    mut v___y_6579_: *mut leanh::LeanObject,
    mut v___y_6580_: *mut leanh::LeanObject,
    mut v___y_6581_: *mut leanh::LeanObject,
    mut v___y_6582_: *mut leanh::LeanObject,
    mut v___y_6583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_6584_: u8 = 0;
    let mut v_res_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6584_ = (leanh::lean_unbox(v_pu_6573_) as u8);
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
    leanh::lean_dec(v___y_6582_);
    leanh::lean_dec_ref(v___y_6581_);
    leanh::lean_dec(v___y_6580_);
    leanh::lean_dec_ref(v___y_6579_);
    leanh::lean_dec_ref(v___y_6578_);
    leanh::lean_dec(v___y_6577_);
    leanh::lean_dec_ref(v___y_6576_);
    return v_res_6585_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_check(
    mut v_pu_6586_: u8,
    mut v_decl_6587_: *mut leanh::LeanObject,
    mut v_a_6588_: *mut leanh::LeanObject,
    mut v_a_6589_: *mut leanh::LeanObject,
    mut v_a_6590_: *mut leanh::LeanObject,
    mut v_a_6591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_pu_6586_ == 0 {
        let mut v_toSignature_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_params_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toSignature_6593_ = leanh::lean_ctor_get(v_decl_6587_, 0);
        leanh::lean_inc_ref(v_toSignature_6593_);
        v_value_6594_ = leanh::lean_ctor_get(v_decl_6587_, 1);
        leanh::lean_inc_ref(v_value_6594_);
        leanh::lean_dec_ref(v_decl_6587_);
        v_name_6595_ = leanh::lean_ctor_get(v_toSignature_6593_, 0);
        leanh::lean_inc(v_name_6595_);
        v_type_6596_ = leanh::lean_ctor_get(v_toSignature_6593_, 2);
        leanh::lean_inc_ref(v_type_6596_);
        v_params_6597_ = leanh::lean_ctor_get(v_toSignature_6593_, 3);
        leanh::lean_inc_ref(v_params_6597_);
        leanh::lean_dec_ref(v_toSignature_6593_);
        v___x_6598_ = leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed as *mut core::ffi::c_void,
            12,
            3,
        );
        leanh::lean_closure_set(v___x_6598_, 0, v_name_6595_);
        leanh::lean_closure_set(v___x_6598_, 1, v_params_6597_);
        leanh::lean_closure_set(v___x_6598_, 2, v_type_6596_);
        v___x_6599_ = leanh::lean_box((v_pu_6586_) as usize);
        v___x_6600_ = leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed as *mut core::ffi::c_void, 11, 3);
        leanh::lean_closure_set(v___x_6600_, 0, v___x_6599_);
        leanh::lean_closure_set(v___x_6600_, 1, v___x_6598_);
        leanh::lean_closure_set(v___x_6600_, 2, v_value_6594_);
        v___x_6601_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
            v___x_6600_,
            v_a_6588_,
            v_a_6589_,
            v_a_6590_,
            v_a_6591_,
        );
        return v___x_6601_;
    } else {
        let mut v___x_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_decl_6587_);
        v___x_6602_ = leanh::lean_box(0);
        v___x_6603_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6603_, 0, v___x_6602_);
        return v___x_6603_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_check___boxed(
    mut v_pu_6604_: *mut leanh::LeanObject,
    mut v_decl_6605_: *mut leanh::LeanObject,
    mut v_a_6606_: *mut leanh::LeanObject,
    mut v_a_6607_: *mut leanh::LeanObject,
    mut v_a_6608_: *mut leanh::LeanObject,
    mut v_a_6609_: *mut leanh::LeanObject,
    mut v_a_6610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_6611_: u8 = 0;
    let mut v_res_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6611_ = (leanh::lean_unbox(v_pu_6604_) as u8);
    v_res_6612_ = l_Lean_Compiler_LCNF_Decl_check(
        v_pu_boxed_6611_,
        v_decl_6605_,
        v_a_6606_,
        v_a_6607_,
        v_a_6608_,
        v_a_6609_,
    );
    leanh::lean_dec(v_a_6609_);
    leanh::lean_dec_ref(v_a_6608_);
    leanh::lean_dec(v_a_6607_);
    leanh::lean_dec_ref(v_a_6606_);
    return v_res_6612_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Check(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Check(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Check(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Check(builtin);
}