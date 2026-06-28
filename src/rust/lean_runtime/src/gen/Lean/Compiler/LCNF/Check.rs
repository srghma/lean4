// Lean compiler output
// Module: Lean.Compiler.LCNF.Check
// Imports: Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.CompatibleTypes
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
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_8,
    lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 111, 117, 116, 32, 111, 102, 32, 115, 99, 111,
            112, 101, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 97, 116, 32, 76, 67, 78, 70, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 97, 114, 103, 117, 109, 101, 110, 116, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [10, 98, 117, 116, 32, 105, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0_value:
    LeanStringObject<42> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0_value: LeanStringObject<
    29,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2_value: LeanStringObject<
    35,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            76, 67, 78, 70, 32, 108, 101, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 97, 116, 32, 96, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            96, 44, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 109, 97, 116, 99, 104, 32, 118,
            97, 108, 117, 101, 32, 105, 110, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101,
            120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0_value: LeanStringObject<
    46,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__7_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__8_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value: LeanCtorObject<
    5,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__14_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__9_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__10_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__11_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__12_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__15_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__13_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0_value: LeanStringObject<46> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 46,
        m_capacity: 46,
        m_length: 45,
        m_data: [
            76, 67, 78, 70, 32, 108, 111, 99, 97, 108, 32, 102, 117, 110, 99, 116, 105, 111, 110,
            32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 109, 105, 115, 109, 97,
            116, 99, 104, 32, 97, 116, 32, 96, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2_value: LeanStringObject<43> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 43,
        m_capacity: 43,
        m_length: 42,
        m_data: [
            96, 44, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 105, 110, 32, 108,
            111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 100, 111, 101, 115, 32,
            109, 97, 116, 99, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            96, 44, 32, 116, 121, 112, 101, 32, 105, 110, 32, 108, 111, 99, 97, 108, 32, 99, 111,
            110, 116, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            96, 44, 32, 98, 105, 110, 100, 101, 114, 32, 110, 97, 109, 101, 32, 105, 110, 32, 108,
            111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 96, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__1_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 32, 96, 103, 111, 116, 111, 96,
            44, 32, 106, 111, 105, 110, 32, 112, 111, 105, 110, 116, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__1_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__3_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__3_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__5_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__5_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_check___closed__7_value: LeanStringObject<15> =
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
            32, 119, 101, 114, 101, 32, 112, 114, 111, 118, 105, 100, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__7_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Check_Pure_check___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 32, 96, 99, 97, 115, 101, 115, 96, 44, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [96, 32, 104, 97, 115, 32, 35, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [32, 102, 105, 101, 108, 100, 115, 44, 32, 98, 117, 116, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 104, 97, 115, 32, 35, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 111, 102, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 110, 97, 109, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 76, 67, 78, 70, 32, 96, 99, 97, 115, 101, 115, 96, 44, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [96, 32, 111, 99, 99, 117, 114, 115, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 111, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(
    mut v_a_3307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v_checkTypes_3314_: u8 = 0;
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_a_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3309_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_3307_);
                if lean_obj_tag(v___x_3309_) == 0 {
                    v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
                    v_isSharedCheck_3319_ = (!lean_is_exclusive(v___x_3309_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3312_ = v___x_3309_;
                        v_isShared_3313_ = v_isSharedCheck_3319_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3310_);
                        lean_dec(v___x_3309_);
                        v___x_3312_ = lean_box(0);
                        v_isShared_3313_ = v_isSharedCheck_3319_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3320_ = lean_ctor_get(v___x_3309_, 0);
                    v_isSharedCheck_3327_ = (!lean_is_exclusive(v___x_3309_)) as u8;
                    if v_isSharedCheck_3327_ == 0 {
                        v___x_3322_ = v___x_3309_;
                        v_isShared_3323_ = v_isSharedCheck_3327_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3320_);
                        lean_dec(v___x_3309_);
                        v___x_3322_ = lean_box(0);
                        v_isShared_3323_ = v_isSharedCheck_3327_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_checkTypes_3314_ = lean_ctor_get_uint8(
                    v_a_3310_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                lean_dec(v_a_3310_);
                v___x_3315_ = lean_box((v_checkTypes_3314_) as usize);
                if v_isShared_3313_ == 0 {
                    lean_ctor_set(v___x_3312_, 0, v___x_3315_);
                    v___x_3317_ = v___x_3312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
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
                    v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
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
    mut v_a_3328_: *mut LeanObject,
    mut v_a_3329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3330_: *mut LeanObject = core::ptr::null_mut();
    v_res_3330_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_3328_);
    lean_dec_ref(v_a_3328_);
    return v_res_3330_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes(
    mut v_a_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_3334_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkTypes___boxed(
    mut v_a_3340_: *mut LeanObject,
    mut v_a_3341_: *mut LeanObject,
    mut v_a_3342_: *mut LeanObject,
    mut v_a_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
    mut v_a_3345_: *mut LeanObject,
    mut v_a_3346_: *mut LeanObject,
    mut v_a_3347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3348_: *mut LeanObject = core::ptr::null_mut();
    v_res_3348_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes(
        v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_,
    );
    lean_dec(v_a_3346_);
    lean_dec_ref(v_a_3345_);
    lean_dec(v_a_3344_);
    lean_dec_ref(v_a_3343_);
    lean_dec_ref(v_a_3342_);
    lean_dec(v_a_3341_);
    lean_dec_ref(v_a_3340_);
    return v_res_3348_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    v___x_3349_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3349_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    v___x_3350_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__0);
    v___x_3351_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3351_, 0, v___x_3350_);
    return v___x_3351_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    v___x_3352_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1);
    v___x_3353_ = lean_unsigned_to_nat(0);
    v___x_3354_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3354_, 0, v___x_3353_);
    lean_ctor_set(v___x_3354_, 1, v___x_3353_);
    lean_ctor_set(v___x_3354_, 2, v___x_3353_);
    lean_ctor_set(v___x_3354_, 3, v___x_3353_);
    lean_ctor_set(v___x_3354_, 4, v___x_3352_);
    lean_ctor_set(v___x_3354_, 5, v___x_3352_);
    lean_ctor_set(v___x_3354_, 6, v___x_3352_);
    lean_ctor_set(v___x_3354_, 7, v___x_3352_);
    lean_ctor_set(v___x_3354_, 8, v___x_3352_);
    lean_ctor_set(v___x_3354_, 9, v___x_3352_);
    return v___x_3354_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
    mut v_msg_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
    mut v___y_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v_env_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_unused_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3388_: u8 = 0;
    let mut v_a_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3392_: u8 = 0;
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3361_ = lean_ctor_get(v___y_3358_, 2);
                v_ref_3362_ = lean_ctor_get(v___y_3358_, 5);
                v___x_3363_ = lean_st_ref_get(v___y_3359_);
                v___x_3364_ = lean_st_ref_get(v___y_3357_);
                v___x_3365_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3356_);
                if lean_obj_tag(v___x_3365_) == 0 {
                    v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
                    v_isSharedCheck_3388_ = (!lean_is_exclusive(v___x_3365_)) as u8;
                    if v_isSharedCheck_3388_ == 0 {
                        v___x_3368_ = v___x_3365_;
                        v_isShared_3369_ = v_isSharedCheck_3388_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3366_);
                        lean_dec(v___x_3365_);
                        v___x_3368_ = lean_box(0);
                        v_isShared_3369_ = v_isSharedCheck_3388_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3364_);
                    lean_dec(v___x_3363_);
                    lean_dec_ref(v_msg_3355_);
                    v_a_3389_ = lean_ctor_get(v___x_3365_, 0);
                    v_isSharedCheck_3396_ = (!lean_is_exclusive(v___x_3365_)) as u8;
                    if v_isSharedCheck_3396_ == 0 {
                        v___x_3391_ = v___x_3365_;
                        v_isShared_3392_ = v_isSharedCheck_3396_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3389_);
                        lean_dec(v___x_3365_);
                        v___x_3391_ = lean_box(0);
                        v_isShared_3392_ = v_isSharedCheck_3396_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3370_ = lean_ctor_get(v___x_3363_, 0);
                lean_inc_ref(v_env_3370_);
                lean_dec(v___x_3363_);
                v_lctx_3371_ = lean_ctor_get(v___x_3364_, 0);
                v_isSharedCheck_3386_ = (!lean_is_exclusive(v___x_3364_)) as u8;
                if v_isSharedCheck_3386_ == 0 {
                    v_unused_3387_ = lean_ctor_get(v___x_3364_, 1);
                    lean_dec(v_unused_3387_);
                    v___x_3373_ = v___x_3364_;
                    v_isShared_3374_ = v_isSharedCheck_3386_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_3371_);
                    lean_dec(v___x_3364_);
                    v___x_3373_ = lean_box(0);
                    v_isShared_3374_ = v_isSharedCheck_3386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3375_ = (lean_unbox(v_a_3366_) as u8);
                lean_dec(v_a_3366_);
                v___x_3376_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3371_, v___x_3375_);
                lean_dec_ref(v_lctx_3371_);
                v___x_3377_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                lean_inc_ref(v_options_3361_);
                v___x_3378_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3378_, 0, v_env_3370_);
                lean_ctor_set(v___x_3378_, 1, v___x_3377_);
                lean_ctor_set(v___x_3378_, 2, v___x_3376_);
                lean_ctor_set(v___x_3378_, 3, v_options_3361_);
                if v_isShared_3374_ == 0 {
                    lean_ctor_set_tag(v___x_3373_, 3);
                    lean_ctor_set(v___x_3373_, 1, v_msg_3355_);
                    lean_ctor_set(v___x_3373_, 0, v___x_3378_);
                    v___x_3380_ = v___x_3373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3378_);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_msg_3355_);
                    v___x_3380_ = v_reuseFailAlloc_3385_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_ref_3362_);
                v___x_3381_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3381_, 0, v_ref_3362_);
                lean_ctor_set(v___x_3381_, 1, v___x_3380_);
                if v_isShared_3369_ == 0 {
                    lean_ctor_set_tag(v___x_3368_, 1);
                    lean_ctor_set(v___x_3368_, 0, v___x_3381_);
                    v___x_3383_ = v___x_3368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
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
                    v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
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
    mut v_msg_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3403_: *mut LeanObject = core::ptr::null_mut();
    v_res_3403_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(
            v_msg_3397_,
            v___y_3398_,
            v___y_3399_,
            v___y_3400_,
            v___y_3401_,
        );
    lean_dec(v___y_3401_);
    lean_dec_ref(v___y_3400_);
    lean_dec(v___y_3399_);
    lean_dec_ref(v___y_3398_);
    return v_res_3403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1(
    mut v_00_u03b1_3404_: *mut LeanObject,
    mut v_msg_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3415_: *mut LeanObject,
    mut v_msg_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
    mut v___y_3423_: *mut LeanObject,
    mut v___y_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3425_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3423_);
    lean_dec_ref(v___y_3422_);
    lean_dec(v___y_3421_);
    lean_dec_ref(v___y_3420_);
    lean_dec_ref(v___y_3419_);
    lean_dec(v___y_3418_);
    lean_dec_ref(v___y_3417_);
    return v_res_3425_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(
    mut v_k_3426_: *mut LeanObject,
    mut v_t_3427_: *mut LeanObject,
) -> u8 {
    let mut v_k_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3427_) == 0 {
                    v_k_3428_ = lean_ctor_get(v_t_3427_, 1);
                    v_l_3429_ = lean_ctor_get(v_t_3427_, 3);
                    v_r_3430_ = lean_ctor_get(v_t_3427_, 4);
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
    mut v_k_3436_: *mut LeanObject,
    mut v_t_3437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3438_: u8 = 0;
    let mut v_r_3439_: *mut LeanObject = core::ptr::null_mut();
    v_res_3438_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_k_3436_, v_t_3437_);
    lean_dec(v_t_3437_);
    lean_dec(v_k_3436_);
    v_r_3439_ = lean_box((v_res_3438_) as usize);
    return v_r_3439_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1() -> *mut LeanObject {
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    v___x_3441_ = l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__0;
    v___x_3442_ = l_Lean_stringToMessageData(v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFVar(
    mut v_fvarId_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
    mut v_a_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
    mut v_a_3450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3463_: u8 = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_3452_ = lean_ctor_get(v_a_3444_, 1);
                v___x_3453_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_fvarId_3443_, v_vars_3452_);
                if v___x_3453_ == 0 {
                    v___x_3454_ = l_Lean_Compiler_LCNF_getBinderName(
                        v_fvarId_3443_,
                        v_a_3447_,
                        v_a_3448_,
                        v_a_3449_,
                        v_a_3450_,
                    );
                    if lean_obj_tag(v___x_3454_) == 0 {
                        v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
                        lean_inc(v_a_3455_);
                        lean_dec_ref_known(v___x_3454_, 1);
                        v___x_3456_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Check_Pure_checkFVar___closed__1,
                        );
                        v___x_3457_ = l_Lean_MessageData_ofName(v_a_3455_);
                        v___x_3458_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3458_, 0, v___x_3456_);
                        lean_ctor_set(v___x_3458_, 1, v___x_3457_);
                        v___x_3459_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_3458_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
                        return v___x_3459_;
                    } else {
                        v_a_3460_ = lean_ctor_get(v___x_3454_, 0);
                        v_isSharedCheck_3467_ = (!lean_is_exclusive(v___x_3454_)) as u8;
                        if v_isSharedCheck_3467_ == 0 {
                            v___x_3462_ = v___x_3454_;
                            v_isShared_3463_ = v_isSharedCheck_3467_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3460_);
                            lean_dec(v___x_3454_);
                            v___x_3462_ = lean_box(0);
                            v_isShared_3463_ = v_isSharedCheck_3467_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fvarId_3443_);
                    v___x_3468_ = lean_box(0);
                    v___x_3469_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3469_, 0, v___x_3468_);
                    return v___x_3469_;
                }
            }
            1 => {
                if v_isShared_3463_ == 0 {
                    v___x_3465_ = v___x_3462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
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
    mut v_fvarId_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
    mut v_a_3472_: *mut LeanObject,
    mut v_a_3473_: *mut LeanObject,
    mut v_a_3474_: *mut LeanObject,
    mut v_a_3475_: *mut LeanObject,
    mut v_a_3476_: *mut LeanObject,
    mut v_a_3477_: *mut LeanObject,
    mut v_a_3478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3479_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3477_);
    lean_dec_ref(v_a_3476_);
    lean_dec(v_a_3475_);
    lean_dec_ref(v_a_3474_);
    lean_dec_ref(v_a_3473_);
    lean_dec(v_a_3472_);
    lean_dec_ref(v_a_3471_);
    return v_res_3479_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(
    mut v_00_u03b2_3480_: *mut LeanObject,
    mut v_k_3481_: *mut LeanObject,
    mut v_t_3482_: *mut LeanObject,
) -> u8 {
    let mut v___x_3483_: u8 = 0;
    v___x_3483_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_k_3481_, v_t_3482_);
    return v___x_3483_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___boxed(
    mut v_00_u03b2_3484_: *mut LeanObject,
    mut v_k_3485_: *mut LeanObject,
    mut v_t_3486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3487_: u8 = 0;
    let mut v_r_3488_: *mut LeanObject = core::ptr::null_mut();
    v_res_3487_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0(v_00_u03b2_3484_, v_k_3485_, v_t_3486_);
    lean_dec(v_t_3486_);
    lean_dec(v_k_3485_);
    v_r_3488_ = lean_box((v_res_3487_) as usize);
    return v_r_3488_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0()
-> *mut LeanObject {
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    v___x_3489_ = lean_unsigned_to_nat(32);
    v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
    v___x_3491_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3491_, 0, v___x_3490_);
    return v___x_3491_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1()
-> *mut LeanObject {
    let mut v___x_3492_: usize = 0;
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    v___x_3492_ = 5usize;
    v___x_3493_ = lean_unsigned_to_nat(0);
    v___x_3494_ = lean_unsigned_to_nat(32);
    v___x_3495_ = lean_mk_empty_array_with_capacity(v___x_3494_);
    v___x_3496_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0);
    v___x_3497_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3497_, 0, v___x_3496_);
    lean_ctor_set(v___x_3497_, 1, v___x_3495_);
    lean_ctor_set(v___x_3497_, 2, v___x_3493_);
    lean_ctor_set(v___x_3497_, 3, v___x_3493_);
    lean_ctor_set_usize(v___x_3497_, 4, v___x_3492_);
    return v___x_3497_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2()
-> *mut LeanObject {
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    v___x_3498_ = lean_box(1);
    v___x_3499_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_3500_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__1);
    v___x_3501_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3501_, 0, v___x_3500_);
    lean_ctor_set(v___x_3501_, 1, v___x_3499_);
    lean_ctor_set(v___x_3501_, 2, v___x_3498_);
    return v___x_3501_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
    mut v___y_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    v___x_3506_ = lean_st_ref_get(v___y_3504_);
    v_env_3507_ = lean_ctor_get(v___x_3506_, 0);
    lean_inc_ref(v_env_3507_);
    lean_dec(v___x_3506_);
    v_options_3508_ = lean_ctor_get(v___y_3503_, 2);
    v___x_3509_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
    v___x_3510_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
    lean_inc_ref(v_options_3508_);
    v___x_3511_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3511_, 0, v_env_3507_);
    lean_ctor_set(v___x_3511_, 1, v___x_3509_);
    lean_ctor_set(v___x_3511_, 2, v___x_3510_);
    lean_ctor_set(v___x_3511_, 3, v_options_3508_);
    v___x_3512_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3512_, 0, v___x_3511_);
    lean_ctor_set(v___x_3512_, 1, v_msgData_3502_);
    v___x_3513_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3513_, 0, v___x_3512_);
    return v___x_3513_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_3514_: *mut LeanObject,
    mut v___y_3515_: *mut LeanObject,
    mut v___y_3516_: *mut LeanObject,
    mut v___y_3517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3518_: *mut LeanObject = core::ptr::null_mut();
    v_res_3518_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_3514_, v___y_3515_, v___y_3516_);
    lean_dec(v___y_3516_);
    lean_dec_ref(v___y_3515_);
    return v_res_3518_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3523_ = lean_ctor_get(v___y_3520_, 5);
                v___x_3524_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_3519_, v___y_3520_, v___y_3521_);
                v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
                v_isSharedCheck_3533_ = (!lean_is_exclusive(v___x_3524_)) as u8;
                if v_isSharedCheck_3533_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3525_);
                    lean_dec(v___x_3524_);
                    v___x_3527_ = lean_box(0);
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3523_);
                v___x_3529_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3529_, 0, v_ref_3523_);
                lean_ctor_set(v___x_3529_, 1, v_a_3525_);
                if v_isShared_3528_ == 0 {
                    lean_ctor_set_tag(v___x_3527_, 1);
                    lean_ctor_set(v___x_3527_, 0, v___x_3529_);
                    v___x_3531_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
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
    mut v_msg_3534_: *mut LeanObject,
    mut v___y_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
    mut v___y_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3538_: *mut LeanObject = core::ptr::null_mut();
    v_res_3538_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3534_, v___y_3535_, v___y_3536_);
    lean_dec(v___y_3536_);
    lean_dec_ref(v___y_3535_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_3539_: *mut LeanObject,
    mut v_msg_3540_: *mut LeanObject,
    mut v___y_3541_: *mut LeanObject,
    mut v___y_3542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3556_: u8 = 0;
    let mut v_cancelTk_x3f_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3558_: u8 = 0;
    let mut v_inheritedTraceOptions_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3544_ = lean_ctor_get(v___y_3541_, 0);
    v_fileMap_3545_ = lean_ctor_get(v___y_3541_, 1);
    v_options_3546_ = lean_ctor_get(v___y_3541_, 2);
    v_currRecDepth_3547_ = lean_ctor_get(v___y_3541_, 3);
    v_maxRecDepth_3548_ = lean_ctor_get(v___y_3541_, 4);
    v_ref_3549_ = lean_ctor_get(v___y_3541_, 5);
    v_currNamespace_3550_ = lean_ctor_get(v___y_3541_, 6);
    v_openDecls_3551_ = lean_ctor_get(v___y_3541_, 7);
    v_initHeartbeats_3552_ = lean_ctor_get(v___y_3541_, 8);
    v_maxHeartbeats_3553_ = lean_ctor_get(v___y_3541_, 9);
    v_quotContext_3554_ = lean_ctor_get(v___y_3541_, 10);
    v_currMacroScope_3555_ = lean_ctor_get(v___y_3541_, 11);
    v_diag_3556_ = lean_ctor_get_uint8(
        v___y_3541_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3557_ = lean_ctor_get(v___y_3541_, 12);
    v_suppressElabErrors_3558_ = lean_ctor_get_uint8(
        v___y_3541_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3559_ = lean_ctor_get(v___y_3541_, 13);
    v_ref_3560_ = l_Lean_replaceRef(v_ref_3539_, v_ref_3549_);
    lean_inc_ref(v_inheritedTraceOptions_3559_);
    lean_inc(v_cancelTk_x3f_3557_);
    lean_inc(v_currMacroScope_3555_);
    lean_inc(v_quotContext_3554_);
    lean_inc(v_maxHeartbeats_3553_);
    lean_inc(v_initHeartbeats_3552_);
    lean_inc(v_openDecls_3551_);
    lean_inc(v_currNamespace_3550_);
    lean_inc(v_maxRecDepth_3548_);
    lean_inc(v_currRecDepth_3547_);
    lean_inc_ref(v_options_3546_);
    lean_inc_ref(v_fileMap_3545_);
    lean_inc_ref(v_fileName_3544_);
    v___x_3561_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3561_, 0, v_fileName_3544_);
    lean_ctor_set(v___x_3561_, 1, v_fileMap_3545_);
    lean_ctor_set(v___x_3561_, 2, v_options_3546_);
    lean_ctor_set(v___x_3561_, 3, v_currRecDepth_3547_);
    lean_ctor_set(v___x_3561_, 4, v_maxRecDepth_3548_);
    lean_ctor_set(v___x_3561_, 5, v_ref_3560_);
    lean_ctor_set(v___x_3561_, 6, v_currNamespace_3550_);
    lean_ctor_set(v___x_3561_, 7, v_openDecls_3551_);
    lean_ctor_set(v___x_3561_, 8, v_initHeartbeats_3552_);
    lean_ctor_set(v___x_3561_, 9, v_maxHeartbeats_3553_);
    lean_ctor_set(v___x_3561_, 10, v_quotContext_3554_);
    lean_ctor_set(v___x_3561_, 11, v_currMacroScope_3555_);
    lean_ctor_set(v___x_3561_, 12, v_cancelTk_x3f_3557_);
    lean_ctor_set(v___x_3561_, 13, v_inheritedTraceOptions_3559_);
    lean_ctor_set_uint8(
        v___x_3561_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3556_,
    );
    lean_ctor_set_uint8(
        v___x_3561_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3558_,
    );
    v___x_3562_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3540_, v___x_3561_, v___y_3542_);
    lean_dec_ref_known(v___x_3561_, 14);
    return v___x_3562_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_3563_: *mut LeanObject,
    mut v_msg_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
    mut v___y_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3568_: *mut LeanObject = core::ptr::null_mut();
    v_res_3568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3563_, v_msg_3564_, v___y_3565_, v___y_3566_);
    lean_dec(v___y_3566_);
    lean_dec_ref(v___y_3565_);
    lean_dec(v_ref_3563_);
    return v_res_3568_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    v___x_3570_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_3571_ = l_Lean_stringToMessageData(v___x_3570_);
    return v___x_3571_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    v___x_3573_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
    v___x_3574_ = l_Lean_stringToMessageData(v___x_3573_);
    return v___x_3574_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    v___x_3576_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
    v___x_3577_ = l_Lean_stringToMessageData(v___x_3576_);
    return v___x_3577_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    v___x_3579_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_3580_ = l_Lean_stringToMessageData(v___x_3579_);
    return v___x_3580_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    v___x_3582_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_3583_ = l_Lean_stringToMessageData(v___x_3582_);
    return v___x_3583_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    v___x_3585_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_3586_ = l_Lean_stringToMessageData(v___x_3585_);
    return v___x_3586_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    v___x_3588_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_3589_ = l_Lean_stringToMessageData(v___x_3588_);
    return v___x_3589_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_3590_: *mut LeanObject,
    mut v_declHint_3591_: *mut LeanObject,
    mut v___y_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v_isExporting_3597_: u8 = 0;
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3619_: u8 = 0;
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: u8 = 0;
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3594_ = lean_st_ref_get(v___y_3592_);
                v_env_3595_ = lean_ctor_get(v___x_3594_, 0);
                lean_inc_ref(v_env_3595_);
                lean_dec(v___x_3594_);
                v___x_3596_ = l_Lean_Name_isAnonymous(v_declHint_3591_);
                if v___x_3596_ == 0 {
                    v_isExporting_3597_ = lean_ctor_get_uint8(
                        v_env_3595_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3597_ == 0 {
                        lean_dec_ref(v_env_3595_);
                        lean_dec(v_declHint_3591_);
                        v___x_3598_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3598_, 0, v_msg_3590_);
                        return v___x_3598_;
                    } else {
                        lean_inc_ref(v_env_3595_);
                        v___x_3599_ = l_Lean_Environment_setExporting(v_env_3595_, v___x_3596_);
                        lean_inc(v_declHint_3591_);
                        lean_inc_ref(v___x_3599_);
                        v___x_3600_ = l_Lean_Environment_contains(
                            v___x_3599_,
                            v_declHint_3591_,
                            v_isExporting_3597_,
                        );
                        if v___x_3600_ == 0 {
                            lean_dec_ref(v___x_3599_);
                            lean_dec_ref(v_env_3595_);
                            lean_dec(v_declHint_3591_);
                            v___x_3601_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3601_, 0, v_msg_3590_);
                            return v___x_3601_;
                        } else {
                            v___x_3602_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                            v___x_3603_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_3604_ = l_Lean_Options_empty;
                            v___x_3605_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3605_, 0, v___x_3599_);
                            lean_ctor_set(v___x_3605_, 1, v___x_3602_);
                            lean_ctor_set(v___x_3605_, 2, v___x_3603_);
                            lean_ctor_set(v___x_3605_, 3, v___x_3604_);
                            lean_inc(v_declHint_3591_);
                            v___x_3606_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3591_, v___x_3596_);
                            v_c_3607_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3607_, 0, v___x_3605_);
                            lean_ctor_set(v_c_3607_, 1, v___x_3606_);
                            v___x_3608_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3595_,
                                v_declHint_3591_,
                            );
                            if lean_obj_tag(v___x_3608_) == 0 {
                                lean_dec_ref(v_env_3595_);
                                lean_dec(v_declHint_3591_);
                                v___x_3609_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_3610_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3610_, 0, v___x_3609_);
                                lean_ctor_set(v___x_3610_, 1, v_c_3607_);
                                v___x_3611_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_3612_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3612_, 0, v___x_3610_);
                                lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                                v___x_3613_ = l_Lean_MessageData_note(v___x_3612_);
                                v___x_3614_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3614_, 0, v_msg_3590_);
                                lean_ctor_set(v___x_3614_, 1, v___x_3613_);
                                v___x_3615_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3615_, 0, v___x_3614_);
                                return v___x_3615_;
                            } else {
                                v_val_3616_ = lean_ctor_get(v___x_3608_, 0);
                                v_isSharedCheck_3651_ = (!lean_is_exclusive(v___x_3608_)) as u8;
                                if v_isSharedCheck_3651_ == 0 {
                                    v___x_3618_ = v___x_3608_;
                                    v_isShared_3619_ = v_isSharedCheck_3651_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3616_);
                                    lean_dec(v___x_3608_);
                                    v___x_3618_ = lean_box(0);
                                    v_isShared_3619_ = v_isSharedCheck_3651_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3595_);
                    lean_dec(v_declHint_3591_);
                    v___x_3652_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3652_, 0, v_msg_3590_);
                    return v___x_3652_;
                }
            }
            1 => {
                v___x_3620_ = lean_box(0);
                v___x_3621_ = l_Lean_Environment_header(v_env_3595_);
                lean_dec_ref(v_env_3595_);
                v___x_3622_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3621_);
                v_mod_3623_ = lean_array_get(v___x_3620_, v___x_3622_, v_val_3616_);
                lean_dec(v_val_3616_);
                lean_dec_ref(v___x_3622_);
                v___x_3624_ = l_Lean_isPrivateName(v_declHint_3591_);
                lean_dec(v_declHint_3591_);
                if v___x_3624_ == 0 {
                    v___x_3625_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_3626_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3626_, 0, v___x_3625_);
                    lean_ctor_set(v___x_3626_, 1, v_c_3607_);
                    v___x_3627_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_3628_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3628_, 0, v___x_3626_);
                    lean_ctor_set(v___x_3628_, 1, v___x_3627_);
                    v___x_3629_ = l_Lean_MessageData_ofName(v_mod_3623_);
                    v___x_3630_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3630_, 0, v___x_3628_);
                    lean_ctor_set(v___x_3630_, 1, v___x_3629_);
                    v___x_3631_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_3632_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3632_, 0, v___x_3630_);
                    lean_ctor_set(v___x_3632_, 1, v___x_3631_);
                    v___x_3633_ = l_Lean_MessageData_note(v___x_3632_);
                    v___x_3634_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3634_, 0, v_msg_3590_);
                    lean_ctor_set(v___x_3634_, 1, v___x_3633_);
                    if v_isShared_3619_ == 0 {
                        lean_ctor_set_tag(v___x_3618_, 0);
                        lean_ctor_set(v___x_3618_, 0, v___x_3634_);
                        v___x_3636_ = v___x_3618_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
                        v___x_3636_ = v_reuseFailAlloc_3637_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3638_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_3639_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3639_, 0, v___x_3638_);
                    lean_ctor_set(v___x_3639_, 1, v_c_3607_);
                    v___x_3640_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_3641_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3641_, 0, v___x_3639_);
                    lean_ctor_set(v___x_3641_, 1, v___x_3640_);
                    v___x_3642_ = l_Lean_MessageData_ofName(v_mod_3623_);
                    v___x_3643_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3643_, 0, v___x_3641_);
                    lean_ctor_set(v___x_3643_, 1, v___x_3642_);
                    v___x_3644_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_3645_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3645_, 0, v___x_3643_);
                    lean_ctor_set(v___x_3645_, 1, v___x_3644_);
                    v___x_3646_ = l_Lean_MessageData_note(v___x_3645_);
                    v___x_3647_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3647_, 0, v_msg_3590_);
                    lean_ctor_set(v___x_3647_, 1, v___x_3646_);
                    if v_isShared_3619_ == 0 {
                        lean_ctor_set_tag(v___x_3618_, 0);
                        lean_ctor_set(v___x_3618_, 0, v___x_3647_);
                        v___x_3649_ = v___x_3618_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
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
    mut v_msg_3653_: *mut LeanObject,
    mut v_declHint_3654_: *mut LeanObject,
    mut v___y_3655_: *mut LeanObject,
    mut v___y_3656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3657_: *mut LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3653_, v_declHint_3654_, v___y_3655_);
    lean_dec(v___y_3655_);
    return v_res_3657_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_3658_: *mut LeanObject,
    mut v_declHint_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3667_: u8 = 0;
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3658_, v_declHint_3659_, v___y_3661_);
                v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
                v_isSharedCheck_3673_ = (!lean_is_exclusive(v___x_3663_)) as u8;
                if v_isSharedCheck_3673_ == 0 {
                    v___x_3666_ = v___x_3663_;
                    v_isShared_3667_ = v_isSharedCheck_3673_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3664_);
                    lean_dec(v___x_3663_);
                    v___x_3666_ = lean_box(0);
                    v_isShared_3667_ = v_isSharedCheck_3673_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3668_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3669_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3669_, 0, v___x_3668_);
                lean_ctor_set(v___x_3669_, 1, v_a_3664_);
                if v_isShared_3667_ == 0 {
                    lean_ctor_set(v___x_3666_, 0, v___x_3669_);
                    v___x_3671_ = v___x_3666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
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
    mut v_msg_3674_: *mut LeanObject,
    mut v_declHint_3675_: *mut LeanObject,
    mut v___y_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3679_: *mut LeanObject = core::ptr::null_mut();
    v_res_3679_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3674_, v_declHint_3675_, v___y_3676_, v___y_3677_);
    lean_dec(v___y_3677_);
    lean_dec_ref(v___y_3676_);
    return v_res_3679_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_3680_: *mut LeanObject,
    mut v_msg_3681_: *mut LeanObject,
    mut v_declHint_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    v___x_3686_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3681_, v_declHint_3682_, v___y_3683_, v___y_3684_);
    v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
    lean_inc(v_a_3687_);
    lean_dec_ref(v___x_3686_);
    v___x_3688_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3680_, v_a_3687_, v___y_3683_, v___y_3684_);
    return v___x_3688_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_3689_: *mut LeanObject,
    mut v_msg_3690_: *mut LeanObject,
    mut v_declHint_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
    mut v___y_3693_: *mut LeanObject,
    mut v___y_3694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3695_: *mut LeanObject = core::ptr::null_mut();
    v_res_3695_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3689_, v_msg_3690_, v_declHint_3691_, v___y_3692_, v___y_3693_);
    lean_dec(v___y_3693_);
    lean_dec_ref(v___y_3692_);
    lean_dec(v_ref_3689_);
    return v_res_3695_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(
    mut v_ref_3702_: *mut LeanObject,
    mut v_constName_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u8 = 0;
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    v___x_3707_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_3708_ = 0;
    lean_inc(v_constName_3703_);
    v___x_3709_ = l_Lean_MessageData_ofConstName(v_constName_3703_, v___x_3708_);
    v___x_3710_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3710_, 0, v___x_3707_);
    lean_ctor_set(v___x_3710_, 1, v___x_3709_);
    v___x_3711_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_3712_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3712_, 0, v___x_3710_);
    lean_ctor_set(v___x_3712_, 1, v___x_3711_);
    v___x_3713_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3702_, v___x_3712_, v_constName_3703_, v___y_3704_, v___y_3705_);
    return v___x_3713_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_3714_: *mut LeanObject,
    mut v_constName_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
    mut v___y_3717_: *mut LeanObject,
    mut v___y_3718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3719_: *mut LeanObject = core::ptr::null_mut();
    v_res_3719_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3714_, v_constName_3715_, v___y_3716_, v___y_3717_);
    lean_dec(v___y_3717_);
    lean_dec_ref(v___y_3716_);
    lean_dec(v_ref_3714_);
    return v_res_3719_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(
    mut v_constName_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3724_ = lean_ctor_get(v___y_3721_, 5);
    v___x_3725_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3724_, v_constName_3720_, v___y_3721_, v___y_3722_);
    return v___x_3725_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg___boxed(
    mut v_constName_3726_: *mut LeanObject,
    mut v___y_3727_: *mut LeanObject,
    mut v___y_3728_: *mut LeanObject,
    mut v___y_3729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3730_: *mut LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3726_, v___y_3727_, v___y_3728_);
    lean_dec(v___y_3728_);
    lean_dec_ref(v___y_3727_);
    return v_res_3730_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(
    mut v_constName_3731_: *mut LeanObject,
    mut v___y_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3735_ = lean_st_ref_get(v___y_3733_);
                v_env_3736_ = lean_ctor_get(v___x_3735_, 0);
                lean_inc_ref(v_env_3736_);
                lean_dec(v___x_3735_);
                v___x_3737_ = 0;
                lean_inc(v_constName_3731_);
                v___x_3738_ =
                    l_Lean_Environment_find_x3f(v_env_3736_, v_constName_3731_, v___x_3737_);
                if lean_obj_tag(v___x_3738_) == 0 {
                    v___x_3739_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3731_, v___y_3732_, v___y_3733_);
                    return v___x_3739_;
                } else {
                    lean_dec(v_constName_3731_);
                    v_val_3740_ = lean_ctor_get(v___x_3738_, 0);
                    v_isSharedCheck_3747_ = (!lean_is_exclusive(v___x_3738_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3742_ = v___x_3738_;
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3740_);
                        lean_dec(v___x_3738_);
                        v___x_3742_ = lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3743_ == 0 {
                    lean_ctor_set_tag(v___x_3742_, 0);
                    v___x_3745_ = v___x_3742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_val_3740_);
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
    mut v_constName_3748_: *mut LeanObject,
    mut v___y_3749_: *mut LeanObject,
    mut v___y_3750_: *mut LeanObject,
    mut v___y_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3752_: *mut LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(
        v_constName_3748_,
        v___y_3749_,
        v___y_3750_,
    );
    lean_dec(v___y_3750_);
    lean_dec_ref(v___y_3749_);
    return v_res_3752_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(
    mut v_f_3753_: *mut LeanObject,
    mut v_i_3754_: *mut LeanObject,
    mut v_a_3755_: *mut LeanObject,
    mut v_a_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3763_: u8 = 0;
    let mut v_val_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: u8 = 0;
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_a_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3780_: u8 = 0;
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_f_3753_) == 4 {
                    v_declName_3758_ = lean_ctor_get(v_f_3753_, 0);
                    lean_inc(v_declName_3758_);
                    lean_dec_ref_known(v_f_3753_, 2);
                    v___x_3759_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0(v_declName_3758_, v_a_3755_, v_a_3756_);
                    if lean_obj_tag(v___x_3759_) == 0 {
                        v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
                        v_isSharedCheck_3776_ = (!lean_is_exclusive(v___x_3759_)) as u8;
                        if v_isSharedCheck_3776_ == 0 {
                            v___x_3762_ = v___x_3759_;
                            v_isShared_3763_ = v_isSharedCheck_3776_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3760_);
                            lean_dec(v___x_3759_);
                            v___x_3762_ = lean_box(0);
                            v_isShared_3763_ = v_isSharedCheck_3776_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3777_ = lean_ctor_get(v___x_3759_, 0);
                        v_isSharedCheck_3784_ = (!lean_is_exclusive(v___x_3759_)) as u8;
                        if v_isSharedCheck_3784_ == 0 {
                            v___x_3779_ = v___x_3759_;
                            v_isShared_3780_ = v_isSharedCheck_3784_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3777_);
                            lean_dec(v___x_3759_);
                            v___x_3779_ = lean_box(0);
                            v_isShared_3780_ = v_isSharedCheck_3784_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_3753_);
                    v___x_3785_ = 0;
                    v___x_3786_ = lean_box((v___x_3785_) as usize);
                    v___x_3787_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3787_, 0, v___x_3786_);
                    return v___x_3787_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_3760_) == 6 {
                    v_val_3764_ = lean_ctor_get(v_a_3760_, 0);
                    lean_inc_ref(v_val_3764_);
                    lean_dec_ref_known(v_a_3760_, 1);
                    v_numParams_3765_ = lean_ctor_get(v_val_3764_, 3);
                    lean_inc(v_numParams_3765_);
                    lean_dec_ref(v_val_3764_);
                    v___x_3766_ = lean_nat_dec_lt(v_i_3754_, v_numParams_3765_);
                    lean_dec(v_numParams_3765_);
                    v___x_3767_ = lean_box((v___x_3766_) as usize);
                    if v_isShared_3763_ == 0 {
                        lean_ctor_set(v___x_3762_, 0, v___x_3767_);
                        v___x_3769_ = v___x_3762_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
                        v___x_3769_ = v_reuseFailAlloc_3770_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3760_);
                    v___x_3771_ = 0;
                    v___x_3772_ = lean_box((v___x_3771_) as usize);
                    if v_isShared_3763_ == 0 {
                        lean_ctor_set(v___x_3762_, 0, v___x_3772_);
                        v___x_3774_ = v___x_3762_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
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
                    v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
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
    mut v_f_3788_: *mut LeanObject,
    mut v_i_3789_: *mut LeanObject,
    mut v_a_3790_: *mut LeanObject,
    mut v_a_3791_: *mut LeanObject,
    mut v_a_3792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3793_: *mut LeanObject = core::ptr::null_mut();
    v_res_3793_ =
        l_Lean_Compiler_LCNF_Check_Pure_isCtorParam(v_f_3788_, v_i_3789_, v_a_3790_, v_a_3791_);
    lean_dec(v_a_3791_);
    lean_dec_ref(v_a_3790_);
    lean_dec(v_i_3789_);
    return v_res_3793_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0(
    mut v_00_u03b1_3794_: *mut LeanObject,
    mut v_constName_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    v___x_3799_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___redArg(v_constName_3795_, v___y_3796_, v___y_3797_);
    return v___x_3799_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0___boxed(
    mut v_00_u03b1_3800_: *mut LeanObject,
    mut v_constName_3801_: *mut LeanObject,
    mut v___y_3802_: *mut LeanObject,
    mut v___y_3803_: *mut LeanObject,
    mut v___y_3804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3805_: *mut LeanObject = core::ptr::null_mut();
    v_res_3805_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0(v_00_u03b1_3800_, v_constName_3801_, v___y_3802_, v___y_3803_);
    lean_dec(v___y_3803_);
    lean_dec_ref(v___y_3802_);
    return v_res_3805_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3806_: *mut LeanObject,
    mut v_ref_3807_: *mut LeanObject,
    mut v_constName_3808_: *mut LeanObject,
    mut v___y_3809_: *mut LeanObject,
    mut v___y_3810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg(v_ref_3807_, v_constName_3808_, v___y_3809_, v___y_3810_);
    return v___x_3812_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3813_: *mut LeanObject,
    mut v_ref_3814_: *mut LeanObject,
    mut v_constName_3815_: *mut LeanObject,
    mut v___y_3816_: *mut LeanObject,
    mut v___y_3817_: *mut LeanObject,
    mut v___y_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3819_: *mut LeanObject = core::ptr::null_mut();
    v_res_3819_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1(v_00_u03b1_3813_, v_ref_3814_, v_constName_3815_, v___y_3816_, v___y_3817_);
    lean_dec(v___y_3817_);
    lean_dec_ref(v___y_3816_);
    lean_dec(v_ref_3814_);
    return v_res_3819_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_3820_: *mut LeanObject,
    mut v_ref_3821_: *mut LeanObject,
    mut v_msg_3822_: *mut LeanObject,
    mut v_declHint_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3821_, v_msg_3822_, v_declHint_3823_, v___y_3824_, v___y_3825_);
    return v___x_3827_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_3828_: *mut LeanObject,
    mut v_ref_3829_: *mut LeanObject,
    mut v_msg_3830_: *mut LeanObject,
    mut v_declHint_3831_: *mut LeanObject,
    mut v___y_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
    mut v___y_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3835_: *mut LeanObject = core::ptr::null_mut();
    v_res_3835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3828_, v_ref_3829_, v_msg_3830_, v_declHint_3831_, v___y_3832_, v___y_3833_);
    lean_dec(v___y_3833_);
    lean_dec_ref(v___y_3832_);
    lean_dec(v_ref_3829_);
    return v_res_3835_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_3836_: *mut LeanObject,
    mut v_declHint_3837_: *mut LeanObject,
    mut v___y_3838_: *mut LeanObject,
    mut v___y_3839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3836_, v_declHint_3837_, v___y_3839_);
    return v___x_3841_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_3842_: *mut LeanObject,
    mut v_declHint_3843_: *mut LeanObject,
    mut v___y_3844_: *mut LeanObject,
    mut v___y_3845_: *mut LeanObject,
    mut v___y_3846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3847_: *mut LeanObject = core::ptr::null_mut();
    v_res_3847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3842_, v_declHint_3843_, v___y_3844_, v___y_3845_);
    lean_dec(v___y_3845_);
    lean_dec_ref(v___y_3844_);
    return v_res_3847_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_3848_: *mut LeanObject,
    mut v_ref_3849_: *mut LeanObject,
    mut v_msg_3850_: *mut LeanObject,
    mut v___y_3851_: *mut LeanObject,
    mut v___y_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v___x_3854_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3849_, v_msg_3850_, v___y_3851_, v___y_3852_);
    return v___x_3854_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_3855_: *mut LeanObject,
    mut v_ref_3856_: *mut LeanObject,
    mut v_msg_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3861_: *mut LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3855_, v_ref_3856_, v_msg_3857_, v___y_3858_, v___y_3859_);
    lean_dec(v___y_3859_);
    lean_dec_ref(v___y_3858_);
    lean_dec(v_ref_3856_);
    return v_res_3861_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_3862_: *mut LeanObject,
    mut v_msg_3863_: *mut LeanObject,
    mut v___y_3864_: *mut LeanObject,
    mut v___y_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    v___x_3867_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3863_, v___y_3864_, v___y_3865_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_3868_: *mut LeanObject,
    mut v_msg_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
    mut v___y_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3873_: *mut LeanObject = core::ptr::null_mut();
    v_res_3873_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3868_, v_msg_3869_, v___y_3870_, v___y_3871_);
    lean_dec(v___y_3871_);
    lean_dec_ref(v___y_3870_);
    return v_res_3873_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(
    mut v_sz_3874_: usize,
    mut v_i_3875_: usize,
    mut v_bs_3876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3877_: u8 = 0;
    let mut v_v_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: usize = 0;
    let mut v___x_3883_: usize = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3877_ = lean_usize_dec_lt(v_i_3875_, v_sz_3874_);
                if v___x_3877_ == 0 {
                    return v_bs_3876_;
                } else {
                    v_v_3878_ = lean_array_uget(v_bs_3876_, v_i_3875_);
                    v___x_3879_ = lean_unsigned_to_nat(0);
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
    mut v_sz_3886_: *mut LeanObject,
    mut v_i_3887_: *mut LeanObject,
    mut v_bs_3888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3889_: usize = 0;
    let mut v_i_boxed_3890_: usize = 0;
    let mut v_res_3891_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3889_ = lean_unbox_usize(v_sz_3886_);
    lean_dec(v_sz_3886_);
    v_i_boxed_3890_ = lean_unbox_usize(v_i_3887_);
    lean_dec(v_i_3887_);
    v_res_3891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(v_sz_boxed_3889_, v_i_boxed_3890_, v_bs_3888_);
    return v_res_3891_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    v___x_3893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__0;
    v___x_3894_ = l_Lean_stringToMessageData(v___x_3893_);
    return v___x_3894_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    v___x_3896_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__2;
    v___x_3897_ = l_Lean_stringToMessageData(v___x_3896_);
    return v___x_3897_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    v___x_3899_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__4;
    v___x_3900_ = l_Lean_stringToMessageData(v___x_3899_);
    return v___x_3900_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    v___x_3902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__6;
    v___x_3903_ = l_Lean_stringToMessageData(v___x_3902_);
    return v___x_3903_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(
    mut v___x_3904_: *mut LeanObject,
    mut v___x_3905_: *mut LeanObject,
    mut v_a_3906_: *mut LeanObject,
    mut v_args_3907_: *mut LeanObject,
    mut v_f_3908_: *mut LeanObject,
    mut v_____x_3909_: *mut LeanObject,
    mut v_fType_3910_: *mut LeanObject,
    mut v_j_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
    mut v___y_3914_: *mut LeanObject,
    mut v___y_3915_: *mut LeanObject,
    mut v___y_3916_: *mut LeanObject,
    mut v___y_3917_: *mut LeanObject,
    mut v___y_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v___x_3935_: u8 = 0;
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: u8 = 0;
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3943_: usize = 0;
    let mut v___x_3944_: usize = 0;
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut v_a_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_a_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_a_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3920_ = lean_ctor_get(v_____x_3909_, 0);
                v_snd_3921_ = lean_ctor_get(v_____x_3909_, 1);
                v_isSharedCheck_3995_ = (!lean_is_exclusive(v_____x_3909_)) as u8;
                if v_isSharedCheck_3995_ == 0 {
                    v___x_3923_ = v_____x_3909_;
                    v_isShared_3924_ = v_isSharedCheck_3995_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3921_);
                    lean_inc(v_fst_3920_);
                    lean_dec(v_____x_3909_);
                    v___x_3923_ = lean_box(0);
                    v_isShared_3924_ = v_isSharedCheck_3995_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3932_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v___y_3915_);
                if lean_obj_tag(v___x_3932_) == 0 {
                    v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
                    lean_inc(v_a_3933_);
                    lean_dec_ref_known(v___x_3932_, 1);
                    v___x_3934_ = (lean_unbox(v_a_3933_) as u8);
                    lean_dec(v_a_3933_);
                    if v___x_3934_ == 0 {
                        lean_dec(v_fst_3920_);
                        lean_dec_ref(v_f_3908_);
                        lean_dec_ref(v_args_3907_);
                        lean_dec(v___x_3905_);
                        state = 2;
                        continue;
                    } else {
                        v___x_3935_ = 0;
                        lean_inc(v___x_3905_);
                        v___x_3936_ = l_Lean_Compiler_LCNF_Arg_inferType(
                            v___x_3935_,
                            v___x_3905_,
                            v___y_3915_,
                            v___y_3916_,
                            v___y_3917_,
                            v___y_3918_,
                        );
                        if lean_obj_tag(v___x_3936_) == 0 {
                            v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
                            lean_inc_n(v_a_3937_, 2);
                            lean_dec_ref_known(v___x_3936_, 1);
                            lean_inc_ref(v_args_3907_);
                            v___x_3938_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(
                                v_fst_3920_,
                                v_j_3911_,
                                v_a_3906_,
                                v_args_3907_,
                            );
                            lean_dec(v_fst_3920_);
                            lean_inc_ref(v___x_3938_);
                            v___x_3939_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_a_3937_,
                                v___x_3938_,
                                v___y_3914_,
                                v___y_3915_,
                                v___y_3916_,
                                v___y_3917_,
                                v___y_3918_,
                            );
                            if lean_obj_tag(v___x_3939_) == 0 {
                                v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
                                lean_inc(v_a_3940_);
                                lean_dec_ref_known(v___x_3939_, 1);
                                v___x_3941_ = (lean_unbox(v_a_3940_) as u8);
                                lean_dec(v_a_3940_);
                                if v___x_3941_ == 0 {
                                    v___x_3942_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__1);
                                    v_sz_3943_ = lean_array_size(v_args_3907_);
                                    v___x_3944_ = 0usize;
                                    v___x_3945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__0(v_sz_3943_, v___x_3944_, v_args_3907_);
                                    v___x_3946_ = l_Lean_mkAppN(v_f_3908_, v___x_3945_);
                                    lean_dec_ref(v___x_3945_);
                                    v___x_3947_ = l_Lean_indentExpr(v___x_3946_);
                                    v___x_3948_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3948_, 0, v___x_3942_);
                                    lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                                    v___x_3949_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__3);
                                    v___x_3950_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                                    lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                                    v___x_3951_ =
                                        l_Lean_Compiler_LCNF_Arg_toExpr___redArg(v___x_3905_);
                                    v___x_3952_ = l_Lean_MessageData_ofExpr(v___x_3951_);
                                    v___x_3953_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3953_, 0, v___x_3950_);
                                    lean_ctor_set(v___x_3953_, 1, v___x_3952_);
                                    v___x_3954_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__5);
                                    v___x_3955_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3955_, 0, v___x_3953_);
                                    lean_ctor_set(v___x_3955_, 1, v___x_3954_);
                                    v___x_3956_ = l_Lean_indentExpr(v_a_3937_);
                                    v___x_3957_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3957_, 0, v___x_3955_);
                                    lean_ctor_set(v___x_3957_, 1, v___x_3956_);
                                    v___x_3958_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                                    v___x_3959_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3959_, 0, v___x_3957_);
                                    lean_ctor_set(v___x_3959_, 1, v___x_3958_);
                                    v___x_3960_ = l_Lean_indentExpr(v___x_3938_);
                                    v___x_3961_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3961_, 0, v___x_3959_);
                                    lean_ctor_set(v___x_3961_, 1, v___x_3960_);
                                    v___x_3962_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_3961_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
                                    if lean_obj_tag(v___x_3962_) == 0 {
                                        lean_dec_ref_known(v___x_3962_, 1);
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_del_object(v___x_3923_);
                                        lean_dec(v_snd_3921_);
                                        lean_dec(v_j_3911_);
                                        lean_dec(v___x_3904_);
                                        v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
                                        v_isSharedCheck_3970_ =
                                            (!lean_is_exclusive(v___x_3962_)) as u8;
                                        if v_isSharedCheck_3970_ == 0 {
                                            v___x_3965_ = v___x_3962_;
                                            v_isShared_3966_ = v_isSharedCheck_3970_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3963_);
                                            lean_dec(v___x_3962_);
                                            v___x_3965_ = lean_box(0);
                                            v_isShared_3966_ = v_isSharedCheck_3970_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_3938_);
                                    lean_dec(v_a_3937_);
                                    lean_dec_ref(v_f_3908_);
                                    lean_dec_ref(v_args_3907_);
                                    lean_dec(v___x_3905_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_3938_);
                                lean_dec(v_a_3937_);
                                lean_del_object(v___x_3923_);
                                lean_dec(v_snd_3921_);
                                lean_dec(v_j_3911_);
                                lean_dec_ref(v_f_3908_);
                                lean_dec_ref(v_args_3907_);
                                lean_dec(v___x_3905_);
                                lean_dec(v___x_3904_);
                                v_a_3971_ = lean_ctor_get(v___x_3939_, 0);
                                v_isSharedCheck_3978_ = (!lean_is_exclusive(v___x_3939_)) as u8;
                                if v_isSharedCheck_3978_ == 0 {
                                    v___x_3973_ = v___x_3939_;
                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_3971_);
                                    lean_dec(v___x_3939_);
                                    v___x_3973_ = lean_box(0);
                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_3923_);
                            lean_dec(v_snd_3921_);
                            lean_dec(v_fst_3920_);
                            lean_dec(v_j_3911_);
                            lean_dec_ref(v_f_3908_);
                            lean_dec_ref(v_args_3907_);
                            lean_dec(v___x_3905_);
                            lean_dec(v___x_3904_);
                            v_a_3979_ = lean_ctor_get(v___x_3936_, 0);
                            v_isSharedCheck_3986_ = (!lean_is_exclusive(v___x_3936_)) as u8;
                            if v_isSharedCheck_3986_ == 0 {
                                v___x_3981_ = v___x_3936_;
                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_3979_);
                                lean_dec(v___x_3936_);
                                v___x_3981_ = lean_box(0);
                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_3923_);
                    lean_dec(v_snd_3921_);
                    lean_dec(v_fst_3920_);
                    lean_dec(v_j_3911_);
                    lean_dec_ref(v_f_3908_);
                    lean_dec_ref(v_args_3907_);
                    lean_dec(v___x_3905_);
                    lean_dec(v___x_3904_);
                    v_a_3987_ = lean_ctor_get(v___x_3932_, 0);
                    v_isSharedCheck_3994_ = (!lean_is_exclusive(v___x_3932_)) as u8;
                    if v_isSharedCheck_3994_ == 0 {
                        v___x_3989_ = v___x_3932_;
                        v_isShared_3990_ = v_isSharedCheck_3994_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3987_);
                        lean_dec(v___x_3932_);
                        v___x_3989_ = lean_box(0);
                        v_isShared_3990_ = v_isSharedCheck_3994_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3924_ == 0 {
                    lean_ctor_set(v___x_3923_, 1, v_j_3911_);
                    lean_ctor_set(v___x_3923_, 0, v_snd_3921_);
                    v___x_3927_ = v___x_3923_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_snd_3921_);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_j_3911_);
                    v___x_3927_ = v_reuseFailAlloc_3931_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3928_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3928_, 0, v___x_3904_);
                lean_ctor_set(v___x_3928_, 1, v___x_3927_);
                v___x_3929_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                v___x_3930_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3930_, 0, v___x_3929_);
                return v___x_3930_;
            }
            4 => {
                if v_isShared_3966_ == 0 {
                    v___x_3968_ = v___x_3965_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
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
                    v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
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
                    v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
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
                    v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
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
    mut v___x_3996_: *mut LeanObject,
    mut v___x_3997_: *mut LeanObject,
    mut v_a_3998_: *mut LeanObject,
    mut v_args_3999_: *mut LeanObject,
    mut v_f_4000_: *mut LeanObject,
    mut v_____x_4001_: *mut LeanObject,
    mut v_fType_4002_: *mut LeanObject,
    mut v_j_4003_: *mut LeanObject,
    mut v___y_4004_: *mut LeanObject,
    mut v___y_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
    mut v___y_4009_: *mut LeanObject,
    mut v___y_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4012_: *mut LeanObject = core::ptr::null_mut();
    v_res_4012_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_3996_, v___x_3997_, v_a_3998_, v_args_3999_, v_f_4000_, v_____x_4001_, v_fType_4002_, v_j_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
    lean_dec(v___y_4010_);
    lean_dec_ref(v___y_4009_);
    lean_dec(v___y_4008_);
    lean_dec_ref(v___y_4007_);
    lean_dec_ref(v___y_4006_);
    lean_dec(v___y_4005_);
    lean_dec_ref(v___y_4004_);
    lean_dec_ref(v_fType_4002_);
    lean_dec(v_a_3998_);
    return v_res_4012_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(
    mut v_upperBound_4015_: *mut LeanObject,
    mut v_args_4016_: *mut LeanObject,
    mut v_f_4017_: *mut LeanObject,
    mut v_a_4018_: *mut LeanObject,
    mut v_b_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
    mut v___y_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v_a_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v_a_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4050_: u8 = 0;
    let mut v___x_4051_: u8 = 0;
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v_fst_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_unused_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4051_ = lean_nat_dec_lt(v_a_4018_, v_upperBound_4015_);
                if v___x_4051_ == 0 {
                    lean_dec(v_a_4018_);
                    lean_dec_ref(v_f_4017_);
                    lean_dec_ref(v_args_4016_);
                    v___x_4052_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4052_, 0, v_b_4019_);
                    return v___x_4052_;
                } else {
                    v_snd_4053_ = lean_ctor_get(v_b_4019_, 1);
                    v_isSharedCheck_4097_ = (!lean_is_exclusive(v_b_4019_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v_unused_4098_ = lean_ctor_get(v_b_4019_, 0);
                        lean_dec(v_unused_4098_);
                        v___x_4055_ = v_b_4019_;
                        v_isShared_4056_ = v_isSharedCheck_4097_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_4053_);
                        lean_dec(v_b_4019_);
                        v___x_4055_ = lean_box(0);
                        v_isShared_4056_ = v_isSharedCheck_4097_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_4029_) == 0 {
                    v_a_4030_ = lean_ctor_get(v___y_4029_, 0);
                    v_isSharedCheck_4042_ = (!lean_is_exclusive(v___y_4029_)) as u8;
                    if v_isSharedCheck_4042_ == 0 {
                        v___x_4032_ = v___y_4029_;
                        v_isShared_4033_ = v_isSharedCheck_4042_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4030_);
                        lean_dec(v___y_4029_);
                        v___x_4032_ = lean_box(0);
                        v_isShared_4033_ = v_isSharedCheck_4042_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4018_);
                    lean_dec_ref(v_f_4017_);
                    lean_dec_ref(v_args_4016_);
                    v_a_4043_ = lean_ctor_get(v___y_4029_, 0);
                    v_isSharedCheck_4050_ = (!lean_is_exclusive(v___y_4029_)) as u8;
                    if v_isSharedCheck_4050_ == 0 {
                        v___x_4045_ = v___y_4029_;
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4043_);
                        lean_dec(v___y_4029_);
                        v___x_4045_ = lean_box(0);
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4030_) == 0 {
                    lean_dec(v_a_4018_);
                    lean_dec_ref(v_f_4017_);
                    lean_dec_ref(v_args_4016_);
                    v_a_4034_ = lean_ctor_get(v_a_4030_, 0);
                    lean_inc(v_a_4034_);
                    lean_dec_ref_known(v_a_4030_, 1);
                    if v_isShared_4033_ == 0 {
                        lean_ctor_set(v___x_4032_, 0, v_a_4034_);
                        v___x_4036_ = v___x_4032_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4034_);
                        v___x_4036_ = v_reuseFailAlloc_4037_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4032_);
                    v_a_4038_ = lean_ctor_get(v_a_4030_, 0);
                    lean_inc(v_a_4038_);
                    lean_dec_ref_known(v_a_4030_, 1);
                    v___x_4039_ = lean_unsigned_to_nat(1);
                    v___x_4040_ = lean_nat_add(v_a_4018_, v___x_4039_);
                    lean_dec(v_a_4018_);
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
                    v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
                    v___x_4048_ = v_reuseFailAlloc_4049_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4048_;
            }
            6 => {
                v_fst_4057_ = lean_ctor_get(v_snd_4053_, 0);
                v_snd_4058_ = lean_ctor_get(v_snd_4053_, 1);
                v_isSharedCheck_4096_ = (!lean_is_exclusive(v_snd_4053_)) as u8;
                if v_isSharedCheck_4096_ == 0 {
                    v___x_4060_ = v_snd_4053_;
                    v_isShared_4061_ = v_isSharedCheck_4096_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_4058_);
                    lean_inc(v_fst_4057_);
                    lean_dec(v_snd_4053_);
                    v___x_4060_ = lean_box(0);
                    v_isShared_4061_ = v_isSharedCheck_4096_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4062_ = l_Lean_Expr_isErased(v_fst_4057_);
                if v___x_4062_ == 0 {
                    v___x_4063_ = lean_box(0);
                    v___x_4064_ = lean_array_fget_borrowed(v_args_4016_, v_a_4018_);
                    v___x_4065_ = l_Lean_Expr_headBeta(v_fst_4057_);
                    if lean_obj_tag(v___x_4065_) == 7 {
                        lean_del_object(v___x_4055_);
                        v_binderType_4066_ = lean_ctor_get(v___x_4065_, 1);
                        lean_inc_ref(v_binderType_4066_);
                        v_body_4067_ = lean_ctor_get(v___x_4065_, 2);
                        lean_inc_ref(v_body_4067_);
                        if v_isShared_4061_ == 0 {
                            lean_ctor_set(v___x_4060_, 1, v_body_4067_);
                            lean_ctor_set(v___x_4060_, 0, v_binderType_4066_);
                            v___x_4069_ = v___x_4060_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_binderType_4066_);
                            lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_body_4067_);
                            v___x_4069_ = v_reuseFailAlloc_4071_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_inc_ref(v_args_4016_);
                        v___x_4072_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(
                            v___x_4065_,
                            v_snd_4058_,
                            v_a_4018_,
                            v_args_4016_,
                        );
                        lean_dec_ref(v___x_4065_);
                        v___x_4073_ = l_Lean_Expr_headBeta(v___x_4072_);
                        if lean_obj_tag(v___x_4073_) == 7 {
                            lean_dec(v_snd_4058_);
                            lean_del_object(v___x_4055_);
                            v_binderType_4074_ = lean_ctor_get(v___x_4073_, 1);
                            lean_inc_ref(v_binderType_4074_);
                            v_body_4075_ = lean_ctor_get(v___x_4073_, 2);
                            lean_inc_ref(v_body_4075_);
                            if v_isShared_4061_ == 0 {
                                lean_ctor_set(v___x_4060_, 1, v_body_4075_);
                                lean_ctor_set(v___x_4060_, 0, v_binderType_4074_);
                                v___x_4077_ = v___x_4060_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_binderType_4074_);
                                lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_body_4075_);
                                v___x_4077_ = v_reuseFailAlloc_4079_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4018_);
                            lean_dec_ref(v_f_4017_);
                            lean_dec_ref(v_args_4016_);
                            v___x_4080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0;
                            if v_isShared_4061_ == 0 {
                                lean_ctor_set(v___x_4060_, 0, v___x_4073_);
                                v___x_4082_ = v___x_4060_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4073_);
                                lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_snd_4058_);
                                v___x_4082_ = v_reuseFailAlloc_4087_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_4018_);
                    lean_dec_ref(v_f_4017_);
                    lean_dec_ref(v_args_4016_);
                    v___x_4088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___closed__0;
                    if v_isShared_4061_ == 0 {
                        v___x_4090_ = v___x_4060_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_fst_4057_);
                        lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_snd_4058_);
                        v___x_4090_ = v_reuseFailAlloc_4095_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                lean_inc_ref(v_f_4017_);
                lean_inc_ref(v_args_4016_);
                lean_inc(v___x_4064_);
                v___x_4070_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_4063_, v___x_4064_, v_a_4018_, v_args_4016_, v_f_4017_, v___x_4069_, v___x_4065_, v_snd_4058_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
                lean_dec_ref_known(v___x_4065_, 3);
                v___y_4029_ = v___x_4070_;
                state = 1;
                continue;
            }
            9 => {
                lean_inc_ref(v_f_4017_);
                lean_inc_ref(v_args_4016_);
                lean_inc(v_a_4018_);
                lean_inc(v___x_4064_);
                v___x_4078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0(v___x_4063_, v___x_4064_, v_a_4018_, v_args_4016_, v_f_4017_, v___x_4077_, v___x_4073_, v_a_4018_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
                lean_dec_ref_known(v___x_4073_, 3);
                v___y_4029_ = v___x_4078_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_4056_ == 0 {
                    lean_ctor_set(v___x_4055_, 1, v___x_4082_);
                    lean_ctor_set(v___x_4055_, 0, v___x_4080_);
                    v___x_4084_ = v___x_4055_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4080_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4082_);
                    v___x_4084_ = v_reuseFailAlloc_4086_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4085_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4085_, 0, v___x_4084_);
                return v___x_4085_;
            }
            12 => {
                if v_isShared_4056_ == 0 {
                    lean_ctor_set(v___x_4055_, 1, v___x_4090_);
                    lean_ctor_set(v___x_4055_, 0, v___x_4088_);
                    v___x_4092_ = v___x_4055_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4088_);
                    lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4090_);
                    v___x_4092_ = v_reuseFailAlloc_4094_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4093_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4093_, 0, v___x_4092_);
                return v___x_4093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___boxed(
    mut v_upperBound_4099_: *mut LeanObject,
    mut v_args_4100_: *mut LeanObject,
    mut v_f_4101_: *mut LeanObject,
    mut v_a_4102_: *mut LeanObject,
    mut v_b_4103_: *mut LeanObject,
    mut v___y_4104_: *mut LeanObject,
    mut v___y_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4112_: *mut LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v_upperBound_4099_, v_args_4100_, v_f_4101_, v_a_4102_, v_b_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    lean_dec(v___y_4110_);
    lean_dec_ref(v___y_4109_);
    lean_dec(v___y_4108_);
    lean_dec_ref(v___y_4107_);
    lean_dec_ref(v___y_4106_);
    lean_dec(v___y_4105_);
    lean_dec_ref(v___y_4104_);
    lean_dec(v_upperBound_4099_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkAppArgs(
    mut v_f_4113_: *mut LeanObject,
    mut v_args_4114_: *mut LeanObject,
    mut v_a_4115_: *mut LeanObject,
    mut v_a_4116_: *mut LeanObject,
    mut v_a_4117_: *mut LeanObject,
    mut v_a_4118_: *mut LeanObject,
    mut v_a_4119_: *mut LeanObject,
    mut v_a_4120_: *mut LeanObject,
    mut v_a_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4134_: u8 = 0;
    let mut v_fst_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4144_: u8 = 0;
    let mut v_a_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4152_: u8 = 0;
    let mut v_a_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4156_: u8 = 0;
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_f_4113_);
                v___x_4123_ = l_Lean_Compiler_LCNF_inferType(
                    v_f_4113_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_,
                );
                if lean_obj_tag(v___x_4123_) == 0 {
                    v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
                    lean_inc(v_a_4124_);
                    lean_dec_ref_known(v___x_4123_, 1);
                    v___x_4125_ = lean_array_get_size(v_args_4114_);
                    v___x_4126_ = lean_unsigned_to_nat(0);
                    v___x_4127_ = lean_box(0);
                    v___x_4128_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4128_, 0, v_a_4124_);
                    lean_ctor_set(v___x_4128_, 1, v___x_4126_);
                    v___x_4129_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4129_, 0, v___x_4127_);
                    lean_ctor_set(v___x_4129_, 1, v___x_4128_);
                    v___x_4130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v___x_4125_, v_args_4114_, v_f_4113_, v___x_4126_, v___x_4129_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
                    if lean_obj_tag(v___x_4130_) == 0 {
                        v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
                        v_isSharedCheck_4144_ = (!lean_is_exclusive(v___x_4130_)) as u8;
                        if v_isSharedCheck_4144_ == 0 {
                            v___x_4133_ = v___x_4130_;
                            v_isShared_4134_ = v_isSharedCheck_4144_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4131_);
                            lean_dec(v___x_4130_);
                            v___x_4133_ = lean_box(0);
                            v_isShared_4134_ = v_isSharedCheck_4144_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4145_ = lean_ctor_get(v___x_4130_, 0);
                        v_isSharedCheck_4152_ = (!lean_is_exclusive(v___x_4130_)) as u8;
                        if v_isSharedCheck_4152_ == 0 {
                            v___x_4147_ = v___x_4130_;
                            v_isShared_4148_ = v_isSharedCheck_4152_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4145_);
                            lean_dec(v___x_4130_);
                            v___x_4147_ = lean_box(0);
                            v_isShared_4148_ = v_isSharedCheck_4152_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_args_4114_);
                    lean_dec_ref(v_f_4113_);
                    v_a_4153_ = lean_ctor_get(v___x_4123_, 0);
                    v_isSharedCheck_4160_ = (!lean_is_exclusive(v___x_4123_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4155_ = v___x_4123_;
                        v_isShared_4156_ = v_isSharedCheck_4160_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4153_);
                        lean_dec(v___x_4123_);
                        v___x_4155_ = lean_box(0);
                        v_isShared_4156_ = v_isSharedCheck_4160_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4135_ = lean_ctor_get(v_a_4131_, 0);
                lean_inc(v_fst_4135_);
                lean_dec(v_a_4131_);
                if lean_obj_tag(v_fst_4135_) == 0 {
                    v___x_4136_ = lean_box(0);
                    if v_isShared_4134_ == 0 {
                        lean_ctor_set(v___x_4133_, 0, v___x_4136_);
                        v___x_4138_ = v___x_4133_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
                        v___x_4138_ = v_reuseFailAlloc_4139_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_4140_ = lean_ctor_get(v_fst_4135_, 0);
                    lean_inc(v_val_4140_);
                    lean_dec_ref_known(v_fst_4135_, 1);
                    if v_isShared_4134_ == 0 {
                        lean_ctor_set(v___x_4133_, 0, v_val_4140_);
                        v___x_4142_ = v___x_4133_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_val_4140_);
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
                    v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
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
                    v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
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
    mut v_f_4161_: *mut LeanObject,
    mut v_args_4162_: *mut LeanObject,
    mut v_a_4163_: *mut LeanObject,
    mut v_a_4164_: *mut LeanObject,
    mut v_a_4165_: *mut LeanObject,
    mut v_a_4166_: *mut LeanObject,
    mut v_a_4167_: *mut LeanObject,
    mut v_a_4168_: *mut LeanObject,
    mut v_a_4169_: *mut LeanObject,
    mut v_a_4170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4171_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4169_);
    lean_dec_ref(v_a_4168_);
    lean_dec(v_a_4167_);
    lean_dec_ref(v_a_4166_);
    lean_dec_ref(v_a_4165_);
    lean_dec(v_a_4164_);
    lean_dec_ref(v_a_4163_);
    return v_res_4171_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1(
    mut v_upperBound_4172_: *mut LeanObject,
    mut v_args_4173_: *mut LeanObject,
    mut v_f_4174_: *mut LeanObject,
    mut v_inst_4175_: *mut LeanObject,
    mut v_R_4176_: *mut LeanObject,
    mut v_a_4177_: *mut LeanObject,
    mut v_b_4178_: *mut LeanObject,
    mut v_c_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
    mut v___y_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    v___x_4188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg(v_upperBound_4172_, v_args_4173_, v_f_4174_, v_a_4177_, v_b_4178_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
    return v___x_4188_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___boxed(
    mut v_upperBound_4189_: *mut LeanObject,
    mut v_args_4190_: *mut LeanObject,
    mut v_f_4191_: *mut LeanObject,
    mut v_inst_4192_: *mut LeanObject,
    mut v_R_4193_: *mut LeanObject,
    mut v_a_4194_: *mut LeanObject,
    mut v_b_4195_: *mut LeanObject,
    mut v_c_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4205_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4203_);
    lean_dec_ref(v___y_4202_);
    lean_dec(v___y_4201_);
    lean_dec_ref(v___y_4200_);
    lean_dec_ref(v___y_4199_);
    lean_dec(v___y_4198_);
    lean_dec_ref(v___y_4197_);
    lean_dec(v_upperBound_4189_);
    return v_res_4205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(
    mut v_e_4206_: *mut LeanObject,
    mut v_a_4207_: *mut LeanObject,
    mut v_a_4208_: *mut LeanObject,
    mut v_a_4209_: *mut LeanObject,
    mut v_a_4210_: *mut LeanObject,
    mut v_a_4211_: *mut LeanObject,
    mut v_a_4212_: *mut LeanObject,
    mut v_a_4213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4222_: u8 = 0;
    let mut v_unused_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_4206_) {
                0 => {
                    v_isSharedCheck_4222_ = (!lean_is_exclusive(v_e_4206_)) as u8;
                    if v_isSharedCheck_4222_ == 0 {
                        v_unused_4223_ = lean_ctor_get(v_e_4206_, 0);
                        lean_dec(v_unused_4223_);
                        v___x_4216_ = v_e_4206_;
                        v_isShared_4217_ = v_isSharedCheck_4222_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_e_4206_);
                        v___x_4216_ = lean_box(0);
                        v_isShared_4217_ = v_isSharedCheck_4222_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4224_ = lean_box(0);
                    v___x_4225_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4225_, 0, v___x_4224_);
                    return v___x_4225_;
                }
                2 => {
                    v_struct_4226_ = lean_ctor_get(v_e_4206_, 2);
                    lean_inc(v_struct_4226_);
                    lean_dec_ref_known(v_e_4206_, 3);
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
                    v_declName_4228_ = lean_ctor_get(v_e_4206_, 0);
                    lean_inc(v_declName_4228_);
                    v_us_4229_ = lean_ctor_get(v_e_4206_, 1);
                    lean_inc(v_us_4229_);
                    v_args_4230_ = lean_ctor_get(v_e_4206_, 2);
                    lean_inc_ref(v_args_4230_);
                    lean_dec_ref_known(v_e_4206_, 3);
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
                    v_fvarId_4233_ = lean_ctor_get(v_e_4206_, 0);
                    lean_inc_n(v_fvarId_4233_, 2);
                    v_args_4234_ = lean_ctor_get(v_e_4206_, 1);
                    lean_inc_ref(v_args_4234_);
                    lean_dec_ref_known(v_e_4206_, 2);
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
                    if lean_obj_tag(v___x_4235_) == 0 {
                        lean_dec_ref_known(v___x_4235_, 1);
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
                        lean_dec_ref(v_args_4234_);
                        lean_dec(v_fvarId_4233_);
                        return v___x_4235_;
                    }
                }
            },
            1 => {
                v___x_4218_ = lean_box(0);
                if v_isShared_4217_ == 0 {
                    lean_ctor_set(v___x_4216_, 0, v___x_4218_);
                    v___x_4220_ = v___x_4216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4218_);
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
    mut v_e_4238_: *mut LeanObject,
    mut v_a_4239_: *mut LeanObject,
    mut v_a_4240_: *mut LeanObject,
    mut v_a_4241_: *mut LeanObject,
    mut v_a_4242_: *mut LeanObject,
    mut v_a_4243_: *mut LeanObject,
    mut v_a_4244_: *mut LeanObject,
    mut v_a_4245_: *mut LeanObject,
    mut v_a_4246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4247_: *mut LeanObject = core::ptr::null_mut();
    v_res_4247_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetValue(
        v_e_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_,
    );
    lean_dec(v_a_4245_);
    lean_dec_ref(v_a_4244_);
    lean_dec(v_a_4243_);
    lean_dec_ref(v_a_4242_);
    lean_dec_ref(v_a_4241_);
    lean_dec(v_a_4240_);
    lean_dec_ref(v_a_4239_);
    return v_res_4247_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    v___x_4249_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___closed__0;
    v___x_4250_ = l_Lean_stringToMessageData(v___x_4249_);
    return v___x_4250_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
    mut v_jp_4251_: *mut LeanObject,
    mut v_a_4252_: *mut LeanObject,
    mut v_a_4253_: *mut LeanObject,
    mut v_a_4254_: *mut LeanObject,
    mut v_a_4255_: *mut LeanObject,
    mut v_a_4256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_jps_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: u8 = 0;
    v_jps_4258_ = lean_ctor_get(v_a_4252_, 0);
    v___x_4259_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__0___redArg(v_jp_4251_, v_jps_4258_);
    if v___x_4259_ == 0 {
        let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
        v___x_4260_ = lean_obj_once(
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
        v___x_4263_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_4263_, 0, v___x_4260_);
        lean_ctor_set(v___x_4263_, 1, v___x_4262_);
        v___x_4264_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
        v___x_4265_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_4265_, 0, v___x_4263_);
        lean_ctor_set(v___x_4265_, 1, v___x_4264_);
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
        let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_jp_4251_);
        v___x_4267_ = lean_box(0);
        v___x_4268_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4268_, 0, v___x_4267_);
        return v___x_4268_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg___boxed(
    mut v_jp_4269_: *mut LeanObject,
    mut v_a_4270_: *mut LeanObject,
    mut v_a_4271_: *mut LeanObject,
    mut v_a_4272_: *mut LeanObject,
    mut v_a_4273_: *mut LeanObject,
    mut v_a_4274_: *mut LeanObject,
    mut v_a_4275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4276_: *mut LeanObject = core::ptr::null_mut();
    v_res_4276_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
        v_jp_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_,
    );
    lean_dec(v_a_4274_);
    lean_dec_ref(v_a_4273_);
    lean_dec(v_a_4272_);
    lean_dec_ref(v_a_4271_);
    lean_dec_ref(v_a_4270_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(
    mut v_jp_4277_: *mut LeanObject,
    mut v_a_4278_: *mut LeanObject,
    mut v_a_4279_: *mut LeanObject,
    mut v_a_4280_: *mut LeanObject,
    mut v_a_4281_: *mut LeanObject,
    mut v_a_4282_: *mut LeanObject,
    mut v_a_4283_: *mut LeanObject,
    mut v_a_4284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    v___x_4286_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
        v_jp_4277_, v_a_4278_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_,
    );
    return v___x_4286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___boxed(
    mut v_jp_4287_: *mut LeanObject,
    mut v_a_4288_: *mut LeanObject,
    mut v_a_4289_: *mut LeanObject,
    mut v_a_4290_: *mut LeanObject,
    mut v_a_4291_: *mut LeanObject,
    mut v_a_4292_: *mut LeanObject,
    mut v_a_4293_: *mut LeanObject,
    mut v_a_4294_: *mut LeanObject,
    mut v_a_4295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4296_: *mut LeanObject = core::ptr::null_mut();
    v_res_4296_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope(
        v_jp_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_,
    );
    lean_dec(v_a_4294_);
    lean_dec_ref(v_a_4293_);
    lean_dec(v_a_4292_);
    lean_dec_ref(v_a_4291_);
    lean_dec_ref(v_a_4290_);
    lean_dec(v_a_4289_);
    lean_dec_ref(v_a_4288_);
    return v_res_4296_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    v___x_4298_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__0;
    v___x_4299_ = l_Lean_stringToMessageData(v___x_4298_);
    return v___x_4299_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    v___x_4301_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__2;
    v___x_4302_ = l_Lean_stringToMessageData(v___x_4301_);
    return v___x_4302_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
    mut v_param_4303_: *mut LeanObject,
    mut v_a_4304_: *mut LeanObject,
    mut v_a_4305_: *mut LeanObject,
    mut v_a_4306_: *mut LeanObject,
    mut v_a_4307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4317_: u8 = 0;
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4309_ = lean_ctor_get(v_param_4303_, 0);
                v_binderName_4310_ = lean_ctor_get(v_param_4303_, 1);
                lean_inc(v_binderName_4310_);
                v___x_4311_ = 0;
                lean_inc(v_fvarId_4309_);
                v___x_4312_ = l_Lean_Compiler_LCNF_getParam(
                    v___x_4311_,
                    v_fvarId_4309_,
                    v_a_4304_,
                    v_a_4305_,
                    v_a_4306_,
                    v_a_4307_,
                );
                if lean_obj_tag(v___x_4312_) == 0 {
                    v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4328_ = (!lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4315_ = v___x_4312_;
                        v_isShared_4316_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4313_);
                        lean_dec(v___x_4312_);
                        v___x_4315_ = lean_box(0);
                        v_isShared_4316_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_binderName_4310_);
                    lean_dec_ref(v_param_4303_);
                    v_a_4329_ = lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4336_ = (!lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4331_ = v___x_4312_;
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4329_);
                        lean_dec(v___x_4312_);
                        v___x_4331_ = lean_box(0);
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4317_ =
                    l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(v_param_4303_, v_a_4313_);
                lean_dec(v_a_4313_);
                lean_dec_ref(v_param_4303_);
                if v___x_4317_ == 0 {
                    lean_del_object(v___x_4315_);
                    v___x_4318_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__1,
                    );
                    v___x_4319_ = l_Lean_MessageData_ofName(v_binderName_4310_);
                    v___x_4320_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4320_, 0, v___x_4318_);
                    lean_ctor_set(v___x_4320_, 1, v___x_4319_);
                    v___x_4321_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg___closed__3,
                    );
                    v___x_4322_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4322_, 0, v___x_4320_);
                    lean_ctor_set(v___x_4322_, 1, v___x_4321_);
                    v___x_4323_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4322_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_);
                    return v___x_4323_;
                } else {
                    lean_dec(v_binderName_4310_);
                    v___x_4324_ = lean_box(0);
                    if v_isShared_4316_ == 0 {
                        lean_ctor_set(v___x_4315_, 0, v___x_4324_);
                        v___x_4326_ = v___x_4315_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
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
                    v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
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
    mut v_param_4337_: *mut LeanObject,
    mut v_a_4338_: *mut LeanObject,
    mut v_a_4339_: *mut LeanObject,
    mut v_a_4340_: *mut LeanObject,
    mut v_a_4341_: *mut LeanObject,
    mut v_a_4342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4343_: *mut LeanObject = core::ptr::null_mut();
    v_res_4343_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
        v_param_4337_,
        v_a_4338_,
        v_a_4339_,
        v_a_4340_,
        v_a_4341_,
    );
    lean_dec(v_a_4341_);
    lean_dec_ref(v_a_4340_);
    lean_dec(v_a_4339_);
    lean_dec_ref(v_a_4338_);
    return v_res_4343_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParam(
    mut v_param_4344_: *mut LeanObject,
    mut v_a_4345_: *mut LeanObject,
    mut v_a_4346_: *mut LeanObject,
    mut v_a_4347_: *mut LeanObject,
    mut v_a_4348_: *mut LeanObject,
    mut v_a_4349_: *mut LeanObject,
    mut v_a_4350_: *mut LeanObject,
    mut v_a_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_param_4354_: *mut LeanObject,
    mut v_a_4355_: *mut LeanObject,
    mut v_a_4356_: *mut LeanObject,
    mut v_a_4357_: *mut LeanObject,
    mut v_a_4358_: *mut LeanObject,
    mut v_a_4359_: *mut LeanObject,
    mut v_a_4360_: *mut LeanObject,
    mut v_a_4361_: *mut LeanObject,
    mut v_a_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4363_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4361_);
    lean_dec_ref(v_a_4360_);
    lean_dec(v_a_4359_);
    lean_dec_ref(v_a_4358_);
    lean_dec_ref(v_a_4357_);
    lean_dec(v_a_4356_);
    lean_dec_ref(v_a_4355_);
    return v_res_4363_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(
    mut v_as_4364_: *mut LeanObject,
    mut v_i_4365_: usize,
    mut v_stop_4366_: usize,
    mut v_b_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
    mut v___y_4371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: usize = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4373_ = lean_usize_dec_eq(v_i_4365_, v_stop_4366_);
                if v___x_4373_ == 0 {
                    v___x_4374_ = lean_array_uget_borrowed(v_as_4364_, v_i_4365_);
                    lean_inc(v___x_4374_);
                    v___x_4375_ = l_Lean_Compiler_LCNF_Check_Pure_checkParam___redArg(
                        v___x_4374_,
                        v___y_4368_,
                        v___y_4369_,
                        v___y_4370_,
                        v___y_4371_,
                    );
                    if lean_obj_tag(v___x_4375_) == 0 {
                        v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
                        lean_inc(v_a_4376_);
                        lean_dec_ref_known(v___x_4375_, 1);
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
                    v___x_4380_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4380_, 0, v_b_4367_);
                    return v___x_4380_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg___boxed(
    mut v_as_4381_: *mut LeanObject,
    mut v_i_4382_: *mut LeanObject,
    mut v_stop_4383_: *mut LeanObject,
    mut v_b_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
    mut v___y_4387_: *mut LeanObject,
    mut v___y_4388_: *mut LeanObject,
    mut v___y_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4390_: usize = 0;
    let mut v_stop_boxed_4391_: usize = 0;
    let mut v_res_4392_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4390_ = lean_unbox_usize(v_i_4382_);
    lean_dec(v_i_4382_);
    v_stop_boxed_4391_ = lean_unbox_usize(v_stop_4383_);
    lean_dec(v_stop_4383_);
    v_res_4392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_as_4381_, v_i_boxed_4390_, v_stop_boxed_4391_, v_b_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
    lean_dec(v___y_4388_);
    lean_dec_ref(v___y_4387_);
    lean_dec(v___y_4386_);
    lean_dec_ref(v___y_4385_);
    lean_dec_ref(v_as_4381_);
    return v_res_4392_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParams(
    mut v_params_4393_: *mut LeanObject,
    mut v_a_4394_: *mut LeanObject,
    mut v_a_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
    mut v_a_4398_: *mut LeanObject,
    mut v_a_4399_: *mut LeanObject,
    mut v_a_4400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: u8 = 0;
    v___x_4402_ = lean_unsigned_to_nat(0);
    v___x_4403_ = lean_array_get_size(v_params_4393_);
    v___x_4404_ = lean_box(0);
    v___x_4405_ = lean_nat_dec_lt(v___x_4402_, v___x_4403_);
    if v___x_4405_ == 0 {
        let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
        v___x_4406_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4406_, 0, v___x_4404_);
        return v___x_4406_;
    } else {
        let mut v___x_4407_: u8 = 0;
        v___x_4407_ = lean_nat_dec_le(v___x_4403_, v___x_4403_);
        if v___x_4407_ == 0 {
            if v___x_4405_ == 0 {
                let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
                v___x_4408_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4408_, 0, v___x_4404_);
                return v___x_4408_;
            } else {
                let mut v___x_4409_: usize = 0;
                let mut v___x_4410_: usize = 0;
                let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
                v___x_4409_ = 0usize;
                v___x_4410_ = lean_usize_of_nat(v___x_4403_);
                v___x_4411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_params_4393_, v___x_4409_, v___x_4410_, v___x_4404_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
                return v___x_4411_;
            }
        } else {
            let mut v___x_4412_: usize = 0;
            let mut v___x_4413_: usize = 0;
            let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
            v___x_4412_ = 0usize;
            v___x_4413_ = lean_usize_of_nat(v___x_4403_);
            v___x_4414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_params_4393_, v___x_4412_, v___x_4413_, v___x_4404_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
            return v___x_4414_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkParams___boxed(
    mut v_params_4415_: *mut LeanObject,
    mut v_a_4416_: *mut LeanObject,
    mut v_a_4417_: *mut LeanObject,
    mut v_a_4418_: *mut LeanObject,
    mut v_a_4419_: *mut LeanObject,
    mut v_a_4420_: *mut LeanObject,
    mut v_a_4421_: *mut LeanObject,
    mut v_a_4422_: *mut LeanObject,
    mut v_a_4423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4424_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4422_);
    lean_dec_ref(v_a_4421_);
    lean_dec(v_a_4420_);
    lean_dec_ref(v_a_4419_);
    lean_dec_ref(v_a_4418_);
    lean_dec(v_a_4417_);
    lean_dec_ref(v_a_4416_);
    lean_dec_ref(v_params_4415_);
    return v_res_4424_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(
    mut v_as_4425_: *mut LeanObject,
    mut v_i_4426_: usize,
    mut v_stop_4427_: usize,
    mut v_b_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
    mut v___y_4431_: *mut LeanObject,
    mut v___y_4432_: *mut LeanObject,
    mut v___y_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___redArg(v_as_4425_, v_i_4426_, v_stop_4427_, v_b_4428_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
    return v___x_4437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0___boxed(
    mut v_as_4438_: *mut LeanObject,
    mut v_i_4439_: *mut LeanObject,
    mut v_stop_4440_: *mut LeanObject,
    mut v_b_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4450_: usize = 0;
    let mut v_stop_boxed_4451_: usize = 0;
    let mut v_res_4452_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4450_ = lean_unbox_usize(v_i_4439_);
    lean_dec(v_i_4439_);
    v_stop_boxed_4451_ = lean_unbox_usize(v_stop_4440_);
    lean_dec(v_stop_4440_);
    v_res_4452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkParams_spec__0(v_as_4438_, v_i_boxed_4450_, v_stop_boxed_4451_, v_b_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
    lean_dec(v___y_4448_);
    lean_dec_ref(v___y_4447_);
    lean_dec(v___y_4446_);
    lean_dec_ref(v___y_4445_);
    lean_dec_ref(v___y_4444_);
    lean_dec(v___y_4443_);
    lean_dec_ref(v___y_4442_);
    lean_dec_ref(v_as_4438_);
    return v_res_4452_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1() -> *mut LeanObject {
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    v___x_4454_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__0;
    v___x_4455_ = l_Lean_stringToMessageData(v___x_4454_);
    return v___x_4455_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3() -> *mut LeanObject {
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    v___x_4457_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__2;
    v___x_4458_ = l_Lean_stringToMessageData(v___x_4457_);
    return v___x_4458_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5() -> *mut LeanObject {
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__4;
    v___x_4461_ = l_Lean_stringToMessageData(v___x_4460_);
    return v___x_4461_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7() -> *mut LeanObject {
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__6;
    v___x_4464_ = l_Lean_stringToMessageData(v___x_4463_);
    return v___x_4464_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl(
    mut v_letDecl_4465_: *mut LeanObject,
    mut v_a_4466_: *mut LeanObject,
    mut v_a_4467_: *mut LeanObject,
    mut v_a_4468_: *mut LeanObject,
    mut v_a_4469_: *mut LeanObject,
    mut v_a_4470_: *mut LeanObject,
    mut v_a_4471_: *mut LeanObject,
    mut v_a_4472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4488_: u8 = 0;
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut v_a_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4504_: u8 = 0;
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4508_: u8 = 0;
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u8 = 0;
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: u8 = 0;
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_a_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4542_: u8 = 0;
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v_a_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4550_: u8 = 0;
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4474_ = lean_ctor_get(v_letDecl_4465_, 0);
                v_binderName_4475_ = lean_ctor_get(v_letDecl_4465_, 1);
                lean_inc(v_binderName_4475_);
                v_type_4476_ = lean_ctor_get(v_letDecl_4465_, 2);
                v_value_4477_ = lean_ctor_get(v_letDecl_4465_, 3);
                lean_inc(v_value_4477_);
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
                if lean_obj_tag(v___x_4509_) == 0 {
                    lean_dec_ref_known(v___x_4509_, 1);
                    v___x_4510_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v_a_4469_);
                    if lean_obj_tag(v___x_4510_) == 0 {
                        v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
                        lean_inc(v_a_4511_);
                        lean_dec_ref_known(v___x_4510_, 1);
                        v___x_4512_ = (lean_unbox(v_a_4511_) as u8);
                        lean_dec(v_a_4511_);
                        if v___x_4512_ == 0 {
                            v___y_4479_ = v_a_4469_;
                            v___y_4480_ = v_a_4470_;
                            v___y_4481_ = v_a_4471_;
                            v___y_4482_ = v_a_4472_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4513_ = 0;
                            lean_inc(v_value_4477_);
                            v___x_4514_ = l_Lean_Compiler_LCNF_LetValue_inferType(
                                v___x_4513_,
                                v_value_4477_,
                                v_a_4469_,
                                v_a_4470_,
                                v_a_4471_,
                                v_a_4472_,
                            );
                            if lean_obj_tag(v___x_4514_) == 0 {
                                v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
                                lean_inc_n(v_a_4515_, 2);
                                lean_dec_ref_known(v___x_4514_, 1);
                                lean_inc_ref(v_type_4476_);
                                v___x_4516_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                    v_type_4476_,
                                    v_a_4515_,
                                    v_a_4468_,
                                    v_a_4469_,
                                    v_a_4470_,
                                    v_a_4471_,
                                    v_a_4472_,
                                );
                                if lean_obj_tag(v___x_4516_) == 0 {
                                    v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
                                    lean_inc(v_a_4517_);
                                    lean_dec_ref_known(v___x_4516_, 1);
                                    v___x_4518_ = (lean_unbox(v_a_4517_) as u8);
                                    lean_dec(v_a_4517_);
                                    if v___x_4518_ == 0 {
                                        lean_inc_ref(v_type_4476_);
                                        lean_dec_ref(v_letDecl_4465_);
                                        v___x_4519_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once), _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5);
                                        v___x_4520_ = l_Lean_MessageData_ofName(v_binderName_4475_);
                                        v___x_4521_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4521_, 0, v___x_4519_);
                                        lean_ctor_set(v___x_4521_, 1, v___x_4520_);
                                        v___x_4522_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once), _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7);
                                        v___x_4523_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4523_, 0, v___x_4521_);
                                        lean_ctor_set(v___x_4523_, 1, v___x_4522_);
                                        v___x_4524_ = l_Lean_indentExpr(v_a_4515_);
                                        v___x_4525_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4525_, 0, v___x_4523_);
                                        lean_ctor_set(v___x_4525_, 1, v___x_4524_);
                                        v___x_4526_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                                        v___x_4527_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4527_, 0, v___x_4525_);
                                        lean_ctor_set(v___x_4527_, 1, v___x_4526_);
                                        v___x_4528_ = l_Lean_indentExpr(v_type_4476_);
                                        v___x_4529_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4529_, 0, v___x_4527_);
                                        lean_ctor_set(v___x_4529_, 1, v___x_4528_);
                                        v___x_4530_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4529_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
                                        return v___x_4530_;
                                    } else {
                                        lean_dec(v_a_4515_);
                                        v___y_4479_ = v_a_4469_;
                                        v___y_4480_ = v_a_4470_;
                                        v___y_4481_ = v_a_4471_;
                                        v___y_4482_ = v_a_4472_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4515_);
                                    lean_dec(v_binderName_4475_);
                                    lean_dec_ref(v_letDecl_4465_);
                                    v_a_4531_ = lean_ctor_get(v___x_4516_, 0);
                                    v_isSharedCheck_4538_ = (!lean_is_exclusive(v___x_4516_)) as u8;
                                    if v_isSharedCheck_4538_ == 0 {
                                        v___x_4533_ = v___x_4516_;
                                        v_isShared_4534_ = v_isSharedCheck_4538_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4531_);
                                        lean_dec(v___x_4516_);
                                        v___x_4533_ = lean_box(0);
                                        v_isShared_4534_ = v_isSharedCheck_4538_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_binderName_4475_);
                                lean_dec_ref(v_letDecl_4465_);
                                v_a_4539_ = lean_ctor_get(v___x_4514_, 0);
                                v_isSharedCheck_4546_ = (!lean_is_exclusive(v___x_4514_)) as u8;
                                if v_isSharedCheck_4546_ == 0 {
                                    v___x_4541_ = v___x_4514_;
                                    v_isShared_4542_ = v_isSharedCheck_4546_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_4539_);
                                    lean_dec(v___x_4514_);
                                    v___x_4541_ = lean_box(0);
                                    v_isShared_4542_ = v_isSharedCheck_4546_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_binderName_4475_);
                        lean_dec_ref(v_letDecl_4465_);
                        v_a_4547_ = lean_ctor_get(v___x_4510_, 0);
                        v_isSharedCheck_4554_ = (!lean_is_exclusive(v___x_4510_)) as u8;
                        if v_isSharedCheck_4554_ == 0 {
                            v___x_4549_ = v___x_4510_;
                            v_isShared_4550_ = v_isSharedCheck_4554_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4547_);
                            lean_dec(v___x_4510_);
                            v___x_4549_ = lean_box(0);
                            v_isShared_4550_ = v_isSharedCheck_4554_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_binderName_4475_);
                    lean_dec_ref(v_letDecl_4465_);
                    return v___x_4509_;
                }
            }
            1 => {
                v___x_4483_ = 0;
                lean_inc(v_fvarId_4474_);
                v___x_4484_ = l_Lean_Compiler_LCNF_getLetDecl(
                    v___x_4483_,
                    v_fvarId_4474_,
                    v___y_4479_,
                    v___y_4480_,
                    v___y_4481_,
                    v___y_4482_,
                );
                if lean_obj_tag(v___x_4484_) == 0 {
                    v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
                    v_isSharedCheck_4500_ = (!lean_is_exclusive(v___x_4484_)) as u8;
                    if v_isSharedCheck_4500_ == 0 {
                        v___x_4487_ = v___x_4484_;
                        v_isShared_4488_ = v_isSharedCheck_4500_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4485_);
                        lean_dec(v___x_4484_);
                        v___x_4487_ = lean_box(0);
                        v_isShared_4488_ = v_isSharedCheck_4500_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_binderName_4475_);
                    lean_dec_ref(v_letDecl_4465_);
                    v_a_4501_ = lean_ctor_get(v___x_4484_, 0);
                    v_isSharedCheck_4508_ = (!lean_is_exclusive(v___x_4484_)) as u8;
                    if v_isSharedCheck_4508_ == 0 {
                        v___x_4503_ = v___x_4484_;
                        v_isShared_4504_ = v_isSharedCheck_4508_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4501_);
                        lean_dec(v___x_4484_);
                        v___x_4503_ = lean_box(0);
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
                lean_dec(v_a_4485_);
                lean_dec_ref(v_letDecl_4465_);
                if v___x_4489_ == 0 {
                    lean_del_object(v___x_4487_);
                    v___x_4490_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__1,
                    );
                    v___x_4491_ = l_Lean_MessageData_ofName(v_binderName_4475_);
                    v___x_4492_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4492_, 0, v___x_4490_);
                    lean_ctor_set(v___x_4492_, 1, v___x_4491_);
                    v___x_4493_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__3,
                    );
                    v___x_4494_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4494_, 0, v___x_4492_);
                    lean_ctor_set(v___x_4494_, 1, v___x_4493_);
                    v___x_4495_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4494_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
                    return v___x_4495_;
                } else {
                    lean_dec(v_binderName_4475_);
                    v___x_4496_ = lean_box(0);
                    if v_isShared_4488_ == 0 {
                        lean_ctor_set(v___x_4487_, 0, v___x_4496_);
                        v___x_4498_ = v___x_4487_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
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
                    v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
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
                    v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
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
                    v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
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
                    v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
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
    mut v_letDecl_4555_: *mut LeanObject,
    mut v_a_4556_: *mut LeanObject,
    mut v_a_4557_: *mut LeanObject,
    mut v_a_4558_: *mut LeanObject,
    mut v_a_4559_: *mut LeanObject,
    mut v_a_4560_: *mut LeanObject,
    mut v_a_4561_: *mut LeanObject,
    mut v_a_4562_: *mut LeanObject,
    mut v_a_4563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4564_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4562_);
    lean_dec_ref(v_a_4561_);
    lean_dec(v_a_4560_);
    lean_dec_ref(v_a_4559_);
    lean_dec_ref(v_a_4558_);
    lean_dec(v_a_4557_);
    lean_dec_ref(v_a_4556_);
    return v_res_4564_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(
    mut v_a_4565_: *mut LeanObject,
    mut v_x_4566_: *mut LeanObject,
) -> u8 {
    let mut v___x_4567_: u8 = 0;
    let mut v_key_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4566_) == 0 {
                    v___x_4567_ = 0;
                    return v___x_4567_;
                } else {
                    v_key_4568_ = lean_ctor_get(v_x_4566_, 0);
                    v_tail_4569_ = lean_ctor_get(v_x_4566_, 2);
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
    mut v_a_4572_: *mut LeanObject,
    mut v_x_4573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4574_: u8 = 0;
    let mut v_r_4575_: *mut LeanObject = core::ptr::null_mut();
    v_res_4574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_4572_, v_x_4573_);
    lean_dec(v_x_4573_);
    lean_dec(v_a_4572_);
    v_r_4575_ = lean_box((v_res_4574_) as usize);
    return v_r_4575_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_4576_: *mut LeanObject,
    mut v_x_4577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4577_) == 0 {
                    return v_x_4576_;
                } else {
                    v_key_4578_ = lean_ctor_get(v_x_4577_, 0);
                    v_value_4579_ = lean_ctor_get(v_x_4577_, 1);
                    v_tail_4580_ = lean_ctor_get(v_x_4577_, 2);
                    v_isSharedCheck_4603_ = (!lean_is_exclusive(v_x_4577_)) as u8;
                    if v_isSharedCheck_4603_ == 0 {
                        v___x_4582_ = v_x_4577_;
                        v_isShared_4583_ = v_isSharedCheck_4603_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4580_);
                        lean_inc(v_value_4579_);
                        lean_inc(v_key_4578_);
                        lean_dec(v_x_4577_);
                        v___x_4582_ = lean_box(0);
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
                lean_inc(v___x_4597_);
                if v_isShared_4583_ == 0 {
                    lean_ctor_set(v___x_4582_, 2, v___x_4597_);
                    v___x_4599_ = v___x_4582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_key_4578_);
                    lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_value_4579_);
                    lean_ctor_set(v_reuseFailAlloc_4602_, 2, v___x_4597_);
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
    mut v_i_4604_: *mut LeanObject,
    mut v_source_4605_: *mut LeanObject,
    mut v_target_4606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: u8 = 0;
    let mut v_es_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4607_ = lean_array_get_size(v_source_4605_);
                v___x_4608_ = lean_nat_dec_lt(v_i_4604_, v___x_4607_);
                if v___x_4608_ == 0 {
                    lean_dec_ref(v_source_4605_);
                    lean_dec(v_i_4604_);
                    return v_target_4606_;
                } else {
                    v_es_4609_ = lean_array_fget(v_source_4605_, v_i_4604_);
                    v___x_4610_ = lean_box(0);
                    v_source_4611_ = lean_array_fset(v_source_4605_, v_i_4604_, v___x_4610_);
                    v_target_4612_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4606_, v_es_4609_);
                    v___x_4613_ = lean_unsigned_to_nat(1);
                    v___x_4614_ = lean_nat_add(v_i_4604_, v___x_4613_);
                    lean_dec(v_i_4604_);
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
    mut v_data_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    v___x_4617_ = lean_array_get_size(v_data_4616_);
    v___x_4618_ = lean_unsigned_to_nat(2);
    v_nbuckets_4619_ = lean_nat_mul(v___x_4617_, v___x_4618_);
    v___x_4620_ = lean_unsigned_to_nat(0);
    v___x_4621_ = lean_box(0);
    v___x_4622_ = lean_mk_array(v_nbuckets_4619_, v___x_4621_);
    v___x_4623_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(v___x_4620_, v_data_4616_, v___x_4622_);
    return v___x_4623_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(
    mut v_m_4624_: *mut LeanObject,
    mut v_a_4625_: *mut LeanObject,
    mut v_b_4626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: u8 = 0;
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4646_: u8 = 0;
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v_val_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v_unused_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4627_ = lean_ctor_get(v_m_4624_, 0);
                v_buckets_4628_ = lean_ctor_get(v_m_4624_, 1);
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
                    lean_inc_ref(v_buckets_4628_);
                    lean_inc(v_size_4627_);
                    v_isSharedCheck_4664_ = (!lean_is_exclusive(v_m_4624_)) as u8;
                    if v_isSharedCheck_4664_ == 0 {
                        v_unused_4665_ = lean_ctor_get(v_m_4624_, 1);
                        lean_dec(v_unused_4665_);
                        v_unused_4666_ = lean_ctor_get(v_m_4624_, 0);
                        lean_dec(v_unused_4666_);
                        v___x_4645_ = v_m_4624_;
                        v_isShared_4646_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_4624_);
                        v___x_4645_ = lean_box(0);
                        v_isShared_4646_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_4626_);
                    lean_dec(v_a_4625_);
                    return v_m_4624_;
                }
            }
            1 => {
                v___x_4647_ = lean_unsigned_to_nat(1);
                v_size_x27_4648_ = lean_nat_add(v_size_4627_, v___x_4647_);
                lean_dec(v_size_4627_);
                lean_inc(v_bkt_4642_);
                v___x_4649_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4649_, 0, v_a_4625_);
                lean_ctor_set(v___x_4649_, 1, v_b_4626_);
                lean_ctor_set(v___x_4649_, 2, v_bkt_4642_);
                v_buckets_x27_4650_ = lean_array_uset(v_buckets_4628_, v___x_4641_, v___x_4649_);
                v___x_4651_ = lean_unsigned_to_nat(4);
                v___x_4652_ = lean_nat_mul(v_size_x27_4648_, v___x_4651_);
                v___x_4653_ = lean_unsigned_to_nat(3);
                v___x_4654_ = lean_nat_div(v___x_4652_, v___x_4653_);
                lean_dec(v___x_4652_);
                v___x_4655_ = lean_array_get_size(v_buckets_x27_4650_);
                v___x_4656_ = lean_nat_dec_le(v___x_4654_, v___x_4655_);
                lean_dec(v___x_4654_);
                if v___x_4656_ == 0 {
                    v_val_4657_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(v_buckets_x27_4650_);
                    if v_isShared_4646_ == 0 {
                        lean_ctor_set(v___x_4645_, 1, v_val_4657_);
                        lean_ctor_set(v___x_4645_, 0, v_size_x27_4648_);
                        v___x_4659_ = v___x_4645_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_size_x27_4648_);
                        lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_val_4657_);
                        v___x_4659_ = v_reuseFailAlloc_4660_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4646_ == 0 {
                        lean_ctor_set(v___x_4645_, 1, v_buckets_x27_4650_);
                        lean_ctor_set(v___x_4645_, 0, v_size_x27_4648_);
                        v___x_4662_ = v___x_4645_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_size_x27_4648_);
                        lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_buckets_x27_4650_);
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
    mut v_m_4667_: *mut LeanObject,
    mut v_a_4668_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    v_buckets_4669_ = lean_ctor_get(v_m_4667_, 1);
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
    mut v_m_4685_: *mut LeanObject,
    mut v_a_4686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4687_: u8 = 0;
    let mut v_r_4688_: *mut LeanObject = core::ptr::null_mut();
    v_res_4687_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v_m_4685_, v_a_4686_);
    lean_dec(v_a_4686_);
    lean_dec_ref(v_m_4685_);
    v_r_4688_ = lean_box((v_res_4687_) as usize);
    return v_r_4688_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    v___x_4690_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__0;
    v___x_4691_ = l_Lean_stringToMessageData(v___x_4690_);
    return v___x_4691_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
    mut v_fvarId_4692_: *mut LeanObject,
    mut v_a_4693_: *mut LeanObject,
    mut v_a_4694_: *mut LeanObject,
    mut v_a_4695_: *mut LeanObject,
    mut v_a_4696_: *mut LeanObject,
    mut v_a_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: u8 = 0;
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4706_ = lean_st_ref_get(v_a_4693_);
                v___x_4707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v___x_4706_, v_fvarId_4692_);
                lean_dec(v___x_4706_);
                if v___x_4707_ == 0 {
                    v___y_4700_ = v_a_4693_;
                    state = 1;
                    continue;
                } else {
                    v___x_4708_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___closed__1,
                    );
                    v___x_4709_ = l_Lean_MessageData_ofName(v_fvarId_4692_);
                    v___x_4710_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4710_, 0, v___x_4708_);
                    lean_ctor_set(v___x_4710_, 1, v___x_4709_);
                    v___x_4711_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                    v___x_4712_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4712_, 0, v___x_4710_);
                    lean_ctor_set(v___x_4712_, 1, v___x_4711_);
                    v___x_4713_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_4712_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
                    return v___x_4713_;
                }
            }
            1 => {
                v___x_4701_ = lean_st_ref_take(v___y_4700_);
                v___x_4702_ = lean_box(0);
                v___x_4703_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(v___x_4701_, v_fvarId_4692_, v___x_4702_);
                v___x_4704_ = lean_st_ref_set(v___y_4700_, v___x_4703_);
                v___x_4705_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4705_, 0, v___x_4702_);
                return v___x_4705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg___boxed(
    mut v_fvarId_4714_: *mut LeanObject,
    mut v_a_4715_: *mut LeanObject,
    mut v_a_4716_: *mut LeanObject,
    mut v_a_4717_: *mut LeanObject,
    mut v_a_4718_: *mut LeanObject,
    mut v_a_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4721_: *mut LeanObject = core::ptr::null_mut();
    v_res_4721_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
        v_fvarId_4714_,
        v_a_4715_,
        v_a_4716_,
        v_a_4717_,
        v_a_4718_,
        v_a_4719_,
    );
    lean_dec(v_a_4719_);
    lean_dec_ref(v_a_4718_);
    lean_dec(v_a_4717_);
    lean_dec_ref(v_a_4716_);
    lean_dec(v_a_4715_);
    return v_res_4721_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_addFVarId(
    mut v_fvarId_4722_: *mut LeanObject,
    mut v_a_4723_: *mut LeanObject,
    mut v_a_4724_: *mut LeanObject,
    mut v_a_4725_: *mut LeanObject,
    mut v_a_4726_: *mut LeanObject,
    mut v_a_4727_: *mut LeanObject,
    mut v_a_4728_: *mut LeanObject,
    mut v_a_4729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_fvarId_4732_: *mut LeanObject,
    mut v_a_4733_: *mut LeanObject,
    mut v_a_4734_: *mut LeanObject,
    mut v_a_4735_: *mut LeanObject,
    mut v_a_4736_: *mut LeanObject,
    mut v_a_4737_: *mut LeanObject,
    mut v_a_4738_: *mut LeanObject,
    mut v_a_4739_: *mut LeanObject,
    mut v_a_4740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4741_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4739_);
    lean_dec_ref(v_a_4738_);
    lean_dec(v_a_4737_);
    lean_dec_ref(v_a_4736_);
    lean_dec_ref(v_a_4735_);
    lean_dec(v_a_4734_);
    lean_dec_ref(v_a_4733_);
    return v_res_4741_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0(
    mut v_00_u03b2_4742_: *mut LeanObject,
    mut v_m_4743_: *mut LeanObject,
    mut v_a_4744_: *mut LeanObject,
    mut v_b_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    v___x_4746_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0___redArg(v_m_4743_, v_a_4744_, v_b_4745_);
    return v___x_4746_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(
    mut v_00_u03b2_4747_: *mut LeanObject,
    mut v_m_4748_: *mut LeanObject,
    mut v_a_4749_: *mut LeanObject,
) -> u8 {
    let mut v___x_4750_: u8 = 0;
    v___x_4750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___redArg(v_m_4748_, v_a_4749_);
    return v___x_4750_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1___boxed(
    mut v_00_u03b2_4751_: *mut LeanObject,
    mut v_m_4752_: *mut LeanObject,
    mut v_a_4753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4754_: u8 = 0;
    let mut v_r_4755_: *mut LeanObject = core::ptr::null_mut();
    v_res_4754_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__1(v_00_u03b2_4751_, v_m_4752_, v_a_4753_);
    lean_dec(v_a_4753_);
    lean_dec_ref(v_m_4752_);
    v_r_4755_ = lean_box((v_res_4754_) as usize);
    return v_r_4755_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(
    mut v_00_u03b2_4756_: *mut LeanObject,
    mut v_a_4757_: *mut LeanObject,
    mut v_x_4758_: *mut LeanObject,
) -> u8 {
    let mut v___x_4759_: u8 = 0;
    v___x_4759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___redArg(v_a_4757_, v_x_4758_);
    return v___x_4759_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0___boxed(
    mut v_00_u03b2_4760_: *mut LeanObject,
    mut v_a_4761_: *mut LeanObject,
    mut v_x_4762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4763_: u8 = 0;
    let mut v_r_4764_: *mut LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__0(v_00_u03b2_4760_, v_a_4761_, v_x_4762_);
    lean_dec(v_x_4762_);
    lean_dec(v_a_4761_);
    v_r_4764_ = lean_box((v_res_4763_) as usize);
    return v_r_4764_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1(
    mut v_00_u03b2_4765_: *mut LeanObject,
    mut v_data_4766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    v___x_4767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1___redArg(v_data_4766_);
    return v___x_4767_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4768_: *mut LeanObject,
    mut v_i_4769_: *mut LeanObject,
    mut v_source_4770_: *mut LeanObject,
    mut v_target_4771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    v___x_4772_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2___redArg(v_i_4769_, v_source_4770_, v_target_4771_);
    return v___x_4772_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4773_: *mut LeanObject,
    mut v_x_4774_: *mut LeanObject,
    mut v_x_4775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    v___x_4776_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Check_Pure_addFVarId_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4774_, v_x_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withFVarId___redArg(
    mut v_fvarId_4777_: *mut LeanObject,
    mut v_x_4778_: *mut LeanObject,
    mut v_a_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
    mut v_a_4781_: *mut LeanObject,
    mut v_a_4782_: *mut LeanObject,
    mut v_a_4783_: *mut LeanObject,
    mut v_a_4784_: *mut LeanObject,
    mut v_a_4785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_4777_);
                v___x_4787_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4777_,
                    v_a_4780_,
                    v_a_4782_,
                    v_a_4783_,
                    v_a_4784_,
                    v_a_4785_,
                );
                if lean_obj_tag(v___x_4787_) == 0 {
                    lean_dec_ref_known(v___x_4787_, 1);
                    v_jps_4788_ = lean_ctor_get(v_a_4779_, 0);
                    v_vars_4789_ = lean_ctor_get(v_a_4779_, 1);
                    lean_inc(v_vars_4789_);
                    v___x_4790_ = l_Lean_FVarIdSet_insert(v_vars_4789_, v_fvarId_4777_);
                    lean_inc(v_jps_4788_);
                    v___x_4791_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4791_, 0, v_jps_4788_);
                    lean_ctor_set(v___x_4791_, 1, v___x_4790_);
                    lean_inc(v_a_4785_);
                    lean_inc_ref(v_a_4784_);
                    lean_inc(v_a_4783_);
                    lean_inc_ref(v_a_4782_);
                    lean_inc_ref(v_a_4781_);
                    lean_inc(v_a_4780_);
                    v___x_4792_ = lean_apply_8(
                        v_x_4778_,
                        v___x_4791_,
                        v_a_4780_,
                        v_a_4781_,
                        v_a_4782_,
                        v_a_4783_,
                        v_a_4784_,
                        v_a_4785_,
                        lean_box(0),
                    );
                    return v___x_4792_;
                } else {
                    lean_dec_ref(v_x_4778_);
                    lean_dec(v_fvarId_4777_);
                    v_a_4793_ = lean_ctor_get(v___x_4787_, 0);
                    v_isSharedCheck_4800_ = (!lean_is_exclusive(v___x_4787_)) as u8;
                    if v_isSharedCheck_4800_ == 0 {
                        v___x_4795_ = v___x_4787_;
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4793_);
                        lean_dec(v___x_4787_);
                        v___x_4795_ = lean_box(0);
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
                    v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
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
    mut v_fvarId_4801_: *mut LeanObject,
    mut v_x_4802_: *mut LeanObject,
    mut v_a_4803_: *mut LeanObject,
    mut v_a_4804_: *mut LeanObject,
    mut v_a_4805_: *mut LeanObject,
    mut v_a_4806_: *mut LeanObject,
    mut v_a_4807_: *mut LeanObject,
    mut v_a_4808_: *mut LeanObject,
    mut v_a_4809_: *mut LeanObject,
    mut v_a_4810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4811_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4809_);
    lean_dec_ref(v_a_4808_);
    lean_dec(v_a_4807_);
    lean_dec_ref(v_a_4806_);
    lean_dec_ref(v_a_4805_);
    lean_dec(v_a_4804_);
    lean_dec_ref(v_a_4803_);
    return v_res_4811_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withFVarId(
    mut v_00_u03b1_4812_: *mut LeanObject,
    mut v_fvarId_4813_: *mut LeanObject,
    mut v_x_4814_: *mut LeanObject,
    mut v_a_4815_: *mut LeanObject,
    mut v_a_4816_: *mut LeanObject,
    mut v_a_4817_: *mut LeanObject,
    mut v_a_4818_: *mut LeanObject,
    mut v_a_4819_: *mut LeanObject,
    mut v_a_4820_: *mut LeanObject,
    mut v_a_4821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4832_: u8 = 0;
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_4813_);
                v___x_4823_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4813_,
                    v_a_4816_,
                    v_a_4818_,
                    v_a_4819_,
                    v_a_4820_,
                    v_a_4821_,
                );
                if lean_obj_tag(v___x_4823_) == 0 {
                    lean_dec_ref_known(v___x_4823_, 1);
                    v_jps_4824_ = lean_ctor_get(v_a_4815_, 0);
                    v_vars_4825_ = lean_ctor_get(v_a_4815_, 1);
                    lean_inc(v_vars_4825_);
                    v___x_4826_ = l_Lean_FVarIdSet_insert(v_vars_4825_, v_fvarId_4813_);
                    lean_inc(v_jps_4824_);
                    v___x_4827_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4827_, 0, v_jps_4824_);
                    lean_ctor_set(v___x_4827_, 1, v___x_4826_);
                    lean_inc(v_a_4821_);
                    lean_inc_ref(v_a_4820_);
                    lean_inc(v_a_4819_);
                    lean_inc_ref(v_a_4818_);
                    lean_inc_ref(v_a_4817_);
                    lean_inc(v_a_4816_);
                    v___x_4828_ = lean_apply_8(
                        v_x_4814_,
                        v___x_4827_,
                        v_a_4816_,
                        v_a_4817_,
                        v_a_4818_,
                        v_a_4819_,
                        v_a_4820_,
                        v_a_4821_,
                        lean_box(0),
                    );
                    return v___x_4828_;
                } else {
                    lean_dec_ref(v_x_4814_);
                    lean_dec(v_fvarId_4813_);
                    v_a_4829_ = lean_ctor_get(v___x_4823_, 0);
                    v_isSharedCheck_4836_ = (!lean_is_exclusive(v___x_4823_)) as u8;
                    if v_isSharedCheck_4836_ == 0 {
                        v___x_4831_ = v___x_4823_;
                        v_isShared_4832_ = v_isSharedCheck_4836_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4829_);
                        lean_dec(v___x_4823_);
                        v___x_4831_ = lean_box(0);
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
                    v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
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
    mut v_00_u03b1_4837_: *mut LeanObject,
    mut v_fvarId_4838_: *mut LeanObject,
    mut v_x_4839_: *mut LeanObject,
    mut v_a_4840_: *mut LeanObject,
    mut v_a_4841_: *mut LeanObject,
    mut v_a_4842_: *mut LeanObject,
    mut v_a_4843_: *mut LeanObject,
    mut v_a_4844_: *mut LeanObject,
    mut v_a_4845_: *mut LeanObject,
    mut v_a_4846_: *mut LeanObject,
    mut v_a_4847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4848_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4846_);
    lean_dec_ref(v_a_4845_);
    lean_dec(v_a_4844_);
    lean_dec_ref(v_a_4843_);
    lean_dec_ref(v_a_4842_);
    lean_dec(v_a_4841_);
    lean_dec_ref(v_a_4840_);
    return v_res_4848_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withJp___redArg(
    mut v_fvarId_4849_: *mut LeanObject,
    mut v_x_4850_: *mut LeanObject,
    mut v_a_4851_: *mut LeanObject,
    mut v_a_4852_: *mut LeanObject,
    mut v_a_4853_: *mut LeanObject,
    mut v_a_4854_: *mut LeanObject,
    mut v_a_4855_: *mut LeanObject,
    mut v_a_4856_: *mut LeanObject,
    mut v_a_4857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_4849_);
                v___x_4859_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4849_,
                    v_a_4852_,
                    v_a_4854_,
                    v_a_4855_,
                    v_a_4856_,
                    v_a_4857_,
                );
                if lean_obj_tag(v___x_4859_) == 0 {
                    lean_dec_ref_known(v___x_4859_, 1);
                    v_jps_4860_ = lean_ctor_get(v_a_4851_, 0);
                    v_vars_4861_ = lean_ctor_get(v_a_4851_, 1);
                    lean_inc(v_jps_4860_);
                    v___x_4862_ = l_Lean_FVarIdSet_insert(v_jps_4860_, v_fvarId_4849_);
                    lean_inc(v_vars_4861_);
                    v___x_4863_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4863_, 0, v___x_4862_);
                    lean_ctor_set(v___x_4863_, 1, v_vars_4861_);
                    lean_inc(v_a_4857_);
                    lean_inc_ref(v_a_4856_);
                    lean_inc(v_a_4855_);
                    lean_inc_ref(v_a_4854_);
                    lean_inc_ref(v_a_4853_);
                    lean_inc(v_a_4852_);
                    v___x_4864_ = lean_apply_8(
                        v_x_4850_,
                        v___x_4863_,
                        v_a_4852_,
                        v_a_4853_,
                        v_a_4854_,
                        v_a_4855_,
                        v_a_4856_,
                        v_a_4857_,
                        lean_box(0),
                    );
                    return v___x_4864_;
                } else {
                    lean_dec_ref(v_x_4850_);
                    lean_dec(v_fvarId_4849_);
                    v_a_4865_ = lean_ctor_get(v___x_4859_, 0);
                    v_isSharedCheck_4872_ = (!lean_is_exclusive(v___x_4859_)) as u8;
                    if v_isSharedCheck_4872_ == 0 {
                        v___x_4867_ = v___x_4859_;
                        v_isShared_4868_ = v_isSharedCheck_4872_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4865_);
                        lean_dec(v___x_4859_);
                        v___x_4867_ = lean_box(0);
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
                    v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
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
    mut v_fvarId_4873_: *mut LeanObject,
    mut v_x_4874_: *mut LeanObject,
    mut v_a_4875_: *mut LeanObject,
    mut v_a_4876_: *mut LeanObject,
    mut v_a_4877_: *mut LeanObject,
    mut v_a_4878_: *mut LeanObject,
    mut v_a_4879_: *mut LeanObject,
    mut v_a_4880_: *mut LeanObject,
    mut v_a_4881_: *mut LeanObject,
    mut v_a_4882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4883_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4881_);
    lean_dec_ref(v_a_4880_);
    lean_dec(v_a_4879_);
    lean_dec_ref(v_a_4878_);
    lean_dec_ref(v_a_4877_);
    lean_dec(v_a_4876_);
    lean_dec_ref(v_a_4875_);
    return v_res_4883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withJp(
    mut v_00_u03b1_4884_: *mut LeanObject,
    mut v_fvarId_4885_: *mut LeanObject,
    mut v_x_4886_: *mut LeanObject,
    mut v_a_4887_: *mut LeanObject,
    mut v_a_4888_: *mut LeanObject,
    mut v_a_4889_: *mut LeanObject,
    mut v_a_4890_: *mut LeanObject,
    mut v_a_4891_: *mut LeanObject,
    mut v_a_4892_: *mut LeanObject,
    mut v_a_4893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4904_: u8 = 0;
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_4885_);
                v___x_4895_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                    v_fvarId_4885_,
                    v_a_4888_,
                    v_a_4890_,
                    v_a_4891_,
                    v_a_4892_,
                    v_a_4893_,
                );
                if lean_obj_tag(v___x_4895_) == 0 {
                    lean_dec_ref_known(v___x_4895_, 1);
                    v_jps_4896_ = lean_ctor_get(v_a_4887_, 0);
                    v_vars_4897_ = lean_ctor_get(v_a_4887_, 1);
                    lean_inc(v_jps_4896_);
                    v___x_4898_ = l_Lean_FVarIdSet_insert(v_jps_4896_, v_fvarId_4885_);
                    lean_inc(v_vars_4897_);
                    v___x_4899_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4899_, 0, v___x_4898_);
                    lean_ctor_set(v___x_4899_, 1, v_vars_4897_);
                    lean_inc(v_a_4893_);
                    lean_inc_ref(v_a_4892_);
                    lean_inc(v_a_4891_);
                    lean_inc_ref(v_a_4890_);
                    lean_inc_ref(v_a_4889_);
                    lean_inc(v_a_4888_);
                    v___x_4900_ = lean_apply_8(
                        v_x_4886_,
                        v___x_4899_,
                        v_a_4888_,
                        v_a_4889_,
                        v_a_4890_,
                        v_a_4891_,
                        v_a_4892_,
                        v_a_4893_,
                        lean_box(0),
                    );
                    return v___x_4900_;
                } else {
                    lean_dec_ref(v_x_4886_);
                    lean_dec(v_fvarId_4885_);
                    v_a_4901_ = lean_ctor_get(v___x_4895_, 0);
                    v_isSharedCheck_4908_ = (!lean_is_exclusive(v___x_4895_)) as u8;
                    if v_isSharedCheck_4908_ == 0 {
                        v___x_4903_ = v___x_4895_;
                        v_isShared_4904_ = v_isSharedCheck_4908_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4901_);
                        lean_dec(v___x_4895_);
                        v___x_4903_ = lean_box(0);
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
                    v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
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
    mut v_00_u03b1_4909_: *mut LeanObject,
    mut v_fvarId_4910_: *mut LeanObject,
    mut v_x_4911_: *mut LeanObject,
    mut v_a_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
    mut v_a_4916_: *mut LeanObject,
    mut v_a_4917_: *mut LeanObject,
    mut v_a_4918_: *mut LeanObject,
    mut v_a_4919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4920_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4918_);
    lean_dec_ref(v_a_4917_);
    lean_dec(v_a_4916_);
    lean_dec_ref(v_a_4915_);
    lean_dec_ref(v_a_4914_);
    lean_dec(v_a_4913_);
    lean_dec_ref(v_a_4912_);
    return v_res_4920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__0(
    mut v_x1_4921_: *mut LeanObject,
    mut v_x2_4922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    v_fvarId_4923_ = lean_ctor_get(v_x2_4922_, 0);
    lean_inc(v_fvarId_4923_);
    lean_dec_ref(v_x2_4922_);
    v___x_4924_ = l_Lean_FVarIdSet_insert(v_x1_4921_, v_fvarId_4923_);
    return v___x_4924_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___lam__1(
    mut v_x_4925_: *mut LeanObject,
    mut v___y_4926_: *mut LeanObject,
    mut v___y_4927_: *mut LeanObject,
    mut v___y_4928_: *mut LeanObject,
    mut v___y_4929_: *mut LeanObject,
    mut v___y_4930_: *mut LeanObject,
    mut v___y_4931_: *mut LeanObject,
    mut v___y_4932_: *mut LeanObject,
    mut v___y_4933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    v_fvarId_4935_ = lean_ctor_get(v___y_4926_, 0);
    lean_inc(v_fvarId_4935_);
    lean_dec_ref(v___y_4926_);
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
    mut v_x_4937_: *mut LeanObject,
    mut v___y_4938_: *mut LeanObject,
    mut v___y_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
    mut v___y_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
    mut v___y_4944_: *mut LeanObject,
    mut v___y_4945_: *mut LeanObject,
    mut v___y_4946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4947_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4945_);
    lean_dec_ref(v___y_4944_);
    lean_dec(v___y_4943_);
    lean_dec_ref(v___y_4942_);
    lean_dec_ref(v___y_4941_);
    lean_dec(v___y_4940_);
    lean_dec_ref(v___y_4939_);
    return v_res_4947_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    v___x_4948_ = l_instMonadEIO(lean_box(0));
    return v___x_4948_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    v___x_4949_ = lean_obj_once(
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
    mut v_params_4976_: *mut LeanObject,
    mut v_x_4977_: *mut LeanObject,
    mut v_a_4978_: *mut LeanObject,
    mut v_a_4979_: *mut LeanObject,
    mut v_a_4980_: *mut LeanObject,
    mut v_a_4981_: *mut LeanObject,
    mut v_a_4982_: *mut LeanObject,
    mut v_a_4983_: *mut LeanObject,
    mut v_a_4984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v_toFunctor_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v___f_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: u8 = 0;
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: usize = 0;
    let mut v___x_5041_: usize = 0;
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: usize = 0;
    let mut v___x_5046_: usize = 0;
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v___x_5060_: u8 = 0;
    let mut v___f_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5064_: usize = 0;
    let mut v___x_5065_: usize = 0;
    let mut v___x_1277__overap_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: usize = 0;
    let mut v___x_5069_: usize = 0;
    let mut v___x_1281__overap_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5074_: u8 = 0;
    let mut v_unused_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5076_: u8 = 0;
    let mut v_unused_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4986_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1,
                );
                v_toApplicative_4987_ = lean_ctor_get(v___x_4986_, 0);
                v_toFunctor_4988_ = lean_ctor_get(v_toApplicative_4987_, 0);
                v_toSeq_4989_ = lean_ctor_get(v_toApplicative_4987_, 2);
                v_toSeqLeft_4990_ = lean_ctor_get(v_toApplicative_4987_, 3);
                v_toSeqRight_4991_ = lean_ctor_get(v_toApplicative_4987_, 4);
                v___f_4992_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2;
                v___f_4993_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3;
                lean_inc_ref_n(v_toFunctor_4988_, 2);
                v___f_4994_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4994_, 0, v_toFunctor_4988_);
                v___f_4995_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4995_, 0, v_toFunctor_4988_);
                v___x_4996_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4996_, 0, v___f_4994_);
                lean_ctor_set(v___x_4996_, 1, v___f_4995_);
                lean_inc(v_toSeqRight_4991_);
                v___f_4997_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4997_, 0, v_toSeqRight_4991_);
                lean_inc(v_toSeqLeft_4990_);
                v___f_4998_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4998_, 0, v_toSeqLeft_4990_);
                lean_inc(v_toSeq_4989_);
                v___f_4999_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4999_, 0, v_toSeq_4989_);
                v___x_5000_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5000_, 0, v___x_4996_);
                lean_ctor_set(v___x_5000_, 1, v___f_4992_);
                lean_ctor_set(v___x_5000_, 2, v___f_4999_);
                lean_ctor_set(v___x_5000_, 3, v___f_4998_);
                lean_ctor_set(v___x_5000_, 4, v___f_4997_);
                v___x_5001_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5001_, 0, v___x_5000_);
                lean_ctor_set(v___x_5001_, 1, v___f_4993_);
                v___x_5002_ = l_StateRefT_x27_instMonad___redArg(v___x_5001_);
                v_toApplicative_5003_ = lean_ctor_get(v___x_5002_, 0);
                v_isSharedCheck_5076_ = (!lean_is_exclusive(v___x_5002_)) as u8;
                if v_isSharedCheck_5076_ == 0 {
                    v_unused_5077_ = lean_ctor_get(v___x_5002_, 1);
                    lean_dec(v_unused_5077_);
                    v___x_5005_ = v___x_5002_;
                    v_isShared_5006_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5003_);
                    lean_dec(v___x_5002_);
                    v___x_5005_ = lean_box(0);
                    v_isShared_5006_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5007_ = lean_ctor_get(v_toApplicative_5003_, 0);
                v_toSeq_5008_ = lean_ctor_get(v_toApplicative_5003_, 2);
                v_toSeqLeft_5009_ = lean_ctor_get(v_toApplicative_5003_, 3);
                v_toSeqRight_5010_ = lean_ctor_get(v_toApplicative_5003_, 4);
                v_isSharedCheck_5074_ = (!lean_is_exclusive(v_toApplicative_5003_)) as u8;
                if v_isSharedCheck_5074_ == 0 {
                    v_unused_5075_ = lean_ctor_get(v_toApplicative_5003_, 1);
                    lean_dec(v_unused_5075_);
                    v___x_5012_ = v_toApplicative_5003_;
                    v_isShared_5013_ = v_isSharedCheck_5074_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5010_);
                    lean_inc(v_toSeqLeft_5009_);
                    lean_inc(v_toSeq_5008_);
                    lean_inc(v_toFunctor_5007_);
                    lean_dec(v_toApplicative_5003_);
                    v___x_5012_ = lean_box(0);
                    v_isShared_5013_ = v_isSharedCheck_5074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5014_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4;
                v___f_5015_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5;
                v___f_5016_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6;
                lean_inc_ref(v_toFunctor_5007_);
                v___f_5017_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5017_, 0, v_toFunctor_5007_);
                v___f_5018_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5018_, 0, v_toFunctor_5007_);
                v___x_5019_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5019_, 0, v___f_5017_);
                lean_ctor_set(v___x_5019_, 1, v___f_5018_);
                v___f_5020_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5020_, 0, v_toSeqRight_5010_);
                v___f_5021_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5021_, 0, v_toSeqLeft_5009_);
                v___f_5022_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5022_, 0, v_toSeq_5008_);
                if v_isShared_5013_ == 0 {
                    lean_ctor_set(v___x_5012_, 4, v___f_5020_);
                    lean_ctor_set(v___x_5012_, 3, v___f_5021_);
                    lean_ctor_set(v___x_5012_, 2, v___f_5022_);
                    lean_ctor_set(v___x_5012_, 1, v___f_5015_);
                    lean_ctor_set(v___x_5012_, 0, v___x_5019_);
                    v___x_5024_ = v___x_5012_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5019_);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 1, v___f_5015_);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 2, v___f_5022_);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 3, v___f_5021_);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 4, v___f_5020_);
                    v___x_5024_ = v_reuseFailAlloc_5073_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5006_ == 0 {
                    lean_ctor_set(v___x_5005_, 1, v___f_5016_);
                    lean_ctor_set(v___x_5005_, 0, v___x_5024_);
                    v___x_5026_ = v___x_5005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5024_);
                    lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___f_5016_);
                    v___x_5026_ = v_reuseFailAlloc_5072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5027_ = l_ReaderT_instMonad___redArg(v___x_5026_);
                v___x_5028_ = l_StateRefT_x27_instMonad___redArg(v___x_5027_);
                v___x_5029_ = l_ReaderT_instMonad___redArg(v___x_5028_);
                v___x_5030_ = lean_unsigned_to_nat(0);
                v___x_5031_ = lean_array_get_size(v_params_4976_);
                v___x_5060_ = lean_nat_dec_lt(v___x_5030_, v___x_5031_);
                if v___x_5060_ == 0 {
                    lean_dec_ref(v___x_5029_);
                    state = 5;
                    continue;
                } else {
                    v___f_5061_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17;
                    v___x_5062_ = lean_box(0);
                    v___x_5063_ = lean_nat_dec_le(v___x_5031_, v___x_5031_);
                    if v___x_5063_ == 0 {
                        if v___x_5060_ == 0 {
                            lean_dec_ref(v___x_5029_);
                            state = 5;
                            continue;
                        } else {
                            v___x_5064_ = 0usize;
                            v___x_5065_ = lean_usize_of_nat(v___x_5031_);
                            lean_inc_ref(v_params_4976_);
                            v___x_1277__overap_5066_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_5029_,
                                    v___f_5061_,
                                    v_params_4976_,
                                    v___x_5064_,
                                    v___x_5065_,
                                    v___x_5062_,
                                );
                            lean_inc(v_a_4984_);
                            lean_inc_ref(v_a_4983_);
                            lean_inc(v_a_4982_);
                            lean_inc_ref(v_a_4981_);
                            lean_inc_ref(v_a_4980_);
                            lean_inc(v_a_4979_);
                            lean_inc_ref(v_a_4978_);
                            v___x_5067_ = lean_apply_8(
                                v___x_1277__overap_5066_,
                                v_a_4978_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                lean_box(0),
                            );
                            v___y_5051_ = v___x_5067_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_5068_ = 0usize;
                        v___x_5069_ = lean_usize_of_nat(v___x_5031_);
                        lean_inc_ref(v_params_4976_);
                        v___x_1281__overap_5070_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_5029_,
                                v___f_5061_,
                                v_params_4976_,
                                v___x_5068_,
                                v___x_5069_,
                                v___x_5062_,
                            );
                        lean_inc(v_a_4984_);
                        lean_inc_ref(v_a_4983_);
                        lean_inc(v_a_4982_);
                        lean_inc_ref(v_a_4981_);
                        lean_inc_ref(v_a_4980_);
                        lean_inc(v_a_4979_);
                        lean_inc_ref(v_a_4978_);
                        v___x_5071_ = lean_apply_8(
                            v___x_1281__overap_5070_,
                            v_a_4978_,
                            v_a_4979_,
                            v_a_4980_,
                            v_a_4981_,
                            v_a_4982_,
                            v_a_4983_,
                            v_a_4984_,
                            lean_box(0),
                        );
                        v___y_5051_ = v___x_5071_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_jps_5033_ = lean_ctor_get(v_a_4978_, 0);
                v_vars_5034_ = lean_ctor_get(v_a_4978_, 1);
                v___x_5035_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16;
                v___x_5036_ = lean_nat_dec_lt(v___x_5030_, v___x_5031_);
                if v___x_5036_ == 0 {
                    lean_dec_ref(v_params_4976_);
                    lean_inc(v_a_4984_);
                    lean_inc_ref(v_a_4983_);
                    lean_inc(v_a_4982_);
                    lean_inc_ref(v_a_4981_);
                    lean_inc_ref(v_a_4980_);
                    lean_inc(v_a_4979_);
                    lean_inc_ref(v_a_4978_);
                    v___x_5037_ = lean_apply_8(
                        v_x_4977_,
                        v_a_4978_,
                        v_a_4979_,
                        v_a_4980_,
                        v_a_4981_,
                        v_a_4982_,
                        v_a_4983_,
                        v_a_4984_,
                        lean_box(0),
                    );
                    return v___x_5037_;
                } else {
                    v___x_5038_ = lean_nat_dec_le(v___x_5031_, v___x_5031_);
                    if v___x_5038_ == 0 {
                        if v___x_5036_ == 0 {
                            lean_dec_ref(v_params_4976_);
                            lean_inc(v_a_4984_);
                            lean_inc_ref(v_a_4983_);
                            lean_inc(v_a_4982_);
                            lean_inc_ref(v_a_4981_);
                            lean_inc_ref(v_a_4980_);
                            lean_inc(v_a_4979_);
                            lean_inc_ref(v_a_4978_);
                            v___x_5039_ = lean_apply_8(
                                v_x_4977_,
                                v_a_4978_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                lean_box(0),
                            );
                            return v___x_5039_;
                        } else {
                            v___x_5040_ = 0usize;
                            v___x_5041_ = lean_usize_of_nat(v___x_5031_);
                            lean_inc(v_vars_5034_);
                            v___x_5042_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_5035_,
                                    v___f_5014_,
                                    v_params_4976_,
                                    v___x_5040_,
                                    v___x_5041_,
                                    v_vars_5034_,
                                );
                            lean_inc(v_jps_5033_);
                            v___x_5043_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_5043_, 0, v_jps_5033_);
                            lean_ctor_set(v___x_5043_, 1, v___x_5042_);
                            lean_inc(v_a_4984_);
                            lean_inc_ref(v_a_4983_);
                            lean_inc(v_a_4982_);
                            lean_inc_ref(v_a_4981_);
                            lean_inc_ref(v_a_4980_);
                            lean_inc(v_a_4979_);
                            v___x_5044_ = lean_apply_8(
                                v_x_4977_,
                                v___x_5043_,
                                v_a_4979_,
                                v_a_4980_,
                                v_a_4981_,
                                v_a_4982_,
                                v_a_4983_,
                                v_a_4984_,
                                lean_box(0),
                            );
                            return v___x_5044_;
                        }
                    } else {
                        v___x_5045_ = 0usize;
                        v___x_5046_ = lean_usize_of_nat(v___x_5031_);
                        lean_inc(v_vars_5034_);
                        v___x_5047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_5035_,
                            v___f_5014_,
                            v_params_4976_,
                            v___x_5045_,
                            v___x_5046_,
                            v_vars_5034_,
                        );
                        lean_inc(v_jps_5033_);
                        v___x_5048_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5048_, 0, v_jps_5033_);
                        lean_ctor_set(v___x_5048_, 1, v___x_5047_);
                        lean_inc(v_a_4984_);
                        lean_inc_ref(v_a_4983_);
                        lean_inc(v_a_4982_);
                        lean_inc_ref(v_a_4981_);
                        lean_inc_ref(v_a_4980_);
                        lean_inc(v_a_4979_);
                        v___x_5049_ = lean_apply_8(
                            v_x_4977_,
                            v___x_5048_,
                            v_a_4979_,
                            v_a_4980_,
                            v_a_4981_,
                            v_a_4982_,
                            v_a_4983_,
                            v_a_4984_,
                            lean_box(0),
                        );
                        return v___x_5049_;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v___y_5051_) == 0 {
                    lean_dec_ref_known(v___y_5051_, 1);
                    state = 5;
                    continue;
                } else {
                    lean_dec_ref(v_x_4977_);
                    lean_dec_ref(v_params_4976_);
                    v_a_5052_ = lean_ctor_get(v___y_5051_, 0);
                    v_isSharedCheck_5059_ = (!lean_is_exclusive(v___y_5051_)) as u8;
                    if v_isSharedCheck_5059_ == 0 {
                        v___x_5054_ = v___y_5051_;
                        v_isShared_5055_ = v_isSharedCheck_5059_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5052_);
                        lean_dec(v___y_5051_);
                        v___x_5054_ = lean_box(0);
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
                    v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
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
    mut v_params_5078_: *mut LeanObject,
    mut v_x_5079_: *mut LeanObject,
    mut v_a_5080_: *mut LeanObject,
    mut v_a_5081_: *mut LeanObject,
    mut v_a_5082_: *mut LeanObject,
    mut v_a_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5088_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5086_);
    lean_dec_ref(v_a_5085_);
    lean_dec(v_a_5084_);
    lean_dec_ref(v_a_5083_);
    lean_dec_ref(v_a_5082_);
    lean_dec(v_a_5081_);
    lean_dec_ref(v_a_5080_);
    return v_res_5088_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_withParams(
    mut v_00_u03b1_5089_: *mut LeanObject,
    mut v_params_5090_: *mut LeanObject,
    mut v_x_5091_: *mut LeanObject,
    mut v_a_5092_: *mut LeanObject,
    mut v_a_5093_: *mut LeanObject,
    mut v_a_5094_: *mut LeanObject,
    mut v_a_5095_: *mut LeanObject,
    mut v_a_5096_: *mut LeanObject,
    mut v_a_5097_: *mut LeanObject,
    mut v_a_5098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v_toFunctor_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v___f_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: u8 = 0;
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: usize = 0;
    let mut v___x_5155_: usize = 0;
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: usize = 0;
    let mut v___x_5160_: usize = 0;
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5169_: u8 = 0;
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v___x_5174_: u8 = 0;
    let mut v___f_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: u8 = 0;
    let mut v___x_5178_: usize = 0;
    let mut v___x_5179_: usize = 0;
    let mut v___x_1403__overap_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: usize = 0;
    let mut v___x_5183_: usize = 0;
    let mut v___x_1406__overap_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v_unused_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5190_: u8 = 0;
    let mut v_unused_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5100_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__1,
                );
                v_toApplicative_5101_ = lean_ctor_get(v___x_5100_, 0);
                v_toFunctor_5102_ = lean_ctor_get(v_toApplicative_5101_, 0);
                v_toSeq_5103_ = lean_ctor_get(v_toApplicative_5101_, 2);
                v_toSeqLeft_5104_ = lean_ctor_get(v_toApplicative_5101_, 3);
                v_toSeqRight_5105_ = lean_ctor_get(v_toApplicative_5101_, 4);
                v___f_5106_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__2;
                v___f_5107_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__3;
                lean_inc_ref_n(v_toFunctor_5102_, 2);
                v___f_5108_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5108_, 0, v_toFunctor_5102_);
                v___f_5109_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5109_, 0, v_toFunctor_5102_);
                v___x_5110_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5110_, 0, v___f_5108_);
                lean_ctor_set(v___x_5110_, 1, v___f_5109_);
                lean_inc(v_toSeqRight_5105_);
                v___f_5111_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5111_, 0, v_toSeqRight_5105_);
                lean_inc(v_toSeqLeft_5104_);
                v___f_5112_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5112_, 0, v_toSeqLeft_5104_);
                lean_inc(v_toSeq_5103_);
                v___f_5113_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5113_, 0, v_toSeq_5103_);
                v___x_5114_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5114_, 0, v___x_5110_);
                lean_ctor_set(v___x_5114_, 1, v___f_5106_);
                lean_ctor_set(v___x_5114_, 2, v___f_5113_);
                lean_ctor_set(v___x_5114_, 3, v___f_5112_);
                lean_ctor_set(v___x_5114_, 4, v___f_5111_);
                v___x_5115_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5115_, 0, v___x_5114_);
                lean_ctor_set(v___x_5115_, 1, v___f_5107_);
                v___x_5116_ = l_StateRefT_x27_instMonad___redArg(v___x_5115_);
                v_toApplicative_5117_ = lean_ctor_get(v___x_5116_, 0);
                v_isSharedCheck_5190_ = (!lean_is_exclusive(v___x_5116_)) as u8;
                if v_isSharedCheck_5190_ == 0 {
                    v_unused_5191_ = lean_ctor_get(v___x_5116_, 1);
                    lean_dec(v_unused_5191_);
                    v___x_5119_ = v___x_5116_;
                    v_isShared_5120_ = v_isSharedCheck_5190_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5117_);
                    lean_dec(v___x_5116_);
                    v___x_5119_ = lean_box(0);
                    v_isShared_5120_ = v_isSharedCheck_5190_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5121_ = lean_ctor_get(v_toApplicative_5117_, 0);
                v_toSeq_5122_ = lean_ctor_get(v_toApplicative_5117_, 2);
                v_toSeqLeft_5123_ = lean_ctor_get(v_toApplicative_5117_, 3);
                v_toSeqRight_5124_ = lean_ctor_get(v_toApplicative_5117_, 4);
                v_isSharedCheck_5188_ = (!lean_is_exclusive(v_toApplicative_5117_)) as u8;
                if v_isSharedCheck_5188_ == 0 {
                    v_unused_5189_ = lean_ctor_get(v_toApplicative_5117_, 1);
                    lean_dec(v_unused_5189_);
                    v___x_5126_ = v_toApplicative_5117_;
                    v_isShared_5127_ = v_isSharedCheck_5188_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5124_);
                    lean_inc(v_toSeqLeft_5123_);
                    lean_inc(v_toSeq_5122_);
                    lean_inc(v_toFunctor_5121_);
                    lean_dec(v_toApplicative_5117_);
                    v___x_5126_ = lean_box(0);
                    v_isShared_5127_ = v_isSharedCheck_5188_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5128_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__4;
                v___f_5129_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__5;
                v___f_5130_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__6;
                lean_inc_ref(v_toFunctor_5121_);
                v___f_5131_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5131_, 0, v_toFunctor_5121_);
                v___f_5132_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5132_, 0, v_toFunctor_5121_);
                v___x_5133_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5133_, 0, v___f_5131_);
                lean_ctor_set(v___x_5133_, 1, v___f_5132_);
                v___f_5134_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5134_, 0, v_toSeqRight_5124_);
                v___f_5135_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5135_, 0, v_toSeqLeft_5123_);
                v___f_5136_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5136_, 0, v_toSeq_5122_);
                if v_isShared_5127_ == 0 {
                    lean_ctor_set(v___x_5126_, 4, v___f_5134_);
                    lean_ctor_set(v___x_5126_, 3, v___f_5135_);
                    lean_ctor_set(v___x_5126_, 2, v___f_5136_);
                    lean_ctor_set(v___x_5126_, 1, v___f_5129_);
                    lean_ctor_set(v___x_5126_, 0, v___x_5133_);
                    v___x_5138_ = v___x_5126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5133_);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 1, v___f_5129_);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 2, v___f_5136_);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 3, v___f_5135_);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 4, v___f_5134_);
                    v___x_5138_ = v_reuseFailAlloc_5187_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5120_ == 0 {
                    lean_ctor_set(v___x_5119_, 1, v___f_5130_);
                    lean_ctor_set(v___x_5119_, 0, v___x_5138_);
                    v___x_5140_ = v___x_5119_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5186_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5138_);
                    lean_ctor_set(v_reuseFailAlloc_5186_, 1, v___f_5130_);
                    v___x_5140_ = v_reuseFailAlloc_5186_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5141_ = l_ReaderT_instMonad___redArg(v___x_5140_);
                v___x_5142_ = l_StateRefT_x27_instMonad___redArg(v___x_5141_);
                v___x_5143_ = l_ReaderT_instMonad___redArg(v___x_5142_);
                v___x_5144_ = lean_unsigned_to_nat(0);
                v___x_5145_ = lean_array_get_size(v_params_5090_);
                v___x_5174_ = lean_nat_dec_lt(v___x_5144_, v___x_5145_);
                if v___x_5174_ == 0 {
                    lean_dec_ref(v___x_5143_);
                    state = 5;
                    continue;
                } else {
                    v___f_5175_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__17;
                    v___x_5176_ = lean_box(0);
                    v___x_5177_ = lean_nat_dec_le(v___x_5145_, v___x_5145_);
                    if v___x_5177_ == 0 {
                        if v___x_5174_ == 0 {
                            lean_dec_ref(v___x_5143_);
                            state = 5;
                            continue;
                        } else {
                            v___x_5178_ = 0usize;
                            v___x_5179_ = lean_usize_of_nat(v___x_5145_);
                            lean_inc_ref(v_params_5090_);
                            v___x_1403__overap_5180_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_5143_,
                                    v___f_5175_,
                                    v_params_5090_,
                                    v___x_5178_,
                                    v___x_5179_,
                                    v___x_5176_,
                                );
                            lean_inc(v_a_5098_);
                            lean_inc_ref(v_a_5097_);
                            lean_inc(v_a_5096_);
                            lean_inc_ref(v_a_5095_);
                            lean_inc_ref(v_a_5094_);
                            lean_inc(v_a_5093_);
                            lean_inc_ref(v_a_5092_);
                            v___x_5181_ = lean_apply_8(
                                v___x_1403__overap_5180_,
                                v_a_5092_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                lean_box(0),
                            );
                            v___y_5165_ = v___x_5181_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_5182_ = 0usize;
                        v___x_5183_ = lean_usize_of_nat(v___x_5145_);
                        lean_inc_ref(v_params_5090_);
                        v___x_1406__overap_5184_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_5143_,
                                v___f_5175_,
                                v_params_5090_,
                                v___x_5182_,
                                v___x_5183_,
                                v___x_5176_,
                            );
                        lean_inc(v_a_5098_);
                        lean_inc_ref(v_a_5097_);
                        lean_inc(v_a_5096_);
                        lean_inc_ref(v_a_5095_);
                        lean_inc_ref(v_a_5094_);
                        lean_inc(v_a_5093_);
                        lean_inc_ref(v_a_5092_);
                        v___x_5185_ = lean_apply_8(
                            v___x_1406__overap_5184_,
                            v_a_5092_,
                            v_a_5093_,
                            v_a_5094_,
                            v_a_5095_,
                            v_a_5096_,
                            v_a_5097_,
                            v_a_5098_,
                            lean_box(0),
                        );
                        v___y_5165_ = v___x_5185_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_jps_5147_ = lean_ctor_get(v_a_5092_, 0);
                v_vars_5148_ = lean_ctor_get(v_a_5092_, 1);
                v___x_5149_ = l_Lean_Compiler_LCNF_Check_Pure_withParams___redArg___closed__16;
                v___x_5150_ = lean_nat_dec_lt(v___x_5144_, v___x_5145_);
                if v___x_5150_ == 0 {
                    lean_dec_ref(v_params_5090_);
                    lean_inc(v_a_5098_);
                    lean_inc_ref(v_a_5097_);
                    lean_inc(v_a_5096_);
                    lean_inc_ref(v_a_5095_);
                    lean_inc_ref(v_a_5094_);
                    lean_inc(v_a_5093_);
                    lean_inc_ref(v_a_5092_);
                    v___x_5151_ = lean_apply_8(
                        v_x_5091_,
                        v_a_5092_,
                        v_a_5093_,
                        v_a_5094_,
                        v_a_5095_,
                        v_a_5096_,
                        v_a_5097_,
                        v_a_5098_,
                        lean_box(0),
                    );
                    return v___x_5151_;
                } else {
                    v___x_5152_ = lean_nat_dec_le(v___x_5145_, v___x_5145_);
                    if v___x_5152_ == 0 {
                        if v___x_5150_ == 0 {
                            lean_dec_ref(v_params_5090_);
                            lean_inc(v_a_5098_);
                            lean_inc_ref(v_a_5097_);
                            lean_inc(v_a_5096_);
                            lean_inc_ref(v_a_5095_);
                            lean_inc_ref(v_a_5094_);
                            lean_inc(v_a_5093_);
                            lean_inc_ref(v_a_5092_);
                            v___x_5153_ = lean_apply_8(
                                v_x_5091_,
                                v_a_5092_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                lean_box(0),
                            );
                            return v___x_5153_;
                        } else {
                            v___x_5154_ = 0usize;
                            v___x_5155_ = lean_usize_of_nat(v___x_5145_);
                            lean_inc(v_vars_5148_);
                            v___x_5156_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_5149_,
                                    v___f_5128_,
                                    v_params_5090_,
                                    v___x_5154_,
                                    v___x_5155_,
                                    v_vars_5148_,
                                );
                            lean_inc(v_jps_5147_);
                            v___x_5157_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_5157_, 0, v_jps_5147_);
                            lean_ctor_set(v___x_5157_, 1, v___x_5156_);
                            lean_inc(v_a_5098_);
                            lean_inc_ref(v_a_5097_);
                            lean_inc(v_a_5096_);
                            lean_inc_ref(v_a_5095_);
                            lean_inc_ref(v_a_5094_);
                            lean_inc(v_a_5093_);
                            v___x_5158_ = lean_apply_8(
                                v_x_5091_,
                                v___x_5157_,
                                v_a_5093_,
                                v_a_5094_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                lean_box(0),
                            );
                            return v___x_5158_;
                        }
                    } else {
                        v___x_5159_ = 0usize;
                        v___x_5160_ = lean_usize_of_nat(v___x_5145_);
                        lean_inc(v_vars_5148_);
                        v___x_5161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_5149_,
                            v___f_5128_,
                            v_params_5090_,
                            v___x_5159_,
                            v___x_5160_,
                            v_vars_5148_,
                        );
                        lean_inc(v_jps_5147_);
                        v___x_5162_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5162_, 0, v_jps_5147_);
                        lean_ctor_set(v___x_5162_, 1, v___x_5161_);
                        lean_inc(v_a_5098_);
                        lean_inc_ref(v_a_5097_);
                        lean_inc(v_a_5096_);
                        lean_inc_ref(v_a_5095_);
                        lean_inc_ref(v_a_5094_);
                        lean_inc(v_a_5093_);
                        v___x_5163_ = lean_apply_8(
                            v_x_5091_,
                            v___x_5162_,
                            v_a_5093_,
                            v_a_5094_,
                            v_a_5095_,
                            v_a_5096_,
                            v_a_5097_,
                            v_a_5098_,
                            lean_box(0),
                        );
                        return v___x_5163_;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v___y_5165_) == 0 {
                    lean_dec_ref_known(v___y_5165_, 1);
                    state = 5;
                    continue;
                } else {
                    lean_dec_ref(v_x_5091_);
                    lean_dec_ref(v_params_5090_);
                    v_a_5166_ = lean_ctor_get(v___y_5165_, 0);
                    v_isSharedCheck_5173_ = (!lean_is_exclusive(v___y_5165_)) as u8;
                    if v_isSharedCheck_5173_ == 0 {
                        v___x_5168_ = v___y_5165_;
                        v_isShared_5169_ = v_isSharedCheck_5173_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5166_);
                        lean_dec(v___y_5165_);
                        v___x_5168_ = lean_box(0);
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
                    v_reuseFailAlloc_5172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
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
    mut v_00_u03b1_5192_: *mut LeanObject,
    mut v_params_5193_: *mut LeanObject,
    mut v_x_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
    mut v_a_5196_: *mut LeanObject,
    mut v_a_5197_: *mut LeanObject,
    mut v_a_5198_: *mut LeanObject,
    mut v_a_5199_: *mut LeanObject,
    mut v_a_5200_: *mut LeanObject,
    mut v_a_5201_: *mut LeanObject,
    mut v_a_5202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5203_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5201_);
    lean_dec_ref(v_a_5200_);
    lean_dec(v_a_5199_);
    lean_dec_ref(v_a_5198_);
    lean_dec_ref(v_a_5197_);
    lean_dec(v_a_5196_);
    lean_dec_ref(v_a_5195_);
    return v_res_5203_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(
    mut v_ref_5204_: *mut LeanObject,
    mut v_msg_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5223_: u8 = 0;
    let mut v_cancelTk_x3f_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5225_: u8 = 0;
    let mut v_inheritedTraceOptions_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_5211_ = lean_ctor_get(v___y_5208_, 0);
    v_fileMap_5212_ = lean_ctor_get(v___y_5208_, 1);
    v_options_5213_ = lean_ctor_get(v___y_5208_, 2);
    v_currRecDepth_5214_ = lean_ctor_get(v___y_5208_, 3);
    v_maxRecDepth_5215_ = lean_ctor_get(v___y_5208_, 4);
    v_ref_5216_ = lean_ctor_get(v___y_5208_, 5);
    v_currNamespace_5217_ = lean_ctor_get(v___y_5208_, 6);
    v_openDecls_5218_ = lean_ctor_get(v___y_5208_, 7);
    v_initHeartbeats_5219_ = lean_ctor_get(v___y_5208_, 8);
    v_maxHeartbeats_5220_ = lean_ctor_get(v___y_5208_, 9);
    v_quotContext_5221_ = lean_ctor_get(v___y_5208_, 10);
    v_currMacroScope_5222_ = lean_ctor_get(v___y_5208_, 11);
    v_diag_5223_ = lean_ctor_get_uint8(
        v___y_5208_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5224_ = lean_ctor_get(v___y_5208_, 12);
    v_suppressElabErrors_5225_ = lean_ctor_get_uint8(
        v___y_5208_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5226_ = lean_ctor_get(v___y_5208_, 13);
    v_ref_5227_ = l_Lean_replaceRef(v_ref_5204_, v_ref_5216_);
    lean_inc_ref(v_inheritedTraceOptions_5226_);
    lean_inc(v_cancelTk_x3f_5224_);
    lean_inc(v_currMacroScope_5222_);
    lean_inc(v_quotContext_5221_);
    lean_inc(v_maxHeartbeats_5220_);
    lean_inc(v_initHeartbeats_5219_);
    lean_inc(v_openDecls_5218_);
    lean_inc(v_currNamespace_5217_);
    lean_inc(v_maxRecDepth_5215_);
    lean_inc(v_currRecDepth_5214_);
    lean_inc_ref(v_options_5213_);
    lean_inc_ref(v_fileMap_5212_);
    lean_inc_ref(v_fileName_5211_);
    v___x_5228_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_5228_, 0, v_fileName_5211_);
    lean_ctor_set(v___x_5228_, 1, v_fileMap_5212_);
    lean_ctor_set(v___x_5228_, 2, v_options_5213_);
    lean_ctor_set(v___x_5228_, 3, v_currRecDepth_5214_);
    lean_ctor_set(v___x_5228_, 4, v_maxRecDepth_5215_);
    lean_ctor_set(v___x_5228_, 5, v_ref_5227_);
    lean_ctor_set(v___x_5228_, 6, v_currNamespace_5217_);
    lean_ctor_set(v___x_5228_, 7, v_openDecls_5218_);
    lean_ctor_set(v___x_5228_, 8, v_initHeartbeats_5219_);
    lean_ctor_set(v___x_5228_, 9, v_maxHeartbeats_5220_);
    lean_ctor_set(v___x_5228_, 10, v_quotContext_5221_);
    lean_ctor_set(v___x_5228_, 11, v_currMacroScope_5222_);
    lean_ctor_set(v___x_5228_, 12, v_cancelTk_x3f_5224_);
    lean_ctor_set(v___x_5228_, 13, v_inheritedTraceOptions_5226_);
    lean_ctor_set_uint8(
        v___x_5228_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_5223_,
    );
    lean_ctor_set_uint8(
        v___x_5228_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
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
    lean_dec_ref_known(v___x_5228_, 14);
    return v___x_5229_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg___boxed(
    mut v_ref_5230_: *mut LeanObject,
    mut v_msg_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5237_: *mut LeanObject = core::ptr::null_mut();
    v_res_5237_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_5230_, v_msg_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
    lean_dec(v___y_5235_);
    lean_dec_ref(v___y_5234_);
    lean_dec(v___y_5233_);
    lean_dec_ref(v___y_5232_);
    lean_dec(v_ref_5230_);
    return v_res_5237_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(
    mut v_msg_5238_: *mut LeanObject,
    mut v_declHint_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: u8 = 0;
    let mut v_isExporting_5245_: u8 = 0;
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u8 = 0;
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: u8 = 0;
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5242_ = lean_st_ref_get(v___y_5240_);
                v_env_5243_ = lean_ctor_get(v___x_5242_, 0);
                lean_inc_ref(v_env_5243_);
                lean_dec(v___x_5242_);
                v___x_5244_ = l_Lean_Name_isAnonymous(v_declHint_5239_);
                if v___x_5244_ == 0 {
                    v_isExporting_5245_ = lean_ctor_get_uint8(
                        v_env_5243_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5245_ == 0 {
                        lean_dec_ref(v_env_5243_);
                        lean_dec(v_declHint_5239_);
                        v___x_5246_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5246_, 0, v_msg_5238_);
                        return v___x_5246_;
                    } else {
                        lean_inc_ref(v_env_5243_);
                        v___x_5247_ = l_Lean_Environment_setExporting(v_env_5243_, v___x_5244_);
                        lean_inc(v_declHint_5239_);
                        lean_inc_ref(v___x_5247_);
                        v___x_5248_ = l_Lean_Environment_contains(
                            v___x_5247_,
                            v_declHint_5239_,
                            v_isExporting_5245_,
                        );
                        if v___x_5248_ == 0 {
                            lean_dec_ref(v___x_5247_);
                            lean_dec_ref(v_env_5243_);
                            lean_dec(v_declHint_5239_);
                            v___x_5249_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5249_, 0, v_msg_5238_);
                            return v___x_5249_;
                        } else {
                            v___x_5250_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg___closed__2);
                            v___x_5251_ = lean_unsigned_to_nat(32);
                            v___x_5252_ = lean_mk_empty_array_with_capacity(v___x_5251_);
                            lean_dec_ref(v___x_5252_);
                            v___x_5253_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_5254_ = l_Lean_Options_empty;
                            v___x_5255_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_5255_, 0, v___x_5247_);
                            lean_ctor_set(v___x_5255_, 1, v___x_5250_);
                            lean_ctor_set(v___x_5255_, 2, v___x_5253_);
                            lean_ctor_set(v___x_5255_, 3, v___x_5254_);
                            lean_inc(v_declHint_5239_);
                            v___x_5256_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5239_, v___x_5244_);
                            v_c_5257_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_5257_, 0, v___x_5255_);
                            lean_ctor_set(v_c_5257_, 1, v___x_5256_);
                            v___x_5258_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5243_,
                                v_declHint_5239_,
                            );
                            if lean_obj_tag(v___x_5258_) == 0 {
                                lean_dec_ref(v_env_5243_);
                                lean_dec(v_declHint_5239_);
                                v___x_5259_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_5260_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5260_, 0, v___x_5259_);
                                lean_ctor_set(v___x_5260_, 1, v_c_5257_);
                                v___x_5261_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_5262_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5262_, 0, v___x_5260_);
                                lean_ctor_set(v___x_5262_, 1, v___x_5261_);
                                v___x_5263_ = l_Lean_MessageData_note(v___x_5262_);
                                v___x_5264_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5264_, 0, v_msg_5238_);
                                lean_ctor_set(v___x_5264_, 1, v___x_5263_);
                                v___x_5265_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_5265_, 0, v___x_5264_);
                                return v___x_5265_;
                            } else {
                                v_val_5266_ = lean_ctor_get(v___x_5258_, 0);
                                v_isSharedCheck_5301_ = (!lean_is_exclusive(v___x_5258_)) as u8;
                                if v_isSharedCheck_5301_ == 0 {
                                    v___x_5268_ = v___x_5258_;
                                    v_isShared_5269_ = v_isSharedCheck_5301_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_5266_);
                                    lean_dec(v___x_5258_);
                                    v___x_5268_ = lean_box(0);
                                    v_isShared_5269_ = v_isSharedCheck_5301_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_5243_);
                    lean_dec(v_declHint_5239_);
                    v___x_5302_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5302_, 0, v_msg_5238_);
                    return v___x_5302_;
                }
            }
            1 => {
                v___x_5270_ = lean_box(0);
                v___x_5271_ = l_Lean_Environment_header(v_env_5243_);
                lean_dec_ref(v_env_5243_);
                v___x_5272_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5271_);
                v_mod_5273_ = lean_array_get(v___x_5270_, v___x_5272_, v_val_5266_);
                lean_dec(v_val_5266_);
                lean_dec_ref(v___x_5272_);
                v___x_5274_ = l_Lean_isPrivateName(v_declHint_5239_);
                lean_dec(v_declHint_5239_);
                if v___x_5274_ == 0 {
                    v___x_5275_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_5276_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5276_, 0, v___x_5275_);
                    lean_ctor_set(v___x_5276_, 1, v_c_5257_);
                    v___x_5277_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_5278_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5278_, 0, v___x_5276_);
                    lean_ctor_set(v___x_5278_, 1, v___x_5277_);
                    v___x_5279_ = l_Lean_MessageData_ofName(v_mod_5273_);
                    v___x_5280_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5280_, 0, v___x_5278_);
                    lean_ctor_set(v___x_5280_, 1, v___x_5279_);
                    v___x_5281_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_5282_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5282_, 0, v___x_5280_);
                    lean_ctor_set(v___x_5282_, 1, v___x_5281_);
                    v___x_5283_ = l_Lean_MessageData_note(v___x_5282_);
                    v___x_5284_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5284_, 0, v_msg_5238_);
                    lean_ctor_set(v___x_5284_, 1, v___x_5283_);
                    if v_isShared_5269_ == 0 {
                        lean_ctor_set_tag(v___x_5268_, 0);
                        lean_ctor_set(v___x_5268_, 0, v___x_5284_);
                        v___x_5286_ = v___x_5268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5284_);
                        v___x_5286_ = v_reuseFailAlloc_5287_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5288_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_5289_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5289_, 0, v___x_5288_);
                    lean_ctor_set(v___x_5289_, 1, v_c_5257_);
                    v___x_5290_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_5291_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5291_, 0, v___x_5289_);
                    lean_ctor_set(v___x_5291_, 1, v___x_5290_);
                    v___x_5292_ = l_Lean_MessageData_ofName(v_mod_5273_);
                    v___x_5293_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5293_, 0, v___x_5291_);
                    lean_ctor_set(v___x_5293_, 1, v___x_5292_);
                    v___x_5294_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_5295_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5295_, 0, v___x_5293_);
                    lean_ctor_set(v___x_5295_, 1, v___x_5294_);
                    v___x_5296_ = l_Lean_MessageData_note(v___x_5295_);
                    v___x_5297_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5297_, 0, v_msg_5238_);
                    lean_ctor_set(v___x_5297_, 1, v___x_5296_);
                    if v_isShared_5269_ == 0 {
                        lean_ctor_set_tag(v___x_5268_, 0);
                        lean_ctor_set(v___x_5268_, 0, v___x_5297_);
                        v___x_5299_ = v___x_5268_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5300_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5300_, 0, v___x_5297_);
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
    mut v_msg_5303_: *mut LeanObject,
    mut v_declHint_5304_: *mut LeanObject,
    mut v___y_5305_: *mut LeanObject,
    mut v___y_5306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5307_: *mut LeanObject = core::ptr::null_mut();
    v_res_5307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_5303_, v_declHint_5304_, v___y_5305_);
    lean_dec(v___y_5305_);
    return v_res_5307_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(
    mut v_msg_5308_: *mut LeanObject,
    mut v_declHint_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
    mut v___y_5316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5318_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_5308_, v_declHint_5309_, v___y_5316_);
                v_a_5319_ = lean_ctor_get(v___x_5318_, 0);
                v_isSharedCheck_5328_ = (!lean_is_exclusive(v___x_5318_)) as u8;
                if v_isSharedCheck_5328_ == 0 {
                    v___x_5321_ = v___x_5318_;
                    v_isShared_5322_ = v_isSharedCheck_5328_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5319_);
                    lean_dec(v___x_5318_);
                    v___x_5321_ = lean_box(0);
                    v_isShared_5322_ = v_isSharedCheck_5328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5323_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5324_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_5324_, 0, v___x_5323_);
                lean_ctor_set(v___x_5324_, 1, v_a_5319_);
                if v_isShared_5322_ == 0 {
                    lean_ctor_set(v___x_5321_, 0, v___x_5324_);
                    v___x_5326_ = v___x_5321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
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
    mut v_msg_5329_: *mut LeanObject,
    mut v_declHint_5330_: *mut LeanObject,
    mut v___y_5331_: *mut LeanObject,
    mut v___y_5332_: *mut LeanObject,
    mut v___y_5333_: *mut LeanObject,
    mut v___y_5334_: *mut LeanObject,
    mut v___y_5335_: *mut LeanObject,
    mut v___y_5336_: *mut LeanObject,
    mut v___y_5337_: *mut LeanObject,
    mut v___y_5338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5339_: *mut LeanObject = core::ptr::null_mut();
    v_res_5339_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(v_msg_5329_, v_declHint_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
    lean_dec(v___y_5337_);
    lean_dec_ref(v___y_5336_);
    lean_dec(v___y_5335_);
    lean_dec_ref(v___y_5334_);
    lean_dec_ref(v___y_5333_);
    lean_dec(v___y_5332_);
    lean_dec_ref(v___y_5331_);
    return v_res_5339_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(
    mut v_ref_5340_: *mut LeanObject,
    mut v_msg_5341_: *mut LeanObject,
    mut v_declHint_5342_: *mut LeanObject,
    mut v___y_5343_: *mut LeanObject,
    mut v___y_5344_: *mut LeanObject,
    mut v___y_5345_: *mut LeanObject,
    mut v___y_5346_: *mut LeanObject,
    mut v___y_5347_: *mut LeanObject,
    mut v___y_5348_: *mut LeanObject,
    mut v___y_5349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    v___x_5351_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9(v_msg_5341_, v_declHint_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
    v_a_5352_ = lean_ctor_get(v___x_5351_, 0);
    lean_inc(v_a_5352_);
    lean_dec_ref(v___x_5351_);
    v___x_5353_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_5340_, v_a_5352_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
    return v___x_5353_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_ref_5354_: *mut LeanObject,
    mut v_msg_5355_: *mut LeanObject,
    mut v_declHint_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
    mut v___y_5360_: *mut LeanObject,
    mut v___y_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
    mut v___y_5364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5365_: *mut LeanObject = core::ptr::null_mut();
    v_res_5365_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_5354_, v_msg_5355_, v_declHint_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
    lean_dec(v___y_5363_);
    lean_dec_ref(v___y_5362_);
    lean_dec(v___y_5361_);
    lean_dec_ref(v___y_5360_);
    lean_dec_ref(v___y_5359_);
    lean_dec(v___y_5358_);
    lean_dec_ref(v___y_5357_);
    lean_dec(v_ref_5354_);
    return v_res_5365_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(
    mut v_ref_5366_: *mut LeanObject,
    mut v_constName_5367_: *mut LeanObject,
    mut v___y_5368_: *mut LeanObject,
    mut v___y_5369_: *mut LeanObject,
    mut v___y_5370_: *mut LeanObject,
    mut v___y_5371_: *mut LeanObject,
    mut v___y_5372_: *mut LeanObject,
    mut v___y_5373_: *mut LeanObject,
    mut v___y_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    v___x_5376_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_5377_ = 0;
    lean_inc(v_constName_5367_);
    v___x_5378_ = l_Lean_MessageData_ofConstName(v_constName_5367_, v___x_5377_);
    v___x_5379_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5379_, 0, v___x_5376_);
    lean_ctor_set(v___x_5379_, 1, v___x_5378_);
    v___x_5380_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_5381_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5381_, 0, v___x_5379_);
    lean_ctor_set(v___x_5381_, 1, v___x_5380_);
    v___x_5382_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_5366_, v___x_5381_, v_constName_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
    return v___x_5382_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg___boxed(
    mut v_ref_5383_: *mut LeanObject,
    mut v_constName_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
    mut v___y_5386_: *mut LeanObject,
    mut v___y_5387_: *mut LeanObject,
    mut v___y_5388_: *mut LeanObject,
    mut v___y_5389_: *mut LeanObject,
    mut v___y_5390_: *mut LeanObject,
    mut v___y_5391_: *mut LeanObject,
    mut v___y_5392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5393_: *mut LeanObject = core::ptr::null_mut();
    v_res_5393_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_5383_, v_constName_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
    lean_dec(v___y_5391_);
    lean_dec_ref(v___y_5390_);
    lean_dec(v___y_5389_);
    lean_dec_ref(v___y_5388_);
    lean_dec_ref(v___y_5387_);
    lean_dec(v___y_5386_);
    lean_dec_ref(v___y_5385_);
    lean_dec(v_ref_5383_);
    return v_res_5393_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(
    mut v_constName_5394_: *mut LeanObject,
    mut v___y_5395_: *mut LeanObject,
    mut v___y_5396_: *mut LeanObject,
    mut v___y_5397_: *mut LeanObject,
    mut v___y_5398_: *mut LeanObject,
    mut v___y_5399_: *mut LeanObject,
    mut v___y_5400_: *mut LeanObject,
    mut v___y_5401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5403_ = lean_ctor_get(v___y_5400_, 5);
    v___x_5404_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_5403_, v_constName_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
    return v___x_5404_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg___boxed(
    mut v_constName_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
    mut v___y_5409_: *mut LeanObject,
    mut v___y_5410_: *mut LeanObject,
    mut v___y_5411_: *mut LeanObject,
    mut v___y_5412_: *mut LeanObject,
    mut v___y_5413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5414_: *mut LeanObject = core::ptr::null_mut();
    v_res_5414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_);
    lean_dec(v___y_5412_);
    lean_dec_ref(v___y_5411_);
    lean_dec(v___y_5410_);
    lean_dec_ref(v___y_5409_);
    lean_dec_ref(v___y_5408_);
    lean_dec(v___y_5407_);
    lean_dec_ref(v___y_5406_);
    return v_res_5414_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4(
    mut v_constName_5415_: *mut LeanObject,
    mut v___y_5416_: *mut LeanObject,
    mut v___y_5417_: *mut LeanObject,
    mut v___y_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
    mut v___y_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: u8 = 0;
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5424_ = lean_st_ref_get(v___y_5422_);
                v_env_5425_ = lean_ctor_get(v___x_5424_, 0);
                lean_inc_ref(v_env_5425_);
                lean_dec(v___x_5424_);
                v___x_5426_ = 0;
                lean_inc(v_constName_5415_);
                v___x_5427_ =
                    l_Lean_Environment_find_x3f(v_env_5425_, v_constName_5415_, v___x_5426_);
                if lean_obj_tag(v___x_5427_) == 0 {
                    v___x_5428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
                    return v___x_5428_;
                } else {
                    lean_dec(v_constName_5415_);
                    v_val_5429_ = lean_ctor_get(v___x_5427_, 0);
                    v_isSharedCheck_5436_ = (!lean_is_exclusive(v___x_5427_)) as u8;
                    if v_isSharedCheck_5436_ == 0 {
                        v___x_5431_ = v___x_5427_;
                        v_isShared_5432_ = v_isSharedCheck_5436_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5429_);
                        lean_dec(v___x_5427_);
                        v___x_5431_ = lean_box(0);
                        v_isShared_5432_ = v_isSharedCheck_5436_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5432_ == 0 {
                    lean_ctor_set_tag(v___x_5431_, 0);
                    v___x_5434_ = v___x_5431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_val_5429_);
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
    mut v_constName_5437_: *mut LeanObject,
    mut v___y_5438_: *mut LeanObject,
    mut v___y_5439_: *mut LeanObject,
    mut v___y_5440_: *mut LeanObject,
    mut v___y_5441_: *mut LeanObject,
    mut v___y_5442_: *mut LeanObject,
    mut v___y_5443_: *mut LeanObject,
    mut v___y_5444_: *mut LeanObject,
    mut v___y_5445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5446_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5444_);
    lean_dec_ref(v___y_5443_);
    lean_dec(v___y_5442_);
    lean_dec_ref(v___y_5441_);
    lean_dec_ref(v___y_5440_);
    lean_dec(v___y_5439_);
    lean_dec_ref(v___y_5438_);
    return v_res_5446_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(
    mut v_as_5447_: *mut LeanObject,
    mut v_i_5448_: usize,
    mut v_stop_5449_: usize,
    mut v_b_5450_: *mut LeanObject,
    mut v___y_5451_: *mut LeanObject,
    mut v___y_5452_: *mut LeanObject,
    mut v___y_5453_: *mut LeanObject,
    mut v___y_5454_: *mut LeanObject,
    mut v___y_5455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5457_: u8 = 0;
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: usize = 0;
    let mut v___x_5463_: usize = 0;
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5457_ = lean_usize_dec_eq(v_i_5448_, v_stop_5449_);
                if v___x_5457_ == 0 {
                    v___x_5458_ = lean_array_uget_borrowed(v_as_5447_, v_i_5448_);
                    v_fvarId_5459_ = lean_ctor_get(v___x_5458_, 0);
                    lean_inc(v_fvarId_5459_);
                    v___x_5460_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_5459_,
                        v___y_5451_,
                        v___y_5452_,
                        v___y_5453_,
                        v___y_5454_,
                        v___y_5455_,
                    );
                    if lean_obj_tag(v___x_5460_) == 0 {
                        v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
                        lean_inc(v_a_5461_);
                        lean_dec_ref_known(v___x_5460_, 1);
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
                    v___x_5465_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5465_, 0, v_b_5450_);
                    return v___x_5465_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg___boxed(
    mut v_as_5466_: *mut LeanObject,
    mut v_i_5467_: *mut LeanObject,
    mut v_stop_5468_: *mut LeanObject,
    mut v_b_5469_: *mut LeanObject,
    mut v___y_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
    mut v___y_5472_: *mut LeanObject,
    mut v___y_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5476_: usize = 0;
    let mut v_stop_boxed_5477_: usize = 0;
    let mut v_res_5478_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5476_ = lean_unbox_usize(v_i_5467_);
    lean_dec(v_i_5467_);
    v_stop_boxed_5477_ = lean_unbox_usize(v_stop_5468_);
    lean_dec(v_stop_5468_);
    v_res_5478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_as_5466_, v_i_boxed_5476_, v_stop_boxed_5477_, v_b_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_);
    lean_dec(v___y_5474_);
    lean_dec_ref(v___y_5473_);
    lean_dec(v___y_5472_);
    lean_dec_ref(v___y_5471_);
    lean_dec(v___y_5470_);
    lean_dec_ref(v_as_5466_);
    return v_res_5478_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(
    mut v_as_5479_: *mut LeanObject,
    mut v_i_5480_: usize,
    mut v_stop_5481_: usize,
    mut v_b_5482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: usize = 0;
    let mut v___x_5488_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5483_ = lean_usize_dec_eq(v_i_5480_, v_stop_5481_);
                if v___x_5483_ == 0 {
                    v___x_5484_ = lean_array_uget_borrowed(v_as_5479_, v_i_5480_);
                    v_fvarId_5485_ = lean_ctor_get(v___x_5484_, 0);
                    lean_inc(v_fvarId_5485_);
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
    mut v_as_5490_: *mut LeanObject,
    mut v_i_5491_: *mut LeanObject,
    mut v_stop_5492_: *mut LeanObject,
    mut v_b_5493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5494_: usize = 0;
    let mut v_stop_boxed_5495_: usize = 0;
    let mut v_res_5496_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5494_ = lean_unbox_usize(v_i_5491_);
    lean_dec(v_i_5491_);
    v_stop_boxed_5495_ = lean_unbox_usize(v_stop_5492_);
    lean_dec(v_stop_5492_);
    v_res_5496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_as_5490_, v_i_boxed_5494_, v_stop_boxed_5495_, v_b_5493_);
    lean_dec_ref(v_as_5490_);
    return v_res_5496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore(
    mut v_declName_5498_: *mut LeanObject,
    mut v_params_5499_: *mut LeanObject,
    mut v_type_5500_: *mut LeanObject,
    mut v_value_5501_: *mut LeanObject,
    mut v_a_5502_: *mut LeanObject,
    mut v_a_5503_: *mut LeanObject,
    mut v_a_5504_: *mut LeanObject,
    mut v_a_5505_: *mut LeanObject,
    mut v_a_5506_: *mut LeanObject,
    mut v_a_5507_: *mut LeanObject,
    mut v_a_5508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5520_: u8 = 0;
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: u8 = 0;
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5536_: u8 = 0;
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5554_: u8 = 0;
    let mut v_a_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5558_: u8 = 0;
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5562_: u8 = 0;
    let mut v_a_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5570_: u8 = 0;
    let mut v_a_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_a_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: u8 = 0;
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5610_: u8 = 0;
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: u8 = 0;
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5627_: u8 = 0;
    let mut v_a_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5643_: u8 = 0;
    let mut v_a_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5647_: u8 = 0;
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_a_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5656_: u8 = 0;
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: usize = 0;
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: usize = 0;
    let mut v___x_5676_: usize = 0;
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: u8 = 0;
    let mut v___x_5683_: u8 = 0;
    let mut v___x_5684_: usize = 0;
    let mut v___x_5685_: usize = 0;
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: usize = 0;
    let mut v___x_5688_: usize = 0;
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5588_) == 0 {
                    lean_dec_ref_known(v___x_5588_, 1);
                    v___x_5589_ = lean_box(0);
                    v___x_5661_ = lean_unsigned_to_nat(0);
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
                    lean_dec_ref(v_value_5501_);
                    lean_dec_ref(v_type_5500_);
                    lean_dec_ref(v_params_5499_);
                    lean_dec(v_declName_5498_);
                    return v___x_5588_;
                }
            }
            1 => {
                v___x_5516_ = l_Lean_Compiler_LCNF_Check_Pure_checkTypes___redArg(v___y_5512_);
                if lean_obj_tag(v___x_5516_) == 0 {
                    v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
                    v_isSharedCheck_5579_ = (!lean_is_exclusive(v___x_5516_)) as u8;
                    if v_isSharedCheck_5579_ == 0 {
                        v___x_5519_ = v___x_5516_;
                        v_isShared_5520_ = v_isSharedCheck_5579_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5517_);
                        lean_dec(v___x_5516_);
                        v___x_5519_ = lean_box(0);
                        v_isShared_5520_ = v_isSharedCheck_5579_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_value_5501_);
                    lean_dec_ref(v_type_5500_);
                    lean_dec_ref(v_params_5499_);
                    lean_dec(v_declName_5498_);
                    v_a_5580_ = lean_ctor_get(v___x_5516_, 0);
                    v_isSharedCheck_5587_ = (!lean_is_exclusive(v___x_5516_)) as u8;
                    if v_isSharedCheck_5587_ == 0 {
                        v___x_5582_ = v___x_5516_;
                        v_isShared_5583_ = v_isSharedCheck_5587_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_5580_);
                        lean_dec(v___x_5516_);
                        v___x_5582_ = lean_box(0);
                        v_isShared_5583_ = v_isSharedCheck_5587_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5521_ = (lean_unbox(v_a_5517_) as u8);
                lean_dec(v_a_5517_);
                if v___x_5521_ == 0 {
                    lean_dec_ref(v_value_5501_);
                    lean_dec_ref(v_type_5500_);
                    lean_dec_ref(v_params_5499_);
                    lean_dec(v_declName_5498_);
                    v___x_5522_ = lean_box(0);
                    if v_isShared_5520_ == 0 {
                        lean_ctor_set(v___x_5519_, 0, v___x_5522_);
                        v___x_5524_ = v___x_5519_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5525_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5525_, 0, v___x_5522_);
                        v___x_5524_ = v_reuseFailAlloc_5525_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5519_);
                    v___x_5526_ = 0;
                    v___x_5527_ = l_Lean_Compiler_LCNF_Code_inferType(
                        v___x_5526_,
                        v_value_5501_,
                        v___y_5512_,
                        v___y_5513_,
                        v___y_5514_,
                        v___y_5515_,
                    );
                    if lean_obj_tag(v___x_5527_) == 0 {
                        v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
                        lean_inc(v_a_5528_);
                        lean_dec_ref_known(v___x_5527_, 1);
                        v___x_5529_ = l_Lean_Compiler_LCNF_mkForallParams(
                            v___x_5526_,
                            v_params_5499_,
                            v_a_5528_,
                            v___y_5512_,
                            v___y_5513_,
                            v___y_5514_,
                            v___y_5515_,
                        );
                        lean_dec(v_a_5528_);
                        if lean_obj_tag(v___x_5529_) == 0 {
                            v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
                            lean_inc_n(v_a_5530_, 2);
                            lean_dec_ref_known(v___x_5529_, 1);
                            lean_inc_ref(v_type_5500_);
                            v___x_5531_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_type_5500_,
                                v_a_5530_,
                                v___y_5511_,
                                v___y_5512_,
                                v___y_5513_,
                                v___y_5514_,
                                v___y_5515_,
                            );
                            if lean_obj_tag(v___x_5531_) == 0 {
                                v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
                                v_isSharedCheck_5554_ = (!lean_is_exclusive(v___x_5531_)) as u8;
                                if v_isSharedCheck_5554_ == 0 {
                                    v___x_5534_ = v___x_5531_;
                                    v_isShared_5535_ = v_isSharedCheck_5554_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_5532_);
                                    lean_dec(v___x_5531_);
                                    v___x_5534_ = lean_box(0);
                                    v_isShared_5535_ = v_isSharedCheck_5554_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5530_);
                                lean_dec_ref(v_type_5500_);
                                lean_dec(v_declName_5498_);
                                v_a_5555_ = lean_ctor_get(v___x_5531_, 0);
                                v_isSharedCheck_5562_ = (!lean_is_exclusive(v___x_5531_)) as u8;
                                if v_isSharedCheck_5562_ == 0 {
                                    v___x_5557_ = v___x_5531_;
                                    v_isShared_5558_ = v_isSharedCheck_5562_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_5555_);
                                    lean_dec(v___x_5531_);
                                    v___x_5557_ = lean_box(0);
                                    v_isShared_5558_ = v_isSharedCheck_5562_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_type_5500_);
                            lean_dec(v_declName_5498_);
                            v_a_5563_ = lean_ctor_get(v___x_5529_, 0);
                            v_isSharedCheck_5570_ = (!lean_is_exclusive(v___x_5529_)) as u8;
                            if v_isSharedCheck_5570_ == 0 {
                                v___x_5565_ = v___x_5529_;
                                v_isShared_5566_ = v_isSharedCheck_5570_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_5563_);
                                lean_dec(v___x_5529_);
                                v___x_5565_ = lean_box(0);
                                v_isShared_5566_ = v_isSharedCheck_5570_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_type_5500_);
                        lean_dec_ref(v_params_5499_);
                        lean_dec(v_declName_5498_);
                        v_a_5571_ = lean_ctor_get(v___x_5527_, 0);
                        v_isSharedCheck_5578_ = (!lean_is_exclusive(v___x_5527_)) as u8;
                        if v_isSharedCheck_5578_ == 0 {
                            v___x_5573_ = v___x_5527_;
                            v_isShared_5574_ = v_isSharedCheck_5578_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_5571_);
                            lean_dec(v___x_5527_);
                            v___x_5573_ = lean_box(0);
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
                v___x_5536_ = (lean_unbox(v_a_5532_) as u8);
                if v___x_5536_ == 0 {
                    lean_del_object(v___x_5534_);
                    v___x_5537_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5,
                    );
                    v___x_5538_ = (lean_unbox(v_a_5532_) as u8);
                    lean_dec(v_a_5532_);
                    v___x_5539_ = l_Lean_MessageData_ofConstName(v_declName_5498_, v___x_5538_);
                    v___x_5540_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5540_, 0, v___x_5537_);
                    lean_ctor_set(v___x_5540_, 1, v___x_5539_);
                    v___x_5541_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7,
                    );
                    v___x_5542_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5542_, 0, v___x_5540_);
                    lean_ctor_set(v___x_5542_, 1, v___x_5541_);
                    v___x_5543_ = l_Lean_indentExpr(v_a_5530_);
                    v___x_5544_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5544_, 0, v___x_5542_);
                    lean_ctor_set(v___x_5544_, 1, v___x_5543_);
                    v___x_5545_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                    v___x_5546_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5546_, 0, v___x_5544_);
                    lean_ctor_set(v___x_5546_, 1, v___x_5545_);
                    v___x_5547_ = l_Lean_indentExpr(v_type_5500_);
                    v___x_5548_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5548_, 0, v___x_5546_);
                    lean_ctor_set(v___x_5548_, 1, v___x_5547_);
                    v___x_5549_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5548_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_);
                    return v___x_5549_;
                } else {
                    lean_dec(v_a_5532_);
                    lean_dec(v_a_5530_);
                    lean_dec_ref(v_type_5500_);
                    lean_dec(v_declName_5498_);
                    v___x_5550_ = lean_box(0);
                    if v_isShared_5535_ == 0 {
                        lean_ctor_set(v___x_5534_, 0, v___x_5550_);
                        v___x_5552_ = v___x_5534_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5550_);
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
                    v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
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
                    v_reuseFailAlloc_5569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5563_);
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
                    v_reuseFailAlloc_5577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5571_);
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
                    v_reuseFailAlloc_5586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_a_5580_);
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
                if lean_obj_tag(v___x_5591_) == 0 {
                    v_a_5592_ = lean_ctor_get(v___x_5591_, 0);
                    v_isSharedCheck_5652_ = (!lean_is_exclusive(v___x_5591_)) as u8;
                    if v_isSharedCheck_5652_ == 0 {
                        v___x_5594_ = v___x_5591_;
                        v_isShared_5595_ = v_isSharedCheck_5652_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5592_);
                        lean_dec(v___x_5591_);
                        v___x_5594_ = lean_box(0);
                        v_isShared_5595_ = v_isSharedCheck_5652_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_value_5501_);
                    lean_dec_ref(v_type_5500_);
                    lean_dec_ref(v_params_5499_);
                    lean_dec(v_declName_5498_);
                    v_a_5653_ = lean_ctor_get(v___x_5591_, 0);
                    v_isSharedCheck_5660_ = (!lean_is_exclusive(v___x_5591_)) as u8;
                    if v_isSharedCheck_5660_ == 0 {
                        v___x_5655_ = v___x_5591_;
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_5653_);
                        lean_dec(v___x_5591_);
                        v___x_5655_ = lean_box(0);
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 25;
                        continue;
                    }
                }
            }
            15 => {
                v___x_5596_ = (lean_unbox(v_a_5592_) as u8);
                lean_dec(v_a_5592_);
                if v___x_5596_ == 0 {
                    lean_dec_ref(v_value_5501_);
                    lean_dec_ref(v_type_5500_);
                    lean_dec_ref(v_params_5499_);
                    lean_dec(v_declName_5498_);
                    if v_isShared_5595_ == 0 {
                        lean_ctor_set(v___x_5594_, 0, v___x_5589_);
                        v___x_5598_ = v___x_5594_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5599_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5599_, 0, v___x_5589_);
                        v___x_5598_ = v_reuseFailAlloc_5599_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5594_);
                    v___x_5600_ = 0;
                    v___x_5601_ = l_Lean_Compiler_LCNF_Code_inferType(
                        v___x_5600_,
                        v_value_5501_,
                        v_a_5505_,
                        v_a_5506_,
                        v_a_5507_,
                        v_a_5508_,
                    );
                    if lean_obj_tag(v___x_5601_) == 0 {
                        v_a_5602_ = lean_ctor_get(v___x_5601_, 0);
                        lean_inc(v_a_5602_);
                        lean_dec_ref_known(v___x_5601_, 1);
                        v___x_5603_ = l_Lean_Compiler_LCNF_mkForallParams(
                            v___x_5600_,
                            v_params_5499_,
                            v_a_5602_,
                            v_a_5505_,
                            v_a_5506_,
                            v_a_5507_,
                            v_a_5508_,
                        );
                        lean_dec(v_a_5602_);
                        if lean_obj_tag(v___x_5603_) == 0 {
                            v_a_5604_ = lean_ctor_get(v___x_5603_, 0);
                            lean_inc_n(v_a_5604_, 2);
                            lean_dec_ref_known(v___x_5603_, 1);
                            lean_inc_ref(v_type_5500_);
                            v___x_5605_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
                                v_type_5500_,
                                v_a_5604_,
                                v_a_5504_,
                                v_a_5505_,
                                v_a_5506_,
                                v_a_5507_,
                                v_a_5508_,
                            );
                            if lean_obj_tag(v___x_5605_) == 0 {
                                v_a_5606_ = lean_ctor_get(v___x_5605_, 0);
                                v_isSharedCheck_5627_ = (!lean_is_exclusive(v___x_5605_)) as u8;
                                if v_isSharedCheck_5627_ == 0 {
                                    v___x_5608_ = v___x_5605_;
                                    v_isShared_5609_ = v_isSharedCheck_5627_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_5606_);
                                    lean_dec(v___x_5605_);
                                    v___x_5608_ = lean_box(0);
                                    v_isShared_5609_ = v_isSharedCheck_5627_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5604_);
                                lean_dec_ref(v_type_5500_);
                                lean_dec(v_declName_5498_);
                                v_a_5628_ = lean_ctor_get(v___x_5605_, 0);
                                v_isSharedCheck_5635_ = (!lean_is_exclusive(v___x_5605_)) as u8;
                                if v_isSharedCheck_5635_ == 0 {
                                    v___x_5630_ = v___x_5605_;
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_5628_);
                                    lean_dec(v___x_5605_);
                                    v___x_5630_ = lean_box(0);
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_type_5500_);
                            lean_dec(v_declName_5498_);
                            v_a_5636_ = lean_ctor_get(v___x_5603_, 0);
                            v_isSharedCheck_5643_ = (!lean_is_exclusive(v___x_5603_)) as u8;
                            if v_isSharedCheck_5643_ == 0 {
                                v___x_5638_ = v___x_5603_;
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_5636_);
                                lean_dec(v___x_5603_);
                                v___x_5638_ = lean_box(0);
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_type_5500_);
                        lean_dec_ref(v_params_5499_);
                        lean_dec(v_declName_5498_);
                        v_a_5644_ = lean_ctor_get(v___x_5601_, 0);
                        v_isSharedCheck_5651_ = (!lean_is_exclusive(v___x_5601_)) as u8;
                        if v_isSharedCheck_5651_ == 0 {
                            v___x_5646_ = v___x_5601_;
                            v_isShared_5647_ = v_isSharedCheck_5651_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_5644_);
                            lean_dec(v___x_5601_);
                            v___x_5646_ = lean_box(0);
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
                v___x_5610_ = (lean_unbox(v_a_5606_) as u8);
                if v___x_5610_ == 0 {
                    lean_del_object(v___x_5608_);
                    v___x_5611_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__5,
                    );
                    v___x_5612_ = (lean_unbox(v_a_5606_) as u8);
                    lean_dec(v_a_5606_);
                    v___x_5613_ = l_Lean_MessageData_ofConstName(v_declName_5498_, v___x_5612_);
                    v___x_5614_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5614_, 0, v___x_5611_);
                    lean_ctor_set(v___x_5614_, 1, v___x_5613_);
                    v___x_5615_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkLetDecl___closed__7,
                    );
                    v___x_5616_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5616_, 0, v___x_5614_);
                    lean_ctor_set(v___x_5616_, 1, v___x_5615_);
                    v___x_5617_ = l_Lean_indentExpr(v_a_5604_);
                    v___x_5618_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5618_, 0, v___x_5616_);
                    lean_ctor_set(v___x_5618_, 1, v___x_5617_);
                    v___x_5619_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Check_Pure_checkAppArgs_spec__1___redArg___lam__0___closed__7);
                    v___x_5620_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5620_, 0, v___x_5618_);
                    lean_ctor_set(v___x_5620_, 1, v___x_5619_);
                    v___x_5621_ = l_Lean_indentExpr(v_type_5500_);
                    v___x_5622_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5622_, 0, v___x_5620_);
                    lean_ctor_set(v___x_5622_, 1, v___x_5621_);
                    v___x_5623_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5622_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
                    return v___x_5623_;
                } else {
                    lean_dec(v_a_5606_);
                    lean_dec(v_a_5604_);
                    lean_dec_ref(v_type_5500_);
                    lean_dec(v_declName_5498_);
                    if v_isShared_5609_ == 0 {
                        lean_ctor_set(v___x_5608_, 0, v___x_5589_);
                        v___x_5625_ = v___x_5608_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_5626_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5626_, 0, v___x_5589_);
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
                    v_reuseFailAlloc_5634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
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
                    v_reuseFailAlloc_5642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_a_5636_);
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
                    v_reuseFailAlloc_5650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_a_5644_);
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
                    v_reuseFailAlloc_5659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
                    v___x_5658_ = v_reuseFailAlloc_5659_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5658_;
            }
            27 => {
                v_jps_5664_ = lean_ctor_get(v_a_5502_, 0);
                v_vars_5665_ = lean_ctor_get(v_a_5502_, 1);
                v___x_5666_ = lean_nat_dec_lt(v___x_5661_, v___x_5662_);
                if v___x_5666_ == 0 {
                    lean_inc_ref(v_a_5502_);
                    lean_inc_ref(v_value_5501_);
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
                    if lean_obj_tag(v___x_5667_) == 0 {
                        lean_dec_ref_known(v___x_5667_, 1);
                        state = 14;
                        continue;
                    } else {
                        if lean_obj_tag(v___x_5667_) == 0 {
                            lean_dec_ref_known(v___x_5667_, 1);
                            state = 14;
                            continue;
                        } else {
                            lean_dec_ref(v_value_5501_);
                            lean_dec_ref(v_type_5500_);
                            lean_dec_ref(v_params_5499_);
                            lean_dec(v_declName_5498_);
                            return v___x_5667_;
                        }
                    }
                } else {
                    v___x_5668_ = lean_nat_dec_le(v___x_5662_, v___x_5662_);
                    if v___x_5668_ == 0 {
                        if v___x_5666_ == 0 {
                            lean_inc_ref(v_a_5502_);
                            lean_inc_ref(v_value_5501_);
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
                            if lean_obj_tag(v___x_5669_) == 0 {
                                lean_dec_ref_known(v___x_5669_, 1);
                                v___y_5511_ = v_a_5504_;
                                v___y_5512_ = v_a_5505_;
                                v___y_5513_ = v_a_5506_;
                                v___y_5514_ = v_a_5507_;
                                v___y_5515_ = v_a_5508_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_value_5501_);
                                lean_dec_ref(v_type_5500_);
                                lean_dec_ref(v_params_5499_);
                                lean_dec(v_declName_5498_);
                                return v___x_5669_;
                            }
                        } else {
                            v___x_5670_ = 0usize;
                            v___x_5671_ = lean_usize_of_nat(v___x_5662_);
                            lean_inc(v_vars_5665_);
                            v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5499_, v___x_5670_, v___x_5671_, v_vars_5665_);
                            lean_inc(v_jps_5664_);
                            v___x_5673_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_5673_, 0, v_jps_5664_);
                            lean_ctor_set(v___x_5673_, 1, v___x_5672_);
                            lean_inc_ref(v_value_5501_);
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
                            if lean_obj_tag(v___x_5674_) == 0 {
                                lean_dec_ref_known(v___x_5674_, 1);
                                v___y_5511_ = v_a_5504_;
                                v___y_5512_ = v_a_5505_;
                                v___y_5513_ = v_a_5506_;
                                v___y_5514_ = v_a_5507_;
                                v___y_5515_ = v_a_5508_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_value_5501_);
                                lean_dec_ref(v_type_5500_);
                                lean_dec_ref(v_params_5499_);
                                lean_dec(v_declName_5498_);
                                return v___x_5674_;
                            }
                        }
                    } else {
                        v___x_5675_ = 0usize;
                        v___x_5676_ = lean_usize_of_nat(v___x_5662_);
                        lean_inc(v_vars_5665_);
                        v___x_5677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5499_, v___x_5675_, v___x_5676_, v_vars_5665_);
                        lean_inc(v_jps_5664_);
                        v___x_5678_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5678_, 0, v_jps_5664_);
                        lean_ctor_set(v___x_5678_, 1, v___x_5677_);
                        lean_inc_ref(v_value_5501_);
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
                        if lean_obj_tag(v___x_5679_) == 0 {
                            lean_dec_ref_known(v___x_5679_, 1);
                            v___y_5511_ = v_a_5504_;
                            v___y_5512_ = v_a_5505_;
                            v___y_5513_ = v_a_5506_;
                            v___y_5514_ = v_a_5507_;
                            v___y_5515_ = v_a_5508_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_value_5501_);
                            lean_dec_ref(v_type_5500_);
                            lean_dec_ref(v_params_5499_);
                            lean_dec(v_declName_5498_);
                            return v___x_5679_;
                        }
                    }
                }
            }
            28 => {
                if lean_obj_tag(v___y_5681_) == 0 {
                    lean_dec_ref_known(v___y_5681_, 1);
                    state = 27;
                    continue;
                } else {
                    lean_dec_ref(v_value_5501_);
                    lean_dec_ref(v_type_5500_);
                    lean_dec_ref(v_params_5499_);
                    lean_dec(v_declName_5498_);
                    return v___y_5681_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1() -> *mut LeanObject {
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    v___x_5691_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__0;
    v___x_5692_ = l_Lean_stringToMessageData(v___x_5691_);
    return v___x_5692_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3() -> *mut LeanObject {
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut LeanObject = core::ptr::null_mut();
    v___x_5694_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__2;
    v___x_5695_ = l_Lean_stringToMessageData(v___x_5694_);
    return v___x_5695_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5() -> *mut LeanObject {
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    v___x_5697_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__4;
    v___x_5698_ = l_Lean_stringToMessageData(v___x_5697_);
    return v___x_5698_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7() -> *mut LeanObject {
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    v___x_5700_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__6;
    v___x_5701_ = l_Lean_stringToMessageData(v___x_5700_);
    return v___x_5701_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9() -> *mut LeanObject {
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    v___x_5703_ = l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__8;
    v___x_5704_ = l_Lean_stringToMessageData(v___x_5703_);
    return v___x_5704_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl(
    mut v_funDecl_5705_: *mut LeanObject,
    mut v_a_5706_: *mut LeanObject,
    mut v_a_5707_: *mut LeanObject,
    mut v_a_5708_: *mut LeanObject,
    mut v_a_5709_: *mut LeanObject,
    mut v_a_5710_: *mut LeanObject,
    mut v_a_5711_: *mut LeanObject,
    mut v_a_5712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: u8 = 0;
    let mut v___y_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5730_: u8 = 0;
    let mut v___x_5731_: u8 = 0;
    let mut v___x_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5742_: u8 = 0;
    let mut v_a_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5746_: u8 = 0;
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5750_: u8 = 0;
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: u8 = 0;
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_5714_ = lean_ctor_get(v_funDecl_5705_, 0);
                v_binderName_5715_ = lean_ctor_get(v_funDecl_5705_, 1);
                lean_inc_n(v_binderName_5715_, 2);
                v_params_5716_ = lean_ctor_get(v_funDecl_5705_, 2);
                v_type_5717_ = lean_ctor_get(v_funDecl_5705_, 3);
                v_value_5718_ = lean_ctor_get(v_funDecl_5705_, 4);
                lean_inc_ref(v_value_5718_);
                lean_inc_ref(v_type_5717_);
                lean_inc_ref(v_params_5716_);
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
                if lean_obj_tag(v___x_5719_) == 0 {
                    lean_dec_ref_known(v___x_5719_, 1);
                    v___x_5720_ = 0;
                    lean_inc(v_fvarId_5714_);
                    v___x_5751_ = l_Lean_Compiler_LCNF_getFunDecl(
                        v___x_5720_,
                        v_fvarId_5714_,
                        v_a_5709_,
                        v_a_5710_,
                        v_a_5711_,
                        v_a_5712_,
                    );
                    if lean_obj_tag(v___x_5751_) == 0 {
                        v_a_5752_ = lean_ctor_get(v___x_5751_, 0);
                        lean_inc(v_a_5752_);
                        lean_dec_ref_known(v___x_5751_, 1);
                        v_binderName_5753_ = lean_ctor_get(v_a_5752_, 1);
                        lean_inc(v_binderName_5753_);
                        v_type_5754_ = lean_ctor_get(v_a_5752_, 3);
                        lean_inc_ref(v_type_5754_);
                        lean_dec(v_a_5752_);
                        v___x_5773_ = lean_name_eq(v_binderName_5753_, v_binderName_5715_);
                        if v___x_5773_ == 0 {
                            v___x_5774_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                            );
                            lean_inc(v_binderName_5715_);
                            v___x_5775_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                            v___x_5776_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5776_, 0, v___x_5774_);
                            lean_ctor_set(v___x_5776_, 1, v___x_5775_);
                            v___x_5777_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__9,
                            );
                            v___x_5778_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5778_, 0, v___x_5776_);
                            lean_ctor_set(v___x_5778_, 1, v___x_5777_);
                            v___x_5779_ = l_Lean_MessageData_ofName(v_binderName_5753_);
                            v___x_5780_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5780_, 0, v___x_5778_);
                            lean_ctor_set(v___x_5780_, 1, v___x_5779_);
                            v___x_5781_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                            v___x_5782_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5782_, 0, v___x_5780_);
                            lean_ctor_set(v___x_5782_, 1, v___x_5781_);
                            v___x_5783_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5782_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_);
                            if lean_obj_tag(v___x_5783_) == 0 {
                                lean_dec_ref_known(v___x_5783_, 1);
                                v___y_5756_ = v_a_5709_;
                                v___y_5757_ = v_a_5710_;
                                v___y_5758_ = v_a_5711_;
                                v___y_5759_ = v_a_5712_;
                                state = 6;
                                continue;
                            } else {
                                lean_dec_ref(v_type_5754_);
                                lean_dec(v_binderName_5715_);
                                lean_dec_ref(v_funDecl_5705_);
                                return v___x_5783_;
                            }
                        } else {
                            lean_dec(v_binderName_5753_);
                            v___y_5756_ = v_a_5709_;
                            v___y_5757_ = v_a_5710_;
                            v___y_5758_ = v_a_5711_;
                            v___y_5759_ = v_a_5712_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_binderName_5715_);
                        lean_dec_ref(v_funDecl_5705_);
                        v_a_5784_ = lean_ctor_get(v___x_5751_, 0);
                        v_isSharedCheck_5791_ = (!lean_is_exclusive(v___x_5751_)) as u8;
                        if v_isSharedCheck_5791_ == 0 {
                            v___x_5786_ = v___x_5751_;
                            v_isShared_5787_ = v_isSharedCheck_5791_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5784_);
                            lean_dec(v___x_5751_);
                            v___x_5786_ = lean_box(0);
                            v_isShared_5787_ = v_isSharedCheck_5791_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_binderName_5715_);
                    lean_dec_ref(v_funDecl_5705_);
                    return v___x_5719_;
                }
            }
            1 => {
                lean_inc(v_fvarId_5714_);
                v___x_5726_ = l_Lean_Compiler_LCNF_getFunDecl(
                    v___x_5720_,
                    v_fvarId_5714_,
                    v___y_5722_,
                    v___y_5723_,
                    v___y_5724_,
                    v___y_5725_,
                );
                if lean_obj_tag(v___x_5726_) == 0 {
                    v_a_5727_ = lean_ctor_get(v___x_5726_, 0);
                    v_isSharedCheck_5742_ = (!lean_is_exclusive(v___x_5726_)) as u8;
                    if v_isSharedCheck_5742_ == 0 {
                        v___x_5729_ = v___x_5726_;
                        v_isShared_5730_ = v_isSharedCheck_5742_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5727_);
                        lean_dec(v___x_5726_);
                        v___x_5729_ = lean_box(0);
                        v_isShared_5730_ = v_isSharedCheck_5742_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_binderName_5715_);
                    lean_dec_ref(v_funDecl_5705_);
                    v_a_5743_ = lean_ctor_get(v___x_5726_, 0);
                    v_isSharedCheck_5750_ = (!lean_is_exclusive(v___x_5726_)) as u8;
                    if v_isSharedCheck_5750_ == 0 {
                        v___x_5745_ = v___x_5726_;
                        v_isShared_5746_ = v_isSharedCheck_5750_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5743_);
                        lean_dec(v___x_5726_);
                        v___x_5745_ = lean_box(0);
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
                lean_dec_ref(v_funDecl_5705_);
                lean_dec(v_a_5727_);
                if v___x_5731_ == 0 {
                    lean_del_object(v___x_5729_);
                    v___x_5732_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                    );
                    v___x_5733_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                    v___x_5734_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5734_, 0, v___x_5732_);
                    lean_ctor_set(v___x_5734_, 1, v___x_5733_);
                    v___x_5735_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__3,
                    );
                    v___x_5736_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5736_, 0, v___x_5734_);
                    lean_ctor_set(v___x_5736_, 1, v___x_5735_);
                    v___x_5737_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5736_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
                    return v___x_5737_;
                } else {
                    lean_dec(v_binderName_5715_);
                    v___x_5738_ = lean_box(0);
                    if v_isShared_5730_ == 0 {
                        lean_ctor_set(v___x_5729_, 0, v___x_5738_);
                        v___x_5740_ = v___x_5729_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5738_);
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
                    v_reuseFailAlloc_5749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_a_5743_);
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
                    v___x_5761_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__1,
                    );
                    lean_inc(v_binderName_5715_);
                    v___x_5762_ = l_Lean_MessageData_ofName(v_binderName_5715_);
                    v___x_5763_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5763_, 0, v___x_5761_);
                    lean_ctor_set(v___x_5763_, 1, v___x_5762_);
                    v___x_5764_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__5,
                    );
                    v___x_5765_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5765_, 0, v___x_5763_);
                    lean_ctor_set(v___x_5765_, 1, v___x_5764_);
                    v___x_5766_ = l_Lean_indentExpr(v_type_5754_);
                    v___x_5767_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5767_, 0, v___x_5765_);
                    lean_ctor_set(v___x_5767_, 1, v___x_5766_);
                    v___x_5768_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___closed__7,
                    );
                    v___x_5769_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5769_, 0, v___x_5767_);
                    lean_ctor_set(v___x_5769_, 1, v___x_5768_);
                    lean_inc_ref(v_type_5717_);
                    v___x_5770_ = l_Lean_indentExpr(v_type_5717_);
                    v___x_5771_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5771_, 0, v___x_5769_);
                    lean_ctor_set(v___x_5771_, 1, v___x_5770_);
                    v___x_5772_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5771_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_);
                    if lean_obj_tag(v___x_5772_) == 0 {
                        lean_dec_ref_known(v___x_5772_, 1);
                        v___y_5722_ = v___y_5756_;
                        v___y_5723_ = v___y_5757_;
                        v___y_5724_ = v___y_5758_;
                        v___y_5725_ = v___y_5759_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_binderName_5715_);
                        lean_dec_ref(v_funDecl_5705_);
                        return v___x_5772_;
                    }
                } else {
                    lean_dec_ref(v_type_5754_);
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
                    v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__2() -> *mut LeanObject {
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    v___x_5793_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__1;
    v___x_5794_ = l_Lean_stringToMessageData(v___x_5793_);
    return v___x_5794_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__4() -> *mut LeanObject {
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    v___x_5796_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__3;
    v___x_5797_ = l_Lean_stringToMessageData(v___x_5796_);
    return v___x_5797_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__6() -> *mut LeanObject {
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    v___x_5799_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__5;
    v___x_5800_ = l_Lean_stringToMessageData(v___x_5799_);
    return v___x_5800_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__8() -> *mut LeanObject {
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    v___x_5802_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__7;
    v___x_5803_ = l_Lean_stringToMessageData(v___x_5802_);
    return v___x_5803_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_checkCases___closed__0() -> *mut LeanObject {
    let mut v_hasDefault_5804_: u8 = 0;
    let mut v_ctorNames_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    v_hasDefault_5804_ = 0;
    v_ctorNames_5805_ = l_Lean_NameSet_empty;
    v___x_5806_ = lean_box((v_hasDefault_5804_) as usize);
    v___x_5807_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5807_, 0, v_ctorNames_5805_);
    lean_ctor_set(v___x_5807_, 1, v___x_5806_);
    return v___x_5807_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    v___x_5809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__0;
    v___x_5810_ = l_Lean_stringToMessageData(v___x_5809_);
    return v___x_5810_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    v___x_5812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__2;
    v___x_5813_ = l_Lean_stringToMessageData(v___x_5812_);
    return v___x_5813_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5()
-> *mut LeanObject {
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    v___x_5815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__4;
    v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7()
-> *mut LeanObject {
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    v___x_5818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__6;
    v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
    return v___x_5819_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9()
-> *mut LeanObject {
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    v___x_5821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__8;
    v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11()
-> *mut LeanObject {
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    v___x_5824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__10;
    v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
    return v___x_5825_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13()
-> *mut LeanObject {
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    v___x_5827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__12;
    v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15()
-> *mut LeanObject {
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    v___x_5830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__14;
    v___x_5831_ = l_Lean_stringToMessageData(v___x_5830_);
    return v___x_5831_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5(
    mut v_typeName_5832_: *mut LeanObject,
    mut v_as_5833_: *mut LeanObject,
    mut v_sz_5834_: usize,
    mut v_i_5835_: usize,
    mut v_b_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
    mut v___y_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: usize = 0;
    let mut v___x_5848_: usize = 0;
    let mut v___x_5850_: u8 = 0;
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___y_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5866_: u8 = 0;
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_a_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: u8 = 0;
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: u8 = 0;
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: usize = 0;
    let mut v___x_5895_: usize = 0;
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: usize = 0;
    let mut v___x_5900_: usize = 0;
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5919_: u8 = 0;
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5923_: u8 = 0;
    let mut v___y_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: u8 = 0;
    let mut v___x_5938_: usize = 0;
    let mut v___x_5939_: usize = 0;
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: usize = 0;
    let mut v___x_5942_: usize = 0;
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u8 = 0;
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5977_: u8 = 0;
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v___y_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_induct_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: u8 = 0;
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6010_: u8 = 0;
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6014_: u8 = 0;
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6025_: u8 = 0;
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6029_: u8 = 0;
    let mut v_a_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6033_: u8 = 0;
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6037_: u8 = 0;
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: u8 = 0;
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6049_: u8 = 0;
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6053_: u8 = 0;
    let mut v_a_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6057_: u8 = 0;
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6061_: u8 = 0;
    let mut v_code_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_isSharedCheck_6074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5850_ = lean_usize_dec_lt(v_i_5835_, v_sz_5834_);
                if v___x_5850_ == 0 {
                    lean_dec(v_typeName_5832_);
                    v___x_5851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5851_, 0, v_b_5836_);
                    return v___x_5851_;
                } else {
                    v_fst_5852_ = lean_ctor_get(v_b_5836_, 0);
                    v_snd_5853_ = lean_ctor_get(v_b_5836_, 1);
                    v_isSharedCheck_6074_ = (!lean_is_exclusive(v_b_5836_)) as u8;
                    if v_isSharedCheck_6074_ == 0 {
                        v___x_5855_ = v_b_5836_;
                        v_isShared_5856_ = v_isSharedCheck_6074_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_5853_);
                        lean_inc(v_fst_5852_);
                        lean_dec(v_b_5836_);
                        v___x_5855_ = lean_box(0);
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
                if lean_obj_tag(v_a_5871_) == 0 {
                    v_ctorName_5872_ = lean_ctor_get(v_a_5871_, 0);
                    v_params_5873_ = lean_ctor_get(v_a_5871_, 1);
                    v_code_5874_ = lean_ctor_get(v_a_5871_, 2);
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
                    if lean_obj_tag(v___x_6038_) == 0 {
                        lean_dec_ref_known(v___x_6038_, 1);
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
                            v___x_6040_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__13);
                            lean_inc(v_ctorName_5872_);
                            v___x_6041_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                            v___x_6042_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6042_, 0, v___x_6040_);
                            lean_ctor_set(v___x_6042_, 1, v___x_6041_);
                            v___x_6043_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__15);
                            v___x_6044_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6044_, 0, v___x_6042_);
                            lean_ctor_set(v___x_6044_, 1, v___x_6043_);
                            v___x_6045_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6044_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
                            if lean_obj_tag(v___x_6045_) == 0 {
                                lean_dec_ref_known(v___x_6045_, 1);
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
                                lean_del_object(v___x_5855_);
                                lean_dec(v_snd_5853_);
                                lean_dec(v_fst_5852_);
                                lean_dec(v_typeName_5832_);
                                v_a_6046_ = lean_ctor_get(v___x_6045_, 0);
                                v_isSharedCheck_6053_ = (!lean_is_exclusive(v___x_6045_)) as u8;
                                if v_isSharedCheck_6053_ == 0 {
                                    v___x_6048_ = v___x_6045_;
                                    v_isShared_6049_ = v_isSharedCheck_6053_;
                                    state = 22;
                                    continue;
                                } else {
                                    lean_inc(v_a_6046_);
                                    lean_dec(v___x_6045_);
                                    v___x_6048_ = lean_box(0);
                                    v_isShared_6049_ = v_isSharedCheck_6053_;
                                    state = 22;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_5855_);
                        lean_dec(v_snd_5853_);
                        lean_dec(v_fst_5852_);
                        lean_dec(v_typeName_5832_);
                        v_a_6054_ = lean_ctor_get(v___x_6038_, 0);
                        v_isSharedCheck_6061_ = (!lean_is_exclusive(v___x_6038_)) as u8;
                        if v_isSharedCheck_6061_ == 0 {
                            v___x_6056_ = v___x_6038_;
                            v_isShared_6057_ = v_isSharedCheck_6061_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_a_6054_);
                            lean_dec(v___x_6038_);
                            v___x_6056_ = lean_box(0);
                            v_isShared_6057_ = v_isSharedCheck_6061_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5855_);
                    lean_dec(v_snd_5853_);
                    v_code_6062_ = lean_ctor_get(v_a_5871_, 0);
                    lean_inc_ref(v___y_5837_);
                    lean_inc_ref(v_code_6062_);
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
                    if lean_obj_tag(v___x_6063_) == 0 {
                        lean_dec_ref_known(v___x_6063_, 1);
                        v___x_6064_ = lean_box((v___x_5850_) as usize);
                        v___x_6065_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_6065_, 0, v_fst_5852_);
                        lean_ctor_set(v___x_6065_, 1, v___x_6064_);
                        v_a_5846_ = v___x_6065_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_fst_5852_);
                        lean_dec(v_typeName_5832_);
                        v_a_6066_ = lean_ctor_get(v___x_6063_, 0);
                        v_isSharedCheck_6073_ = (!lean_is_exclusive(v___x_6063_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6063_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 26;
                            continue;
                        } else {
                            lean_inc(v_a_6066_);
                            lean_dec(v___x_6063_);
                            v___x_6068_ = lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if lean_obj_tag(v___y_5859_) == 0 {
                    lean_dec_ref_known(v___y_5859_, 1);
                    if v_isShared_5856_ == 0 {
                        lean_ctor_set(v___x_5855_, 0, v___y_5858_);
                        v___x_5861_ = v___x_5855_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5862_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___y_5858_);
                        lean_ctor_set(v_reuseFailAlloc_5862_, 1, v_snd_5853_);
                        v___x_5861_ = v_reuseFailAlloc_5862_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___y_5858_);
                    lean_del_object(v___x_5855_);
                    lean_dec(v_snd_5853_);
                    lean_dec(v_typeName_5832_);
                    v_a_5863_ = lean_ctor_get(v___y_5859_, 0);
                    v_isSharedCheck_5870_ = (!lean_is_exclusive(v___y_5859_)) as u8;
                    if v_isSharedCheck_5870_ == 0 {
                        v___x_5865_ = v___y_5859_;
                        v_isShared_5866_ = v_isSharedCheck_5870_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5863_);
                        lean_dec(v___y_5859_);
                        v___x_5865_ = lean_box(0);
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
                    v_reuseFailAlloc_5869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
                    v___x_5868_ = v_reuseFailAlloc_5869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5868_;
            }
            7 => {
                v_jps_5886_ = lean_ctor_get(v___y_5880_, 0);
                v_vars_5887_ = lean_ctor_get(v___y_5880_, 1);
                v___x_5888_ = lean_nat_dec_lt(v___y_5876_, v___y_5885_);
                if v___x_5888_ == 0 {
                    lean_dec(v___y_5885_);
                    lean_inc(v_vars_5887_);
                    lean_inc(v_jps_5886_);
                    v___x_5889_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5889_, 0, v_jps_5886_);
                    lean_ctor_set(v___x_5889_, 1, v_vars_5887_);
                    lean_inc_ref(v_code_5874_);
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
                            lean_dec(v___y_5885_);
                            lean_inc(v_vars_5887_);
                            lean_inc(v_jps_5886_);
                            v___x_5892_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_5892_, 0, v_jps_5886_);
                            lean_ctor_set(v___x_5892_, 1, v_vars_5887_);
                            lean_inc_ref(v_code_5874_);
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
                            lean_dec(v___y_5885_);
                            lean_inc(v_vars_5887_);
                            v___x_5896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5873_, v___x_5894_, v___x_5895_, v_vars_5887_);
                            lean_inc(v_jps_5886_);
                            v___x_5897_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_5897_, 0, v_jps_5886_);
                            lean_ctor_set(v___x_5897_, 1, v___x_5896_);
                            lean_inc_ref(v_code_5874_);
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
                        lean_dec(v___y_5885_);
                        lean_inc(v_vars_5887_);
                        v___x_5901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__0(v_params_5873_, v___x_5899_, v___x_5900_, v_vars_5887_);
                        lean_inc(v_jps_5886_);
                        v___x_5902_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5902_, 0, v_jps_5886_);
                        lean_ctor_set(v___x_5902_, 1, v___x_5901_);
                        lean_inc_ref(v_code_5874_);
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
                if lean_obj_tag(v___y_5915_) == 0 {
                    lean_dec_ref_known(v___y_5915_, 1);
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
                    lean_dec(v___y_5914_);
                    lean_dec(v___y_5911_);
                    lean_del_object(v___x_5855_);
                    lean_dec(v_snd_5853_);
                    lean_dec(v_typeName_5832_);
                    v_a_5916_ = lean_ctor_get(v___y_5915_, 0);
                    v_isSharedCheck_5923_ = (!lean_is_exclusive(v___y_5915_)) as u8;
                    if v_isSharedCheck_5923_ == 0 {
                        v___x_5918_ = v___y_5915_;
                        v_isShared_5919_ = v_isSharedCheck_5923_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5916_);
                        lean_dec(v___y_5915_);
                        v___x_5918_ = lean_box(0);
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
                    v_reuseFailAlloc_5922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_a_5916_);
                    v___x_5921_ = v_reuseFailAlloc_5922_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5921_;
            }
            11 => {
                v___x_5933_ = lean_unsigned_to_nat(0);
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
                    v___x_5936_ = lean_box(0);
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
                    v___x_5956_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                    lean_inc(v_ctorName_5872_);
                    v___x_5957_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                    v___x_5958_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5958_, 0, v___x_5956_);
                    lean_ctor_set(v___x_5958_, 1, v___x_5957_);
                    v___x_5959_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__3);
                    v___x_5960_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5960_, 0, v___x_5958_);
                    lean_ctor_set(v___x_5960_, 1, v___x_5959_);
                    v___x_5961_ = l_Nat_reprFast(v_numFields_5945_);
                    v___x_5962_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_5962_, 0, v___x_5961_);
                    v___x_5963_ = l_Lean_MessageData_ofFormat(v___x_5962_);
                    v___x_5964_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5964_, 0, v___x_5960_);
                    lean_ctor_set(v___x_5964_, 1, v___x_5963_);
                    v___x_5965_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__5);
                    v___x_5966_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5966_, 0, v___x_5964_);
                    lean_ctor_set(v___x_5966_, 1, v___x_5965_);
                    v___x_5967_ = l_Nat_reprFast(v___x_5954_);
                    v___x_5968_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_5968_, 0, v___x_5967_);
                    v___x_5969_ = l_Lean_MessageData_ofFormat(v___x_5968_);
                    v___x_5970_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5970_, 0, v___x_5966_);
                    lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                    v___x_5971_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__7);
                    v___x_5972_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5972_, 0, v___x_5970_);
                    lean_ctor_set(v___x_5972_, 1, v___x_5971_);
                    v___x_5973_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_5972_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_);
                    if lean_obj_tag(v___x_5973_) == 0 {
                        lean_dec_ref_known(v___x_5973_, 1);
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
                        lean_dec(v___y_5946_);
                        lean_del_object(v___x_5855_);
                        lean_dec(v_snd_5853_);
                        lean_dec(v_typeName_5832_);
                        v_a_5974_ = lean_ctor_get(v___x_5973_, 0);
                        v_isSharedCheck_5981_ = (!lean_is_exclusive(v___x_5973_)) as u8;
                        if v_isSharedCheck_5981_ == 0 {
                            v___x_5976_ = v___x_5973_;
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_5974_);
                            lean_dec(v___x_5973_);
                            v___x_5976_ = lean_box(0);
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_numFields_5945_);
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
                    v_reuseFailAlloc_5980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
                    v___x_5979_ = v_reuseFailAlloc_5980_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5979_;
            }
            15 => {
                lean_inc_n(v_ctorName_5872_, 2);
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
                if lean_obj_tag(v___x_5991_) == 0 {
                    v_a_5992_ = lean_ctor_get(v___x_5991_, 0);
                    lean_inc(v_a_5992_);
                    lean_dec_ref_known(v___x_5991_, 1);
                    if lean_obj_tag(v_a_5992_) == 6 {
                        v_val_5993_ = lean_ctor_get(v_a_5992_, 0);
                        lean_inc_ref(v_val_5993_);
                        lean_dec_ref_known(v_a_5992_, 1);
                        v_induct_5994_ = lean_ctor_get(v_val_5993_, 1);
                        lean_inc(v_induct_5994_);
                        v_numFields_5995_ = lean_ctor_get(v_val_5993_, 4);
                        lean_inc(v_numFields_5995_);
                        lean_dec_ref(v_val_5993_);
                        v___x_5996_ = lean_name_eq(v_induct_5994_, v_typeName_5832_);
                        lean_dec(v_induct_5994_);
                        if v___x_5996_ == 0 {
                            v___x_5997_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                            lean_inc(v_ctorName_5872_);
                            v___x_5998_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                            v___x_5999_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5999_, 0, v___x_5997_);
                            lean_ctor_set(v___x_5999_, 1, v___x_5998_);
                            v___x_6000_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__9);
                            v___x_6001_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6001_, 0, v___x_5999_);
                            lean_ctor_set(v___x_6001_, 1, v___x_6000_);
                            lean_inc(v_typeName_5832_);
                            v___x_6002_ = l_Lean_MessageData_ofName(v_typeName_5832_);
                            v___x_6003_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6003_, 0, v___x_6001_);
                            lean_ctor_set(v___x_6003_, 1, v___x_6002_);
                            v___x_6004_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1___redArg___closed__3);
                            v___x_6005_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6005_, 0, v___x_6003_);
                            lean_ctor_set(v___x_6005_, 1, v___x_6004_);
                            v___x_6006_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6005_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
                            if lean_obj_tag(v___x_6006_) == 0 {
                                lean_dec_ref_known(v___x_6006_, 1);
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
                                lean_dec(v_numFields_5995_);
                                lean_dec(v___x_5990_);
                                lean_del_object(v___x_5855_);
                                lean_dec(v_snd_5853_);
                                lean_dec(v_typeName_5832_);
                                v_a_6007_ = lean_ctor_get(v___x_6006_, 0);
                                v_isSharedCheck_6014_ = (!lean_is_exclusive(v___x_6006_)) as u8;
                                if v_isSharedCheck_6014_ == 0 {
                                    v___x_6009_ = v___x_6006_;
                                    v_isShared_6010_ = v_isSharedCheck_6014_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_6007_);
                                    lean_dec(v___x_6006_);
                                    v___x_6009_ = lean_box(0);
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
                        lean_dec(v_a_5992_);
                        lean_del_object(v___x_5855_);
                        v___x_6015_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__1);
                        lean_inc(v_ctorName_5872_);
                        v___x_6016_ = l_Lean_MessageData_ofName(v_ctorName_5872_);
                        v___x_6017_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6017_, 0, v___x_6015_);
                        lean_ctor_set(v___x_6017_, 1, v___x_6016_);
                        v___x_6018_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___closed__11);
                        v___x_6019_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6019_, 0, v___x_6017_);
                        lean_ctor_set(v___x_6019_, 1, v___x_6018_);
                        v___x_6020_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6019_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
                        if lean_obj_tag(v___x_6020_) == 0 {
                            lean_dec_ref_known(v___x_6020_, 1);
                            v___x_6021_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_6021_, 0, v___x_5990_);
                            lean_ctor_set(v___x_6021_, 1, v_snd_5853_);
                            v_a_5846_ = v___x_6021_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_5990_);
                            lean_dec(v_snd_5853_);
                            lean_dec(v_typeName_5832_);
                            v_a_6022_ = lean_ctor_get(v___x_6020_, 0);
                            v_isSharedCheck_6029_ = (!lean_is_exclusive(v___x_6020_)) as u8;
                            if v_isSharedCheck_6029_ == 0 {
                                v___x_6024_ = v___x_6020_;
                                v_isShared_6025_ = v_isSharedCheck_6029_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_6022_);
                                lean_dec(v___x_6020_);
                                v___x_6024_ = lean_box(0);
                                v_isShared_6025_ = v_isSharedCheck_6029_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_5990_);
                    lean_del_object(v___x_5855_);
                    lean_dec(v_snd_5853_);
                    lean_dec(v_typeName_5832_);
                    v_a_6030_ = lean_ctor_get(v___x_5991_, 0);
                    v_isSharedCheck_6037_ = (!lean_is_exclusive(v___x_5991_)) as u8;
                    if v_isSharedCheck_6037_ == 0 {
                        v___x_6032_ = v___x_5991_;
                        v_isShared_6033_ = v_isSharedCheck_6037_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_6030_);
                        lean_dec(v___x_5991_);
                        v___x_6032_ = lean_box(0);
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
                    v_reuseFailAlloc_6013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_a_6007_);
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
                    v_reuseFailAlloc_6028_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
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
                    v_reuseFailAlloc_6036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_a_6030_);
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
                    v_reuseFailAlloc_6052_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_a_6046_);
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
                    v_reuseFailAlloc_6060_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6060_, 0, v_a_6054_);
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
                    v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
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
    mut v_c_6075_: *mut LeanObject,
    mut v_a_6076_: *mut LeanObject,
    mut v_a_6077_: *mut LeanObject,
    mut v_a_6078_: *mut LeanObject,
    mut v_a_6079_: *mut LeanObject,
    mut v_a_6080_: *mut LeanObject,
    mut v_a_6081_: *mut LeanObject,
    mut v_a_6082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_typeName_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6089_: usize = 0;
    let mut v___x_6090_: usize = 0;
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6094_: u8 = 0;
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut v_unused_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6104_: u8 = 0;
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_6084_ = lean_ctor_get(v_c_6075_, 0);
                lean_inc(v_typeName_6084_);
                v_discr_6085_ = lean_ctor_get(v_c_6075_, 2);
                lean_inc(v_discr_6085_);
                v_alts_6086_ = lean_ctor_get(v_c_6075_, 3);
                lean_inc_ref(v_alts_6086_);
                lean_dec_ref(v_c_6075_);
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
                if lean_obj_tag(v___x_6087_) == 0 {
                    lean_dec_ref_known(v___x_6087_, 1);
                    v___x_6088_ = lean_obj_once(
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
                    lean_dec_ref(v_alts_6086_);
                    if lean_obj_tag(v___x_6091_) == 0 {
                        v_isSharedCheck_6099_ = (!lean_is_exclusive(v___x_6091_)) as u8;
                        if v_isSharedCheck_6099_ == 0 {
                            v_unused_6100_ = lean_ctor_get(v___x_6091_, 0);
                            lean_dec(v_unused_6100_);
                            v___x_6093_ = v___x_6091_;
                            v_isShared_6094_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_6091_);
                            v___x_6093_ = lean_box(0);
                            v_isShared_6094_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6101_ = lean_ctor_get(v___x_6091_, 0);
                        v_isSharedCheck_6108_ = (!lean_is_exclusive(v___x_6091_)) as u8;
                        if v_isSharedCheck_6108_ == 0 {
                            v___x_6103_ = v___x_6091_;
                            v_isShared_6104_ = v_isSharedCheck_6108_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6101_);
                            lean_dec(v___x_6091_);
                            v___x_6103_ = lean_box(0);
                            v_isShared_6104_ = v_isSharedCheck_6108_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_alts_6086_);
                    lean_dec(v_typeName_6084_);
                    return v___x_6087_;
                }
            }
            1 => {
                v___x_6095_ = lean_box(0);
                if v_isShared_6094_ == 0 {
                    lean_ctor_set(v___x_6093_, 0, v___x_6095_);
                    v___x_6097_ = v___x_6093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6098_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6098_, 0, v___x_6095_);
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
                    v_reuseFailAlloc_6107_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6107_, 0, v_a_6101_);
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
    mut v_code_6109_: *mut LeanObject,
    mut v_a_6110_: *mut LeanObject,
    mut v_a_6111_: *mut LeanObject,
    mut v_a_6112_: *mut LeanObject,
    mut v_a_6113_: *mut LeanObject,
    mut v_a_6114_: *mut LeanObject,
    mut v_a_6115_: *mut LeanObject,
    mut v_a_6116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6122_: u8 = 0;
    let mut v_decl_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6127_: u8 = 0;
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v_decl_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6143_: u8 = 0;
    let mut v_jps_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6156_: u8 = 0;
    let mut v_decl_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6161_: u8 = 0;
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6172_: u8 = 0;
    let mut v_fvarId_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___y_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6191_: u8 = 0;
    let mut v___x_6192_: u8 = 0;
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: u8 = 0;
    let mut v_binderName_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6224_: u8 = 0;
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6228_: u8 = 0;
    let mut v_isSharedCheck_6229_: u8 = 0;
    let mut v_unused_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut v_cases_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6240_: u8 = 0;
    let mut v_unused_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6118_ = l_Lean_Compiler_LCNF_Check_Pure_check___closed__0;
                v___x_6119_ = l_Lean_Core_checkSystem(v___x_6118_, v_a_6115_, v_a_6116_);
                if lean_obj_tag(v___x_6119_) == 0 {
                    v_isSharedCheck_6240_ = (!lean_is_exclusive(v___x_6119_)) as u8;
                    if v_isSharedCheck_6240_ == 0 {
                        v_unused_6241_ = lean_ctor_get(v___x_6119_, 0);
                        lean_dec(v_unused_6241_);
                        v___x_6121_ = v___x_6119_;
                        v_isShared_6122_ = v_isSharedCheck_6240_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6119_);
                        v___x_6121_ = lean_box(0);
                        v_isShared_6122_ = v_isSharedCheck_6240_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_6110_);
                    lean_dec_ref(v_code_6109_);
                    return v___x_6119_;
                }
            }
            1 => match lean_obj_tag(v_code_6109_) {
                0 => {
                    lean_del_object(v___x_6121_);
                    v_decl_6123_ = lean_ctor_get(v_code_6109_, 0);
                    v_k_6124_ = lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6138_ = (!lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6138_ == 0 {
                        v___x_6126_ = v_code_6109_;
                        v_isShared_6127_ = v_isSharedCheck_6138_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_k_6124_);
                        lean_inc(v_decl_6123_);
                        lean_dec(v_code_6109_);
                        v___x_6126_ = lean_box(0);
                        v_isShared_6127_ = v_isSharedCheck_6138_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_6121_);
                    v_decl_6139_ = lean_ctor_get(v_code_6109_, 0);
                    v_k_6140_ = lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6156_ = (!lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6156_ == 0 {
                        v___x_6142_ = v_code_6109_;
                        v_isShared_6143_ = v_isSharedCheck_6156_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_k_6140_);
                        lean_inc(v_decl_6139_);
                        lean_dec(v_code_6109_);
                        v___x_6142_ = lean_box(0);
                        v_isShared_6143_ = v_isSharedCheck_6156_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    lean_del_object(v___x_6121_);
                    v_decl_6157_ = lean_ctor_get(v_code_6109_, 0);
                    v_k_6158_ = lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6172_ = (!lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6172_ == 0 {
                        v___x_6160_ = v_code_6109_;
                        v_isShared_6161_ = v_isSharedCheck_6172_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_k_6158_);
                        lean_inc(v_decl_6157_);
                        lean_dec(v_code_6109_);
                        v___x_6160_ = lean_box(0);
                        v_isShared_6161_ = v_isSharedCheck_6172_;
                        state = 6;
                        continue;
                    }
                }
                3 => {
                    lean_del_object(v___x_6121_);
                    v_fvarId_6173_ = lean_ctor_get(v_code_6109_, 0);
                    v_args_6174_ = lean_ctor_get(v_code_6109_, 1);
                    v_isSharedCheck_6231_ = (!lean_is_exclusive(v_code_6109_)) as u8;
                    if v_isSharedCheck_6231_ == 0 {
                        v___x_6176_ = v_code_6109_;
                        v_isShared_6177_ = v_isSharedCheck_6231_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_args_6174_);
                        lean_inc(v_fvarId_6173_);
                        lean_dec(v_code_6109_);
                        v___x_6176_ = lean_box(0);
                        v_isShared_6177_ = v_isSharedCheck_6231_;
                        state = 8;
                        continue;
                    }
                }
                4 => {
                    lean_del_object(v___x_6121_);
                    v_cases_6232_ = lean_ctor_get(v_code_6109_, 0);
                    lean_inc_ref(v_cases_6232_);
                    lean_dec_ref_known(v_code_6109_, 1);
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
                    lean_dec_ref(v_a_6110_);
                    return v___x_6233_;
                }
                5 => {
                    lean_del_object(v___x_6121_);
                    v_fvarId_6234_ = lean_ctor_get(v_code_6109_, 0);
                    lean_inc(v_fvarId_6234_);
                    lean_dec_ref_known(v_code_6109_, 1);
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
                    lean_dec_ref(v_a_6110_);
                    return v___x_6235_;
                }
                _ => {
                    lean_dec_ref_known(v_code_6109_, 1);
                    lean_dec_ref(v_a_6110_);
                    v___x_6236_ = lean_box(0);
                    if v_isShared_6122_ == 0 {
                        lean_ctor_set(v___x_6121_, 0, v___x_6236_);
                        v___x_6238_ = v___x_6121_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_6239_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6239_, 0, v___x_6236_);
                        v___x_6238_ = v_reuseFailAlloc_6239_;
                        state = 15;
                        continue;
                    }
                }
            },
            2 => {
                lean_inc_ref(v_decl_6123_);
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
                if lean_obj_tag(v___x_6128_) == 0 {
                    lean_dec_ref_known(v___x_6128_, 1);
                    v_fvarId_6129_ = lean_ctor_get(v_decl_6123_, 0);
                    lean_inc_n(v_fvarId_6129_, 2);
                    lean_dec_ref(v_decl_6123_);
                    v___x_6130_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6129_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if lean_obj_tag(v___x_6130_) == 0 {
                        lean_dec_ref_known(v___x_6130_, 1);
                        v_jps_6131_ = lean_ctor_get(v_a_6110_, 0);
                        lean_inc(v_jps_6131_);
                        v_vars_6132_ = lean_ctor_get(v_a_6110_, 1);
                        lean_inc(v_vars_6132_);
                        lean_dec_ref(v_a_6110_);
                        v___x_6133_ = l_Lean_FVarIdSet_insert(v_vars_6132_, v_fvarId_6129_);
                        if v_isShared_6127_ == 0 {
                            lean_ctor_set(v___x_6126_, 1, v___x_6133_);
                            lean_ctor_set(v___x_6126_, 0, v_jps_6131_);
                            v___x_6135_ = v___x_6126_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6137_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_jps_6131_);
                            lean_ctor_set(v_reuseFailAlloc_6137_, 1, v___x_6133_);
                            v___x_6135_ = v_reuseFailAlloc_6137_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_fvarId_6129_);
                        lean_del_object(v___x_6126_);
                        lean_dec_ref(v_k_6124_);
                        lean_dec_ref(v_a_6110_);
                        return v___x_6130_;
                    }
                } else {
                    lean_del_object(v___x_6126_);
                    lean_dec_ref(v_k_6124_);
                    lean_dec_ref(v_decl_6123_);
                    lean_dec_ref(v_a_6110_);
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
                v_jps_6144_ = lean_ctor_get(v_a_6110_, 0);
                lean_inc(v_jps_6144_);
                v_vars_6145_ = lean_ctor_get(v_a_6110_, 1);
                lean_inc_n(v_vars_6145_, 2);
                lean_dec_ref(v_a_6110_);
                v___x_6146_ = lean_box(1);
                if v_isShared_6143_ == 0 {
                    lean_ctor_set_tag(v___x_6142_, 0);
                    lean_ctor_set(v___x_6142_, 1, v_vars_6145_);
                    lean_ctor_set(v___x_6142_, 0, v___x_6146_);
                    v___x_6148_ = v___x_6142_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6155_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6155_, 0, v___x_6146_);
                    lean_ctor_set(v_reuseFailAlloc_6155_, 1, v_vars_6145_);
                    v___x_6148_ = v_reuseFailAlloc_6155_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v_decl_6139_);
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
                lean_dec_ref(v___x_6148_);
                if lean_obj_tag(v___x_6149_) == 0 {
                    lean_dec_ref_known(v___x_6149_, 1);
                    v_fvarId_6150_ = lean_ctor_get(v_decl_6139_, 0);
                    lean_inc_n(v_fvarId_6150_, 2);
                    lean_dec_ref(v_decl_6139_);
                    v___x_6151_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6150_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if lean_obj_tag(v___x_6151_) == 0 {
                        lean_dec_ref_known(v___x_6151_, 1);
                        v___x_6152_ = l_Lean_FVarIdSet_insert(v_vars_6145_, v_fvarId_6150_);
                        v___x_6153_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_6153_, 0, v_jps_6144_);
                        lean_ctor_set(v___x_6153_, 1, v___x_6152_);
                        v_code_6109_ = v_k_6140_;
                        v_a_6110_ = v___x_6153_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_fvarId_6150_);
                        lean_dec(v_vars_6145_);
                        lean_dec(v_jps_6144_);
                        lean_dec_ref(v_k_6140_);
                        return v___x_6151_;
                    }
                } else {
                    lean_dec(v_vars_6145_);
                    lean_dec(v_jps_6144_);
                    lean_dec_ref(v_k_6140_);
                    lean_dec_ref(v_decl_6139_);
                    return v___x_6149_;
                }
            }
            6 => {
                lean_inc_ref(v_decl_6157_);
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
                if lean_obj_tag(v___x_6162_) == 0 {
                    lean_dec_ref_known(v___x_6162_, 1);
                    v_fvarId_6163_ = lean_ctor_get(v_decl_6157_, 0);
                    lean_inc_n(v_fvarId_6163_, 2);
                    lean_dec_ref(v_decl_6157_);
                    v___x_6164_ = l_Lean_Compiler_LCNF_Check_Pure_addFVarId___redArg(
                        v_fvarId_6163_,
                        v_a_6111_,
                        v_a_6113_,
                        v_a_6114_,
                        v_a_6115_,
                        v_a_6116_,
                    );
                    if lean_obj_tag(v___x_6164_) == 0 {
                        lean_dec_ref_known(v___x_6164_, 1);
                        v_jps_6165_ = lean_ctor_get(v_a_6110_, 0);
                        lean_inc(v_jps_6165_);
                        v_vars_6166_ = lean_ctor_get(v_a_6110_, 1);
                        lean_inc(v_vars_6166_);
                        lean_dec_ref(v_a_6110_);
                        v___x_6167_ = l_Lean_FVarIdSet_insert(v_jps_6165_, v_fvarId_6163_);
                        if v_isShared_6161_ == 0 {
                            lean_ctor_set_tag(v___x_6160_, 0);
                            lean_ctor_set(v___x_6160_, 1, v_vars_6166_);
                            lean_ctor_set(v___x_6160_, 0, v___x_6167_);
                            v___x_6169_ = v___x_6160_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_6171_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6171_, 0, v___x_6167_);
                            lean_ctor_set(v_reuseFailAlloc_6171_, 1, v_vars_6166_);
                            v___x_6169_ = v_reuseFailAlloc_6171_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_fvarId_6163_);
                        lean_del_object(v___x_6160_);
                        lean_dec_ref(v_k_6158_);
                        lean_dec_ref(v_a_6110_);
                        return v___x_6164_;
                    }
                } else {
                    lean_del_object(v___x_6160_);
                    lean_dec_ref(v_k_6158_);
                    lean_dec_ref(v_decl_6157_);
                    lean_dec_ref(v_a_6110_);
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
                lean_inc(v_fvarId_6173_);
                v___x_6188_ = l_Lean_Compiler_LCNF_Check_Pure_checkJpInScope___redArg(
                    v_fvarId_6173_,
                    v_a_6110_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                if lean_obj_tag(v___x_6188_) == 0 {
                    v_isSharedCheck_6229_ = (!lean_is_exclusive(v___x_6188_)) as u8;
                    if v_isSharedCheck_6229_ == 0 {
                        v_unused_6230_ = lean_ctor_get(v___x_6188_, 0);
                        lean_dec(v_unused_6230_);
                        v___x_6190_ = v___x_6188_;
                        v_isShared_6191_ = v_isSharedCheck_6229_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec(v___x_6188_);
                        v___x_6190_ = lean_box(0);
                        v_isShared_6191_ = v_isSharedCheck_6229_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6176_);
                    lean_dec_ref(v_args_6174_);
                    lean_dec(v_fvarId_6173_);
                    lean_dec_ref(v_a_6110_);
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
                lean_dec_ref(v___y_6179_);
                return v___x_6187_;
            }
            10 => {
                v___x_6192_ = 0;
                lean_inc(v_fvarId_6173_);
                v___x_6193_ = l_Lean_Compiler_LCNF_getFunDecl(
                    v___x_6192_,
                    v_fvarId_6173_,
                    v_a_6113_,
                    v_a_6114_,
                    v_a_6115_,
                    v_a_6116_,
                );
                if lean_obj_tag(v___x_6193_) == 0 {
                    v_a_6194_ = lean_ctor_get(v___x_6193_, 0);
                    lean_inc(v_a_6194_);
                    lean_dec_ref_known(v___x_6193_, 1);
                    v___x_6195_ = l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(v_a_6194_);
                    v___x_6196_ = lean_array_get_size(v_args_6174_);
                    v___x_6197_ = lean_nat_dec_eq(v___x_6195_, v___x_6196_);
                    if v___x_6197_ == 0 {
                        v_binderName_6198_ = lean_ctor_get(v_a_6194_, 1);
                        lean_inc(v_binderName_6198_);
                        lean_dec(v_a_6194_);
                        v___x_6199_ = lean_obj_once(
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
                            lean_ctor_set_tag(v___x_6176_, 7);
                            lean_ctor_set(v___x_6176_, 1, v___x_6200_);
                            lean_ctor_set(v___x_6176_, 0, v___x_6199_);
                            v___x_6202_ = v___x_6176_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_6220_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6220_, 0, v___x_6199_);
                            lean_ctor_set(v_reuseFailAlloc_6220_, 1, v___x_6200_);
                            v___x_6202_ = v_reuseFailAlloc_6220_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6195_);
                        lean_dec(v_a_6194_);
                        lean_del_object(v___x_6190_);
                        lean_del_object(v___x_6176_);
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
                    lean_del_object(v___x_6190_);
                    lean_del_object(v___x_6176_);
                    lean_dec_ref(v_args_6174_);
                    lean_dec(v_fvarId_6173_);
                    lean_dec_ref(v_a_6110_);
                    v_a_6221_ = lean_ctor_get(v___x_6193_, 0);
                    v_isSharedCheck_6228_ = (!lean_is_exclusive(v___x_6193_)) as u8;
                    if v_isSharedCheck_6228_ == 0 {
                        v___x_6223_ = v___x_6193_;
                        v_isShared_6224_ = v_isSharedCheck_6228_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_6221_);
                        lean_dec(v___x_6193_);
                        v___x_6223_ = lean_box(0);
                        v_isShared_6224_ = v_isSharedCheck_6228_;
                        state = 13;
                        continue;
                    }
                }
            }
            11 => {
                v___x_6203_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__4_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__4,
                );
                v___x_6204_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6204_, 0, v___x_6202_);
                lean_ctor_set(v___x_6204_, 1, v___x_6203_);
                v___x_6205_ = l_Nat_reprFast(v___x_6195_);
                if v_isShared_6191_ == 0 {
                    lean_ctor_set_tag(v___x_6190_, 3);
                    lean_ctor_set(v___x_6190_, 0, v___x_6205_);
                    v___x_6207_ = v___x_6190_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6219_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6219_, 0, v___x_6205_);
                    v___x_6207_ = v_reuseFailAlloc_6219_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6208_ = l_Lean_MessageData_ofFormat(v___x_6207_);
                v___x_6209_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6209_, 0, v___x_6204_);
                lean_ctor_set(v___x_6209_, 1, v___x_6208_);
                v___x_6210_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__6_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__6,
                );
                v___x_6211_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6211_, 0, v___x_6209_);
                lean_ctor_set(v___x_6211_, 1, v___x_6210_);
                v___x_6212_ = l_Nat_reprFast(v___x_6196_);
                v___x_6213_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6213_, 0, v___x_6212_);
                v___x_6214_ = l_Lean_MessageData_ofFormat(v___x_6213_);
                v___x_6215_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6215_, 0, v___x_6211_);
                lean_ctor_set(v___x_6215_, 1, v___x_6214_);
                v___x_6216_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_check___closed__8_once),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_check___closed__8,
                );
                v___x_6217_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6217_, 0, v___x_6215_);
                lean_ctor_set(v___x_6217_, 1, v___x_6216_);
                v___x_6218_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Check_Pure_checkFVar_spec__1___redArg(v___x_6217_, v_a_6113_, v_a_6114_, v_a_6115_, v_a_6116_);
                if lean_obj_tag(v___x_6218_) == 0 {
                    lean_dec_ref_known(v___x_6218_, 1);
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
                    lean_dec_ref(v_args_6174_);
                    lean_dec(v_fvarId_6173_);
                    lean_dec_ref(v_a_6110_);
                    return v___x_6218_;
                }
            }
            13 => {
                if v_isShared_6224_ == 0 {
                    v___x_6226_ = v___x_6223_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_a_6221_);
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
    mut v_value_6242_: *mut LeanObject,
    mut v___x_6243_: *mut LeanObject,
    mut v___y_6244_: *mut LeanObject,
    mut v___y_6245_: *mut LeanObject,
    mut v___y_6246_: *mut LeanObject,
    mut v___y_6247_: *mut LeanObject,
    mut v___y_6248_: *mut LeanObject,
    mut v___y_6249_: *mut LeanObject,
    mut v___y_6250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6259_: u8 = 0;
    let mut v_unused_6260_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_6252_) == 0 {
                    v_isSharedCheck_6259_ = (!lean_is_exclusive(v___x_6252_)) as u8;
                    if v_isSharedCheck_6259_ == 0 {
                        v_unused_6260_ = lean_ctor_get(v___x_6252_, 0);
                        lean_dec(v_unused_6260_);
                        v___x_6254_ = v___x_6252_;
                        v_isShared_6255_ = v_isSharedCheck_6259_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6252_);
                        v___x_6254_ = lean_box(0);
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
                    lean_ctor_set(v___x_6254_, 0, v___x_6243_);
                    v___x_6257_ = v___x_6254_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6258_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6258_, 0, v___x_6243_);
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
    mut v_value_6261_: *mut LeanObject,
    mut v___x_6262_: *mut LeanObject,
    mut v___y_6263_: *mut LeanObject,
    mut v___y_6264_: *mut LeanObject,
    mut v___y_6265_: *mut LeanObject,
    mut v___y_6266_: *mut LeanObject,
    mut v___y_6267_: *mut LeanObject,
    mut v___y_6268_: *mut LeanObject,
    mut v___y_6269_: *mut LeanObject,
    mut v___y_6270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6271_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6269_);
    lean_dec_ref(v___y_6268_);
    lean_dec(v___y_6267_);
    lean_dec_ref(v___y_6266_);
    lean_dec_ref(v___y_6265_);
    lean_dec(v___y_6264_);
    return v_res_6271_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkCases___boxed(
    mut v_c_6272_: *mut LeanObject,
    mut v_a_6273_: *mut LeanObject,
    mut v_a_6274_: *mut LeanObject,
    mut v_a_6275_: *mut LeanObject,
    mut v_a_6276_: *mut LeanObject,
    mut v_a_6277_: *mut LeanObject,
    mut v_a_6278_: *mut LeanObject,
    mut v_a_6279_: *mut LeanObject,
    mut v_a_6280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6281_: *mut LeanObject = core::ptr::null_mut();
    v_res_6281_ = l_Lean_Compiler_LCNF_Check_Pure_checkCases(
        v_c_6272_, v_a_6273_, v_a_6274_, v_a_6275_, v_a_6276_, v_a_6277_, v_a_6278_, v_a_6279_,
    );
    lean_dec(v_a_6279_);
    lean_dec_ref(v_a_6278_);
    lean_dec(v_a_6277_);
    lean_dec_ref(v_a_6276_);
    lean_dec_ref(v_a_6275_);
    lean_dec(v_a_6274_);
    lean_dec_ref(v_a_6273_);
    return v_res_6281_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDecl___boxed(
    mut v_funDecl_6282_: *mut LeanObject,
    mut v_a_6283_: *mut LeanObject,
    mut v_a_6284_: *mut LeanObject,
    mut v_a_6285_: *mut LeanObject,
    mut v_a_6286_: *mut LeanObject,
    mut v_a_6287_: *mut LeanObject,
    mut v_a_6288_: *mut LeanObject,
    mut v_a_6289_: *mut LeanObject,
    mut v_a_6290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6291_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6289_);
    lean_dec_ref(v_a_6288_);
    lean_dec(v_a_6287_);
    lean_dec_ref(v_a_6286_);
    lean_dec_ref(v_a_6285_);
    lean_dec(v_a_6284_);
    lean_dec_ref(v_a_6283_);
    return v_res_6291_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_check___boxed(
    mut v_code_6292_: *mut LeanObject,
    mut v_a_6293_: *mut LeanObject,
    mut v_a_6294_: *mut LeanObject,
    mut v_a_6295_: *mut LeanObject,
    mut v_a_6296_: *mut LeanObject,
    mut v_a_6297_: *mut LeanObject,
    mut v_a_6298_: *mut LeanObject,
    mut v_a_6299_: *mut LeanObject,
    mut v_a_6300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6301_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6299_);
    lean_dec_ref(v_a_6298_);
    lean_dec(v_a_6297_);
    lean_dec_ref(v_a_6296_);
    lean_dec_ref(v_a_6295_);
    lean_dec(v_a_6294_);
    return v_res_6301_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed(
    mut v_declName_6302_: *mut LeanObject,
    mut v_params_6303_: *mut LeanObject,
    mut v_type_6304_: *mut LeanObject,
    mut v_value_6305_: *mut LeanObject,
    mut v_a_6306_: *mut LeanObject,
    mut v_a_6307_: *mut LeanObject,
    mut v_a_6308_: *mut LeanObject,
    mut v_a_6309_: *mut LeanObject,
    mut v_a_6310_: *mut LeanObject,
    mut v_a_6311_: *mut LeanObject,
    mut v_a_6312_: *mut LeanObject,
    mut v_a_6313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6314_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6312_);
    lean_dec_ref(v_a_6311_);
    lean_dec(v_a_6310_);
    lean_dec_ref(v_a_6309_);
    lean_dec_ref(v_a_6308_);
    lean_dec(v_a_6307_);
    lean_dec_ref(v_a_6306_);
    return v_res_6314_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5___boxed(
    mut v_typeName_6315_: *mut LeanObject,
    mut v_as_6316_: *mut LeanObject,
    mut v_sz_6317_: *mut LeanObject,
    mut v_i_6318_: *mut LeanObject,
    mut v_b_6319_: *mut LeanObject,
    mut v___y_6320_: *mut LeanObject,
    mut v___y_6321_: *mut LeanObject,
    mut v___y_6322_: *mut LeanObject,
    mut v___y_6323_: *mut LeanObject,
    mut v___y_6324_: *mut LeanObject,
    mut v___y_6325_: *mut LeanObject,
    mut v___y_6326_: *mut LeanObject,
    mut v___y_6327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6328_: usize = 0;
    let mut v_i_boxed_6329_: usize = 0;
    let mut v_res_6330_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6328_ = lean_unbox_usize(v_sz_6317_);
    lean_dec(v_sz_6317_);
    v_i_boxed_6329_ = lean_unbox_usize(v_i_6318_);
    lean_dec(v_i_6318_);
    v_res_6330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__5(v_typeName_6315_, v_as_6316_, v_sz_boxed_6328_, v_i_boxed_6329_, v_b_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_, v___y_6324_, v___y_6325_, v___y_6326_);
    lean_dec(v___y_6326_);
    lean_dec_ref(v___y_6325_);
    lean_dec(v___y_6324_);
    lean_dec_ref(v___y_6323_);
    lean_dec_ref(v___y_6322_);
    lean_dec(v___y_6321_);
    lean_dec_ref(v___y_6320_);
    lean_dec_ref(v_as_6316_);
    return v_res_6330_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(
    mut v_as_6331_: *mut LeanObject,
    mut v_i_6332_: usize,
    mut v_stop_6333_: usize,
    mut v_b_6334_: *mut LeanObject,
    mut v___y_6335_: *mut LeanObject,
    mut v___y_6336_: *mut LeanObject,
    mut v___y_6337_: *mut LeanObject,
    mut v___y_6338_: *mut LeanObject,
    mut v___y_6339_: *mut LeanObject,
    mut v___y_6340_: *mut LeanObject,
    mut v___y_6341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    v___x_6343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___redArg(v_as_6331_, v_i_6332_, v_stop_6333_, v_b_6334_, v___y_6336_, v___y_6338_, v___y_6339_, v___y_6340_, v___y_6341_);
    return v___x_6343_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1___boxed(
    mut v_as_6344_: *mut LeanObject,
    mut v_i_6345_: *mut LeanObject,
    mut v_stop_6346_: *mut LeanObject,
    mut v_b_6347_: *mut LeanObject,
    mut v___y_6348_: *mut LeanObject,
    mut v___y_6349_: *mut LeanObject,
    mut v___y_6350_: *mut LeanObject,
    mut v___y_6351_: *mut LeanObject,
    mut v___y_6352_: *mut LeanObject,
    mut v___y_6353_: *mut LeanObject,
    mut v___y_6354_: *mut LeanObject,
    mut v___y_6355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6356_: usize = 0;
    let mut v_stop_boxed_6357_: usize = 0;
    let mut v_res_6358_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6356_ = lean_unbox_usize(v_i_6345_);
    lean_dec(v_i_6345_);
    v_stop_boxed_6357_ = lean_unbox_usize(v_stop_6346_);
    lean_dec(v_stop_6346_);
    v_res_6358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore_spec__1(v_as_6344_, v_i_boxed_6356_, v_stop_boxed_6357_, v_b_6347_, v___y_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_);
    lean_dec(v___y_6354_);
    lean_dec_ref(v___y_6353_);
    lean_dec(v___y_6352_);
    lean_dec_ref(v___y_6351_);
    lean_dec_ref(v___y_6350_);
    lean_dec(v___y_6349_);
    lean_dec_ref(v___y_6348_);
    lean_dec_ref(v_as_6344_);
    return v_res_6358_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4(
    mut v_00_u03b1_6359_: *mut LeanObject,
    mut v_constName_6360_: *mut LeanObject,
    mut v___y_6361_: *mut LeanObject,
    mut v___y_6362_: *mut LeanObject,
    mut v___y_6363_: *mut LeanObject,
    mut v___y_6364_: *mut LeanObject,
    mut v___y_6365_: *mut LeanObject,
    mut v___y_6366_: *mut LeanObject,
    mut v___y_6367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    v___x_6369_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___redArg(v_constName_6360_, v___y_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_, v___y_6367_);
    return v___x_6369_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4___boxed(
    mut v_00_u03b1_6370_: *mut LeanObject,
    mut v_constName_6371_: *mut LeanObject,
    mut v___y_6372_: *mut LeanObject,
    mut v___y_6373_: *mut LeanObject,
    mut v___y_6374_: *mut LeanObject,
    mut v___y_6375_: *mut LeanObject,
    mut v___y_6376_: *mut LeanObject,
    mut v___y_6377_: *mut LeanObject,
    mut v___y_6378_: *mut LeanObject,
    mut v___y_6379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6380_: *mut LeanObject = core::ptr::null_mut();
    v_res_6380_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4(v_00_u03b1_6370_, v_constName_6371_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_);
    lean_dec(v___y_6378_);
    lean_dec_ref(v___y_6377_);
    lean_dec(v___y_6376_);
    lean_dec_ref(v___y_6375_);
    lean_dec_ref(v___y_6374_);
    lean_dec(v___y_6373_);
    lean_dec_ref(v___y_6372_);
    return v_res_6380_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6(
    mut v_00_u03b1_6381_: *mut LeanObject,
    mut v_ref_6382_: *mut LeanObject,
    mut v_constName_6383_: *mut LeanObject,
    mut v___y_6384_: *mut LeanObject,
    mut v___y_6385_: *mut LeanObject,
    mut v___y_6386_: *mut LeanObject,
    mut v___y_6387_: *mut LeanObject,
    mut v___y_6388_: *mut LeanObject,
    mut v___y_6389_: *mut LeanObject,
    mut v___y_6390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    v___x_6392_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___redArg(v_ref_6382_, v_constName_6383_, v___y_6384_, v___y_6385_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
    return v___x_6392_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6___boxed(
    mut v_00_u03b1_6393_: *mut LeanObject,
    mut v_ref_6394_: *mut LeanObject,
    mut v_constName_6395_: *mut LeanObject,
    mut v___y_6396_: *mut LeanObject,
    mut v___y_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
    mut v___y_6402_: *mut LeanObject,
    mut v___y_6403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6404_: *mut LeanObject = core::ptr::null_mut();
    v_res_6404_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6(v_00_u03b1_6393_, v_ref_6394_, v_constName_6395_, v___y_6396_, v___y_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_);
    lean_dec(v___y_6402_);
    lean_dec_ref(v___y_6401_);
    lean_dec(v___y_6400_);
    lean_dec_ref(v___y_6399_);
    lean_dec_ref(v___y_6398_);
    lean_dec(v___y_6397_);
    lean_dec_ref(v___y_6396_);
    lean_dec(v_ref_6394_);
    return v_res_6404_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8(
    mut v_00_u03b1_6405_: *mut LeanObject,
    mut v_ref_6406_: *mut LeanObject,
    mut v_msg_6407_: *mut LeanObject,
    mut v_declHint_6408_: *mut LeanObject,
    mut v___y_6409_: *mut LeanObject,
    mut v___y_6410_: *mut LeanObject,
    mut v___y_6411_: *mut LeanObject,
    mut v___y_6412_: *mut LeanObject,
    mut v___y_6413_: *mut LeanObject,
    mut v___y_6414_: *mut LeanObject,
    mut v___y_6415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    v___x_6417_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___redArg(v_ref_6406_, v_msg_6407_, v_declHint_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_);
    return v___x_6417_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_6418_: *mut LeanObject,
    mut v_ref_6419_: *mut LeanObject,
    mut v_msg_6420_: *mut LeanObject,
    mut v_declHint_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
    mut v___y_6426_: *mut LeanObject,
    mut v___y_6427_: *mut LeanObject,
    mut v___y_6428_: *mut LeanObject,
    mut v___y_6429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6430_: *mut LeanObject = core::ptr::null_mut();
    v_res_6430_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8(v_00_u03b1_6418_, v_ref_6419_, v_msg_6420_, v_declHint_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_);
    lean_dec(v___y_6428_);
    lean_dec_ref(v___y_6427_);
    lean_dec(v___y_6426_);
    lean_dec_ref(v___y_6425_);
    lean_dec_ref(v___y_6424_);
    lean_dec(v___y_6423_);
    lean_dec_ref(v___y_6422_);
    lean_dec(v_ref_6419_);
    return v_res_6430_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10(
    mut v_msg_6431_: *mut LeanObject,
    mut v_declHint_6432_: *mut LeanObject,
    mut v___y_6433_: *mut LeanObject,
    mut v___y_6434_: *mut LeanObject,
    mut v___y_6435_: *mut LeanObject,
    mut v___y_6436_: *mut LeanObject,
    mut v___y_6437_: *mut LeanObject,
    mut v___y_6438_: *mut LeanObject,
    mut v___y_6439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    v___x_6441_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___redArg(v_msg_6431_, v_declHint_6432_, v___y_6439_);
    return v___x_6441_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10___boxed(
    mut v_msg_6442_: *mut LeanObject,
    mut v_declHint_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
    mut v___y_6448_: *mut LeanObject,
    mut v___y_6449_: *mut LeanObject,
    mut v___y_6450_: *mut LeanObject,
    mut v___y_6451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6452_: *mut LeanObject = core::ptr::null_mut();
    v_res_6452_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__9_spec__10(v_msg_6442_, v_declHint_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_);
    lean_dec(v___y_6450_);
    lean_dec_ref(v___y_6449_);
    lean_dec(v___y_6448_);
    lean_dec_ref(v___y_6447_);
    lean_dec_ref(v___y_6446_);
    lean_dec(v___y_6445_);
    lean_dec_ref(v___y_6444_);
    return v_res_6452_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10(
    mut v_00_u03b1_6453_: *mut LeanObject,
    mut v_ref_6454_: *mut LeanObject,
    mut v_msg_6455_: *mut LeanObject,
    mut v___y_6456_: *mut LeanObject,
    mut v___y_6457_: *mut LeanObject,
    mut v___y_6458_: *mut LeanObject,
    mut v___y_6459_: *mut LeanObject,
    mut v___y_6460_: *mut LeanObject,
    mut v___y_6461_: *mut LeanObject,
    mut v___y_6462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    v___x_6464_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___redArg(v_ref_6454_, v_msg_6455_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_);
    return v___x_6464_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10___boxed(
    mut v_00_u03b1_6465_: *mut LeanObject,
    mut v_ref_6466_: *mut LeanObject,
    mut v_msg_6467_: *mut LeanObject,
    mut v___y_6468_: *mut LeanObject,
    mut v___y_6469_: *mut LeanObject,
    mut v___y_6470_: *mut LeanObject,
    mut v___y_6471_: *mut LeanObject,
    mut v___y_6472_: *mut LeanObject,
    mut v___y_6473_: *mut LeanObject,
    mut v___y_6474_: *mut LeanObject,
    mut v___y_6475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6476_: *mut LeanObject = core::ptr::null_mut();
    v_res_6476_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_checkCases_spec__4_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_6465_, v_ref_6466_, v_msg_6467_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_);
    lean_dec(v___y_6474_);
    lean_dec_ref(v___y_6473_);
    lean_dec(v___y_6472_);
    lean_dec_ref(v___y_6471_);
    lean_dec_ref(v___y_6470_);
    lean_dec(v___y_6469_);
    lean_dec_ref(v___y_6468_);
    lean_dec(v_ref_6466_);
    return v_res_6476_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    v___x_6479_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6479_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    v___x_6480_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1_once),
        _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__1,
    );
    v___x_6481_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6481_, 0, v___x_6480_);
    return v___x_6481_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut LeanObject = core::ptr::null_mut();
    v___x_6482_ = lean_box(1);
    v___x_6483_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_Check_Pure_isCtorParam_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_6484_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2_once),
        _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__2,
    );
    v___x_6485_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6485_, 0, v___x_6484_);
    lean_ctor_set(v___x_6485_, 1, v___x_6483_);
    lean_ctor_set(v___x_6485_, 2, v___x_6482_);
    return v___x_6485_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
    mut v_x_6486_: *mut LeanObject,
    mut v_a_6487_: *mut LeanObject,
    mut v_a_6488_: *mut LeanObject,
    mut v_a_6489_: *mut LeanObject,
    mut v_a_6490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6500_: u8 = 0;
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6492_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v___x_6493_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__0;
                v___x_6494_ = lean_st_mk_ref(v___x_6492_);
                v___x_6495_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Check_Pure_run___redArg___closed__3,
                );
                lean_inc(v_a_6490_);
                lean_inc_ref(v_a_6489_);
                lean_inc(v_a_6488_);
                lean_inc_ref(v_a_6487_);
                lean_inc(v___x_6494_);
                v___x_6496_ = lean_apply_8(
                    v_x_6486_,
                    v___x_6493_,
                    v___x_6494_,
                    v___x_6495_,
                    v_a_6487_,
                    v_a_6488_,
                    v_a_6489_,
                    v_a_6490_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6496_) == 0 {
                    v_a_6497_ = lean_ctor_get(v___x_6496_, 0);
                    v_isSharedCheck_6505_ = (!lean_is_exclusive(v___x_6496_)) as u8;
                    if v_isSharedCheck_6505_ == 0 {
                        v___x_6499_ = v___x_6496_;
                        v_isShared_6500_ = v_isSharedCheck_6505_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6497_);
                        lean_dec(v___x_6496_);
                        v___x_6499_ = lean_box(0);
                        v_isShared_6500_ = v_isSharedCheck_6505_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6494_);
                    return v___x_6496_;
                }
            }
            1 => {
                v___x_6501_ = lean_st_ref_get(v___x_6494_);
                lean_dec(v___x_6494_);
                lean_dec(v___x_6501_);
                if v_isShared_6500_ == 0 {
                    v___x_6503_ = v___x_6499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6504_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6497_);
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
    mut v_x_6506_: *mut LeanObject,
    mut v_a_6507_: *mut LeanObject,
    mut v_a_6508_: *mut LeanObject,
    mut v_a_6509_: *mut LeanObject,
    mut v_a_6510_: *mut LeanObject,
    mut v_a_6511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6512_: *mut LeanObject = core::ptr::null_mut();
    v_res_6512_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
        v_x_6506_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_,
    );
    lean_dec(v_a_6510_);
    lean_dec_ref(v_a_6509_);
    lean_dec(v_a_6508_);
    lean_dec_ref(v_a_6507_);
    return v_res_6512_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run(
    mut v_00_u03b1_6513_: *mut LeanObject,
    mut v_x_6514_: *mut LeanObject,
    mut v_a_6515_: *mut LeanObject,
    mut v_a_6516_: *mut LeanObject,
    mut v_a_6517_: *mut LeanObject,
    mut v_a_6518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    v___x_6520_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
        v_x_6514_, v_a_6515_, v_a_6516_, v_a_6517_, v_a_6518_,
    );
    return v___x_6520_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Check_Pure_run___boxed(
    mut v_00_u03b1_6521_: *mut LeanObject,
    mut v_x_6522_: *mut LeanObject,
    mut v_a_6523_: *mut LeanObject,
    mut v_a_6524_: *mut LeanObject,
    mut v_a_6525_: *mut LeanObject,
    mut v_a_6526_: *mut LeanObject,
    mut v_a_6527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6528_: *mut LeanObject = core::ptr::null_mut();
    v_res_6528_ = l_Lean_Compiler_LCNF_Check_Pure_run(
        v_00_u03b1_6521_,
        v_x_6522_,
        v_a_6523_,
        v_a_6524_,
        v_a_6525_,
        v_a_6526_,
    );
    lean_dec(v_a_6526_);
    lean_dec_ref(v_a_6525_);
    lean_dec(v_a_6524_);
    lean_dec_ref(v_a_6523_);
    return v_res_6528_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(
    mut v_f_6529_: *mut LeanObject,
    mut v_v_6530_: *mut LeanObject,
    mut v___y_6531_: *mut LeanObject,
    mut v___y_6532_: *mut LeanObject,
    mut v___y_6533_: *mut LeanObject,
    mut v___y_6534_: *mut LeanObject,
    mut v___y_6535_: *mut LeanObject,
    mut v___y_6536_: *mut LeanObject,
    mut v___y_6537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6543_: u8 = 0;
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6548_: u8 = 0;
    let mut v_unused_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_6530_) == 0 {
                    v_code_6539_ = lean_ctor_get(v_v_6530_, 0);
                    lean_inc_ref(v_code_6539_);
                    lean_dec_ref_known(v_v_6530_, 1);
                    lean_inc(v___y_6537_);
                    lean_inc_ref(v___y_6536_);
                    lean_inc(v___y_6535_);
                    lean_inc_ref(v___y_6534_);
                    lean_inc_ref(v___y_6533_);
                    lean_inc(v___y_6532_);
                    lean_inc_ref(v___y_6531_);
                    v___x_6540_ = lean_apply_9(
                        v_f_6529_,
                        v_code_6539_,
                        v___y_6531_,
                        v___y_6532_,
                        v___y_6533_,
                        v___y_6534_,
                        v___y_6535_,
                        v___y_6536_,
                        v___y_6537_,
                        lean_box(0),
                    );
                    return v___x_6540_;
                } else {
                    lean_dec_ref(v_f_6529_);
                    v_isSharedCheck_6548_ = (!lean_is_exclusive(v_v_6530_)) as u8;
                    if v_isSharedCheck_6548_ == 0 {
                        v_unused_6549_ = lean_ctor_get(v_v_6530_, 0);
                        lean_dec(v_unused_6549_);
                        v___x_6542_ = v_v_6530_;
                        v_isShared_6543_ = v_isSharedCheck_6548_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_6530_);
                        v___x_6542_ = lean_box(0);
                        v_isShared_6543_ = v_isSharedCheck_6548_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6544_ = lean_box(0);
                if v_isShared_6543_ == 0 {
                    lean_ctor_set_tag(v___x_6542_, 0);
                    lean_ctor_set(v___x_6542_, 0, v___x_6544_);
                    v___x_6546_ = v___x_6542_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6547_, 0, v___x_6544_);
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
    mut v_f_6550_: *mut LeanObject,
    mut v_v_6551_: *mut LeanObject,
    mut v___y_6552_: *mut LeanObject,
    mut v___y_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
    mut v___y_6556_: *mut LeanObject,
    mut v___y_6557_: *mut LeanObject,
    mut v___y_6558_: *mut LeanObject,
    mut v___y_6559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6560_: *mut LeanObject = core::ptr::null_mut();
    v_res_6560_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(v_f_6550_, v_v_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
    lean_dec(v___y_6558_);
    lean_dec_ref(v___y_6557_);
    lean_dec(v___y_6556_);
    lean_dec_ref(v___y_6555_);
    lean_dec_ref(v___y_6554_);
    lean_dec(v___y_6553_);
    lean_dec_ref(v___y_6552_);
    return v_res_6560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0(
    mut v_pu_6561_: u8,
    mut v_f_6562_: *mut LeanObject,
    mut v_v_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
    mut v___y_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
    mut v___y_6568_: *mut LeanObject,
    mut v___y_6569_: *mut LeanObject,
    mut v___y_6570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    v___x_6572_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___redArg(v_f_6562_, v_v_6563_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_);
    return v___x_6572_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed(
    mut v_pu_6573_: *mut LeanObject,
    mut v_f_6574_: *mut LeanObject,
    mut v_v_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
    mut v___y_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
    mut v___y_6579_: *mut LeanObject,
    mut v___y_6580_: *mut LeanObject,
    mut v___y_6581_: *mut LeanObject,
    mut v___y_6582_: *mut LeanObject,
    mut v___y_6583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6584_: u8 = 0;
    let mut v_res_6585_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6584_ = (lean_unbox(v_pu_6573_) as u8);
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
    lean_dec(v___y_6582_);
    lean_dec_ref(v___y_6581_);
    lean_dec(v___y_6580_);
    lean_dec_ref(v___y_6579_);
    lean_dec_ref(v___y_6578_);
    lean_dec(v___y_6577_);
    lean_dec_ref(v___y_6576_);
    return v_res_6585_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_check(
    mut v_pu_6586_: u8,
    mut v_decl_6587_: *mut LeanObject,
    mut v_a_6588_: *mut LeanObject,
    mut v_a_6589_: *mut LeanObject,
    mut v_a_6590_: *mut LeanObject,
    mut v_a_6591_: *mut LeanObject,
) -> *mut LeanObject {
    if v_pu_6586_ == 0 {
        let mut v_toSignature_6593_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_6594_: *mut LeanObject = core::ptr::null_mut();
        let mut v_name_6595_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_6596_: *mut LeanObject = core::ptr::null_mut();
        let mut v_params_6597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
        v_toSignature_6593_ = lean_ctor_get(v_decl_6587_, 0);
        lean_inc_ref(v_toSignature_6593_);
        v_value_6594_ = lean_ctor_get(v_decl_6587_, 1);
        lean_inc_ref(v_value_6594_);
        lean_dec_ref(v_decl_6587_);
        v_name_6595_ = lean_ctor_get(v_toSignature_6593_, 0);
        lean_inc(v_name_6595_);
        v_type_6596_ = lean_ctor_get(v_toSignature_6593_, 2);
        lean_inc_ref(v_type_6596_);
        v_params_6597_ = lean_ctor_get(v_toSignature_6593_, 3);
        lean_inc_ref(v_params_6597_);
        lean_dec_ref(v_toSignature_6593_);
        v___x_6598_ = lean_alloc_closure(
            l_Lean_Compiler_LCNF_Check_Pure_checkFunDeclCore___boxed as *mut core::ffi::c_void,
            12,
            3,
        );
        lean_closure_set(v___x_6598_, 0, v_name_6595_);
        lean_closure_set(v___x_6598_, 1, v_params_6597_);
        lean_closure_set(v___x_6598_, 2, v_type_6596_);
        v___x_6599_ = lean_box((v_pu_6586_) as usize);
        v___x_6600_ = lean_alloc_closure(l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_Decl_check_spec__0___boxed as *mut core::ffi::c_void, 11, 3);
        lean_closure_set(v___x_6600_, 0, v___x_6599_);
        lean_closure_set(v___x_6600_, 1, v___x_6598_);
        lean_closure_set(v___x_6600_, 2, v_value_6594_);
        v___x_6601_ = l_Lean_Compiler_LCNF_Check_Pure_run___redArg(
            v___x_6600_,
            v_a_6588_,
            v_a_6589_,
            v_a_6590_,
            v_a_6591_,
        );
        return v___x_6601_;
    } else {
        let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_decl_6587_);
        v___x_6602_ = lean_box(0);
        v___x_6603_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6603_, 0, v___x_6602_);
        return v___x_6603_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_check___boxed(
    mut v_pu_6604_: *mut LeanObject,
    mut v_decl_6605_: *mut LeanObject,
    mut v_a_6606_: *mut LeanObject,
    mut v_a_6607_: *mut LeanObject,
    mut v_a_6608_: *mut LeanObject,
    mut v_a_6609_: *mut LeanObject,
    mut v_a_6610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6611_: u8 = 0;
    let mut v_res_6612_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6611_ = (lean_unbox(v_pu_6604_) as u8);
    v_res_6612_ = l_Lean_Compiler_LCNF_Decl_check(
        v_pu_boxed_6611_,
        v_decl_6605_,
        v_a_6606_,
        v_a_6607_,
        v_a_6608_,
        v_a_6609_,
    );
    lean_dec(v_a_6609_);
    lean_dec_ref(v_a_6608_);
    lean_dec(v_a_6607_);
    lean_dec_ref(v_a_6606_);
    return v_res_6612_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Check(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Check(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Check(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Check(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Check(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Check(builtin);
}
