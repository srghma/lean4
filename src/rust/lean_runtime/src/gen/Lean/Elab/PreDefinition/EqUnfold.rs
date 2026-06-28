// Lean compiler output
// Module: Lean.Elab.PreDefinition.EqUnfold
// Imports: Lean.Meta.Eqns Lean.Meta.Tactic.Rfl Lean.Meta.Tactic.Intro
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_replaceRef};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type};
use crate::r#gen::Lean::DefEqAttrib::l_Lean_inferDefEqAttr;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_isSafeDefinition, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_Kernel_enableDiag,
    l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_sort___override, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkAppM, l_Lean_Meta_mkEq};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_realizeConst,
};
use crate::r#gen::Lean::Meta::Eqns::{
    initialize_Lean_Meta_Eqns, l_Lean_Meta_eqUnfoldThmSuffix, l_Lean_Meta_getUnfoldEqnFor_x3f,
    l_Lean_Meta_mkEqLikeNameFor, l_Lean_Meta_withEqnOptions___boxed,
    runtime_initialize_Lean_Meta_Eqns,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{
    initialize_Lean_Meta_Tactic_Intro, runtime_initialize_Lean_Meta_Tactic_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Refl::l_Lean_MVarId_refl;
use crate::r#gen::Lean::Meta::Tactic::Rfl::{
    initialize_Lean_Meta_Tactic_Rfl, runtime_initialize_Lean_Meta_Tactic_Rfl,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_smartUnfolding;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::{l_Lean_isPrivateName, l_Lean_privateToUserName};
use crate::r#gen::Lean::ReservedNameAction::l_Lean_registerReservedNameAction;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_tryURefl___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_tryURefl___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_tryURefl___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_tryURefl___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_tryURefl___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_tryURefl___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__9___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__9___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__9___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 117, 110, 102, 111, 108, 100, 32,
            116, 104, 101, 111, 114, 101, 109, 32, 116, 121, 112, 101, 32, 0,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 117, 110, 101, 120, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___closed__0_value) as *mut LeanObject,9408729929927031778 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0_value: LeanStringObject<33> =
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
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105,
            116, 105, 111, 110, 46, 69, 113, 85, 110, 102, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 103, 101, 116, 67, 111, 110, 115, 116, 85,
            110, 102, 111, 108, 100, 69, 113, 110, 70, 111, 114, 63, 0,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2_value: LeanStringObject<34> =
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0_value: LeanStringObject<19> =
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
            82, 101, 115, 101, 114, 118, 101, 100, 78, 97, 109, 101, 65, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0_value)
                as *mut LeanObject,
            16524425170056508783 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            103, 101, 116, 67, 111, 110, 115, 116, 85, 110, 102, 111, 108, 100, 69, 113, 110, 70,
            111, 114, 63, 32, 0,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            32, 102, 97, 105, 108, 101, 100, 44, 32, 110, 111, 32, 117, 110, 102, 111, 108, 100,
            32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5_value) as *mut LeanObject;
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__4_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__4_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_tryURefl_spec__1(
    mut v_opts_1474_: *mut LeanObject,
    mut v_opt_1475_: *mut LeanObject,
) -> u8 {
    let mut v_name_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    v_name_1476_ = lean_ctor_get(v_opt_1475_, 0);
    v_defValue_1477_ = lean_ctor_get(v_opt_1475_, 1);
    v_map_1478_ = lean_ctor_get(v_opts_1474_, 0);
    v___x_1479_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1478_,
            v_name_1476_,
        );
    if lean_obj_tag(v___x_1479_) == 0 {
        let mut v___x_1480_: u8 = 0;
        v___x_1480_ = (lean_unbox(v_defValue_1477_) as u8);
        return v___x_1480_;
    } else {
        let mut v_val_1481_: *mut LeanObject = core::ptr::null_mut();
        v_val_1481_ = lean_ctor_get(v___x_1479_, 0);
        lean_inc(v_val_1481_);
        lean_dec_ref_known(v___x_1479_, 1);
        if lean_obj_tag(v_val_1481_) == 1 {
            let mut v_v_1482_: u8 = 0;
            v_v_1482_ = lean_ctor_get_uint8(v_val_1481_, 0 as u32);
            lean_dec_ref_known(v_val_1481_, 0);
            return v_v_1482_;
        } else {
            let mut v___x_1483_: u8 = 0;
            lean_dec(v_val_1481_);
            v___x_1483_ = (lean_unbox(v_defValue_1477_) as u8);
            return v___x_1483_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_tryURefl_spec__1___boxed(
    mut v_opts_1484_: *mut LeanObject,
    mut v_opt_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1486_: u8 = 0;
    let mut v_r_1487_: *mut LeanObject = core::ptr::null_mut();
    v_res_1486_ = l_Lean_Option_get___at___00Lean_Meta_tryURefl_spec__1(v_opts_1484_, v_opt_1485_);
    lean_dec_ref(v_opt_1485_);
    lean_dec_ref(v_opts_1484_);
    v_r_1487_ = lean_box((v_res_1486_) as usize);
    return v_r_1487_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_tryURefl_spec__2(
    mut v_opts_1488_: *mut LeanObject,
    mut v_opt_1489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    v_name_1490_ = lean_ctor_get(v_opt_1489_, 0);
    v_defValue_1491_ = lean_ctor_get(v_opt_1489_, 1);
    v_map_1492_ = lean_ctor_get(v_opts_1488_, 0);
    v___x_1493_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1492_,
            v_name_1490_,
        );
    if lean_obj_tag(v___x_1493_) == 0 {
        lean_inc(v_defValue_1491_);
        return v_defValue_1491_;
    } else {
        let mut v_val_1494_: *mut LeanObject = core::ptr::null_mut();
        v_val_1494_ = lean_ctor_get(v___x_1493_, 0);
        lean_inc(v_val_1494_);
        lean_dec_ref_known(v___x_1493_, 1);
        if lean_obj_tag(v_val_1494_) == 3 {
            let mut v_v_1495_: *mut LeanObject = core::ptr::null_mut();
            v_v_1495_ = lean_ctor_get(v_val_1494_, 0);
            lean_inc(v_v_1495_);
            lean_dec_ref_known(v_val_1494_, 1);
            return v_v_1495_;
        } else {
            lean_dec(v_val_1494_);
            lean_inc(v_defValue_1491_);
            return v_defValue_1491_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_tryURefl_spec__2___boxed(
    mut v_opts_1496_: *mut LeanObject,
    mut v_opt_1497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1498_: *mut LeanObject = core::ptr::null_mut();
    v_res_1498_ = l_Lean_Option_get___at___00Lean_Meta_tryURefl_spec__2(v_opts_1496_, v_opt_1497_);
    lean_dec_ref(v_opt_1497_);
    lean_dec_ref(v_opts_1496_);
    return v_res_1498_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0(
    mut v_o_1502_: *mut LeanObject,
    mut v_k_1503_: *mut LeanObject,
    mut v_v_1504_: u8,
) -> *mut LeanObject {
    let mut v_map_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1506_: u8 = 0;
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1505_ = lean_ctor_get(v_o_1502_, 0);
                v_hasTrace_1506_ = lean_ctor_get_uint8(
                    v_o_1502_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1520_ = (!lean_is_exclusive(v_o_1502_)) as u8;
                if v_isSharedCheck_1520_ == 0 {
                    v___x_1508_ = v_o_1502_;
                    v_isShared_1509_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_1505_);
                    lean_dec(v_o_1502_);
                    v___x_1508_ = lean_box(0);
                    v_isShared_1509_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1510_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_1510_, 0 as u32, v_v_1504_);
                lean_inc(v_k_1503_);
                v___x_1511_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1503_, v___x_1510_, v_map_1505_);
                if v_hasTrace_1506_ == 0 {
                    v___x_1512_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__1;
                    v___x_1513_ = l_Lean_Name_isPrefixOf(v___x_1512_, v_k_1503_);
                    lean_dec(v_k_1503_);
                    if v_isShared_1509_ == 0 {
                        lean_ctor_set(v___x_1508_, 0, v___x_1511_);
                        v___x_1515_ = v___x_1508_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1511_);
                        v___x_1515_ = v_reuseFailAlloc_1516_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_1503_);
                    if v_isShared_1509_ == 0 {
                        lean_ctor_set(v___x_1508_, 0, v___x_1511_);
                        v___x_1518_ = v___x_1508_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1511_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1519_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_1506_,
                        );
                        v___x_1518_ = v_reuseFailAlloc_1519_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1515_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1513_,
                );
                return v___x_1515_;
            }
            3 => {
                return v___x_1518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___boxed(
    mut v_o_1521_: *mut LeanObject,
    mut v_k_1522_: *mut LeanObject,
    mut v_v_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1524_: u8 = 0;
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1524_ = (lean_unbox(v_v_1523_) as u8);
    v_res_1525_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0(
            v_o_1521_,
            v_k_1522_,
            v_v_boxed_1524_,
        );
    return v_res_1525_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0(
    mut v_opts_1526_: *mut LeanObject,
    mut v_opt_1527_: *mut LeanObject,
    mut v_val_1528_: u8,
) -> *mut LeanObject {
    let mut v_name_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v_name_1529_ = lean_ctor_get(v_opt_1527_, 0);
    lean_inc(v_name_1529_);
    lean_dec_ref(v_opt_1527_);
    v___x_1530_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0(
            v_opts_1526_,
            v_name_1529_,
            v_val_1528_,
        );
    return v___x_1530_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0___boxed(
    mut v_opts_1531_: *mut LeanObject,
    mut v_opt_1532_: *mut LeanObject,
    mut v_val_1533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_1534_: u8 = 0;
    let mut v_res_1535_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_1534_ = (lean_unbox(v_val_1533_) as u8);
    v_res_1535_ = l_Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0(
        v_opts_1531_,
        v_opt_1532_,
        v_val_boxed_1534_,
    );
    return v_res_1535_;
}
pub unsafe fn _init_l_Lean_Meta_tryURefl___closed__0() -> *mut LeanObject {
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    v___x_1536_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1536_;
}
pub unsafe fn _init_l_Lean_Meta_tryURefl___closed__1() -> *mut LeanObject {
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    v___x_1537_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_tryURefl___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_tryURefl___closed__0_once),
        _init_l_Lean_Meta_tryURefl___closed__0,
    );
    v___x_1538_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1538_, 0, v___x_1537_);
    return v___x_1538_;
}
pub unsafe fn _init_l_Lean_Meta_tryURefl___closed__2() -> *mut LeanObject {
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    v___x_1539_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_tryURefl___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_tryURefl___closed__1_once),
        _init_l_Lean_Meta_tryURefl___closed__1,
    );
    v___x_1540_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1540_, 0, v___x_1539_);
    lean_ctor_set(v___x_1540_, 1, v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Lean_Meta_tryURefl(
    mut v_mvarId_1541_: *mut LeanObject,
    mut v_a_1542_: *mut LeanObject,
    mut v_a_1543_: *mut LeanObject,
    mut v_a_1544_: *mut LeanObject,
    mut v_a_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1549_: u8 = 0;
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1566_: u8 = 0;
    let mut v_inheritedTraceOptions_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v_fileName_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1587_: u8 = 0;
    let mut v_inheritedTraceOptions_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_unused_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: u8 = 0;
    let mut v___y_1607_: u8 = 0;
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_unused_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1553_ = lean_st_ref_get(v_a_1545_);
                v_fileName_1554_ = lean_ctor_get(v_a_1544_, 0);
                v_fileMap_1555_ = lean_ctor_get(v_a_1544_, 1);
                v_options_1556_ = lean_ctor_get(v_a_1544_, 2);
                v_currRecDepth_1557_ = lean_ctor_get(v_a_1544_, 3);
                v_ref_1558_ = lean_ctor_get(v_a_1544_, 5);
                v_currNamespace_1559_ = lean_ctor_get(v_a_1544_, 6);
                v_openDecls_1560_ = lean_ctor_get(v_a_1544_, 7);
                v_initHeartbeats_1561_ = lean_ctor_get(v_a_1544_, 8);
                v_maxHeartbeats_1562_ = lean_ctor_get(v_a_1544_, 9);
                v_quotContext_1563_ = lean_ctor_get(v_a_1544_, 10);
                v_currMacroScope_1564_ = lean_ctor_get(v_a_1544_, 11);
                v_cancelTk_x3f_1565_ = lean_ctor_get(v_a_1544_, 12);
                v_suppressElabErrors_1566_ = lean_ctor_get_uint8(
                    v_a_1544_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1567_ = lean_ctor_get(v_a_1544_, 13);
                v_env_1568_ = lean_ctor_get(v___x_1553_, 0);
                lean_inc_ref(v_env_1568_);
                lean_dec(v___x_1553_);
                v___x_1569_ = 1;
                v___x_1570_ = l_Lean_Meta_smartUnfolding;
                v___x_1571_ = 0;
                lean_inc_ref(v_options_1556_);
                v___x_1572_ = l_Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0(
                    v_options_1556_,
                    v___x_1570_,
                    v___x_1571_,
                );
                v___x_1573_ = l_Lean_diagnostics;
                v___x_1574_ =
                    l_Lean_Option_get___at___00Lean_Meta_tryURefl_spec__1(v___x_1572_, v___x_1573_);
                v___x_1628_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1568_);
                lean_dec_ref(v_env_1568_);
                if v___x_1628_ == 0 {
                    if v___x_1574_ == 0 {
                        v_fileName_1576_ = v_fileName_1554_;
                        v_fileMap_1577_ = v_fileMap_1555_;
                        v_currRecDepth_1578_ = v_currRecDepth_1557_;
                        v_ref_1579_ = v_ref_1558_;
                        v_currNamespace_1580_ = v_currNamespace_1559_;
                        v_openDecls_1581_ = v_openDecls_1560_;
                        v_initHeartbeats_1582_ = v_initHeartbeats_1561_;
                        v_maxHeartbeats_1583_ = v_maxHeartbeats_1562_;
                        v_quotContext_1584_ = v_quotContext_1563_;
                        v_currMacroScope_1585_ = v_currMacroScope_1564_;
                        v_cancelTk_x3f_1586_ = v_cancelTk_x3f_1565_;
                        v_suppressElabErrors_1587_ = v_suppressElabErrors_1566_;
                        v_inheritedTraceOptions_1588_ = v_inheritedTraceOptions_1567_;
                        v___y_1589_ = v_a_1545_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1607_ = v___x_1628_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_1607_ = v___x_1574_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                if v___y_1549_ == 0 {
                    lean_dec_ref(v___y_1548_);
                    v___x_1550_ = lean_box((v___y_1549_) as usize);
                    v___x_1551_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1551_, 0, v___x_1550_);
                    return v___x_1551_;
                } else {
                    v___x_1552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1552_, 0, v___y_1548_);
                    return v___x_1552_;
                }
            }
            2 => {
                v___x_1590_ = l_Lean_maxRecDepth;
                v___x_1591_ =
                    l_Lean_Option_get___at___00Lean_Meta_tryURefl_spec__2(v___x_1572_, v___x_1590_);
                lean_inc_ref(v_inheritedTraceOptions_1588_);
                lean_inc(v_cancelTk_x3f_1586_);
                lean_inc(v_currMacroScope_1585_);
                lean_inc(v_quotContext_1584_);
                lean_inc(v_maxHeartbeats_1583_);
                lean_inc(v_initHeartbeats_1582_);
                lean_inc(v_openDecls_1581_);
                lean_inc(v_currNamespace_1580_);
                lean_inc(v_ref_1579_);
                lean_inc(v_currRecDepth_1578_);
                lean_inc_ref(v_fileMap_1577_);
                lean_inc_ref(v_fileName_1576_);
                v___x_1592_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1592_, 0, v_fileName_1576_);
                lean_ctor_set(v___x_1592_, 1, v_fileMap_1577_);
                lean_ctor_set(v___x_1592_, 2, v___x_1572_);
                lean_ctor_set(v___x_1592_, 3, v_currRecDepth_1578_);
                lean_ctor_set(v___x_1592_, 4, v___x_1591_);
                lean_ctor_set(v___x_1592_, 5, v_ref_1579_);
                lean_ctor_set(v___x_1592_, 6, v_currNamespace_1580_);
                lean_ctor_set(v___x_1592_, 7, v_openDecls_1581_);
                lean_ctor_set(v___x_1592_, 8, v_initHeartbeats_1582_);
                lean_ctor_set(v___x_1592_, 9, v_maxHeartbeats_1583_);
                lean_ctor_set(v___x_1592_, 10, v_quotContext_1584_);
                lean_ctor_set(v___x_1592_, 11, v_currMacroScope_1585_);
                lean_ctor_set(v___x_1592_, 12, v_cancelTk_x3f_1586_);
                lean_ctor_set(v___x_1592_, 13, v_inheritedTraceOptions_1588_);
                lean_ctor_set_uint8(
                    v___x_1592_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_1574_,
                );
                lean_ctor_set_uint8(
                    v___x_1592_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1587_,
                );
                v___x_1593_ = l_Lean_MVarId_refl(
                    v_mvarId_1541_,
                    v___x_1569_,
                    v_a_1542_,
                    v_a_1543_,
                    v___x_1592_,
                    v___y_1589_,
                );
                lean_dec_ref_known(v___x_1592_, 14);
                if lean_obj_tag(v___x_1593_) == 0 {
                    v_isSharedCheck_1601_ = (!lean_is_exclusive(v___x_1593_)) as u8;
                    if v_isSharedCheck_1601_ == 0 {
                        v_unused_1602_ = lean_ctor_get(v___x_1593_, 0);
                        lean_dec(v_unused_1602_);
                        v___x_1595_ = v___x_1593_;
                        v_isShared_1596_ = v_isSharedCheck_1601_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_1593_);
                        v___x_1595_ = lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1601_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1603_ = lean_ctor_get(v___x_1593_, 0);
                    lean_inc(v_a_1603_);
                    lean_dec_ref_known(v___x_1593_, 1);
                    v___x_1604_ = l_Lean_Exception_isInterrupt(v_a_1603_);
                    if v___x_1604_ == 0 {
                        lean_inc(v_a_1603_);
                        v___x_1605_ = l_Lean_Exception_isRuntime(v_a_1603_);
                        v___y_1548_ = v_a_1603_;
                        v___y_1549_ = v___x_1605_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1548_ = v_a_1603_;
                        v___y_1549_ = v___x_1604_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1597_ = lean_box((v___x_1569_) as usize);
                if v_isShared_1596_ == 0 {
                    lean_ctor_set(v___x_1595_, 0, v___x_1597_);
                    v___x_1599_ = v___x_1595_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
                    v___x_1599_ = v_reuseFailAlloc_1600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1599_;
            }
            5 => {
                if v___y_1607_ == 0 {
                    v___x_1608_ = lean_st_ref_take(v_a_1545_);
                    v_env_1609_ = lean_ctor_get(v___x_1608_, 0);
                    v_nextMacroScope_1610_ = lean_ctor_get(v___x_1608_, 1);
                    v_ngen_1611_ = lean_ctor_get(v___x_1608_, 2);
                    v_auxDeclNGen_1612_ = lean_ctor_get(v___x_1608_, 3);
                    v_traceState_1613_ = lean_ctor_get(v___x_1608_, 4);
                    v_messages_1614_ = lean_ctor_get(v___x_1608_, 6);
                    v_infoState_1615_ = lean_ctor_get(v___x_1608_, 7);
                    v_snapshotTasks_1616_ = lean_ctor_get(v___x_1608_, 8);
                    v_isSharedCheck_1626_ = (!lean_is_exclusive(v___x_1608_)) as u8;
                    if v_isSharedCheck_1626_ == 0 {
                        v_unused_1627_ = lean_ctor_get(v___x_1608_, 5);
                        lean_dec(v_unused_1627_);
                        v___x_1618_ = v___x_1608_;
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1616_);
                        lean_inc(v_infoState_1615_);
                        lean_inc(v_messages_1614_);
                        lean_inc(v_traceState_1613_);
                        lean_inc(v_auxDeclNGen_1612_);
                        lean_inc(v_ngen_1611_);
                        lean_inc(v_nextMacroScope_1610_);
                        lean_inc(v_env_1609_);
                        lean_dec(v___x_1608_);
                        v___x_1618_ = lean_box(0);
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_fileName_1576_ = v_fileName_1554_;
                    v_fileMap_1577_ = v_fileMap_1555_;
                    v_currRecDepth_1578_ = v_currRecDepth_1557_;
                    v_ref_1579_ = v_ref_1558_;
                    v_currNamespace_1580_ = v_currNamespace_1559_;
                    v_openDecls_1581_ = v_openDecls_1560_;
                    v_initHeartbeats_1582_ = v_initHeartbeats_1561_;
                    v_maxHeartbeats_1583_ = v_maxHeartbeats_1562_;
                    v_quotContext_1584_ = v_quotContext_1563_;
                    v_currMacroScope_1585_ = v_currMacroScope_1564_;
                    v_cancelTk_x3f_1586_ = v_cancelTk_x3f_1565_;
                    v_suppressElabErrors_1587_ = v_suppressElabErrors_1566_;
                    v_inheritedTraceOptions_1588_ = v_inheritedTraceOptions_1567_;
                    v___y_1589_ = v_a_1545_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_1620_ = l_Lean_Kernel_enableDiag(v_env_1609_, v___x_1574_);
                v___x_1621_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_tryURefl___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_tryURefl___closed__2_once),
                    _init_l_Lean_Meta_tryURefl___closed__2,
                );
                if v_isShared_1619_ == 0 {
                    lean_ctor_set(v___x_1618_, 5, v___x_1621_);
                    lean_ctor_set(v___x_1618_, 0, v___x_1620_);
                    v___x_1623_ = v___x_1618_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1620_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_nextMacroScope_1610_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_ngen_1611_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_auxDeclNGen_1612_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_traceState_1613_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 5, v___x_1621_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 6, v_messages_1614_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 7, v_infoState_1615_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 8, v_snapshotTasks_1616_);
                    v___x_1623_ = v_reuseFailAlloc_1625_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1624_ = lean_st_ref_set(v_a_1545_, v___x_1623_);
                v_fileName_1576_ = v_fileName_1554_;
                v_fileMap_1577_ = v_fileMap_1555_;
                v_currRecDepth_1578_ = v_currRecDepth_1557_;
                v_ref_1579_ = v_ref_1558_;
                v_currNamespace_1580_ = v_currNamespace_1559_;
                v_openDecls_1581_ = v_openDecls_1560_;
                v_initHeartbeats_1582_ = v_initHeartbeats_1561_;
                v_maxHeartbeats_1583_ = v_maxHeartbeats_1562_;
                v_quotContext_1584_ = v_quotContext_1563_;
                v_currMacroScope_1585_ = v_currMacroScope_1564_;
                v_cancelTk_x3f_1586_ = v_cancelTk_x3f_1565_;
                v_suppressElabErrors_1587_ = v_suppressElabErrors_1566_;
                v_inheritedTraceOptions_1588_ = v_inheritedTraceOptions_1567_;
                v___y_1589_ = v_a_1545_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_tryURefl___boxed(
    mut v_mvarId_1629_: *mut LeanObject,
    mut v_a_1630_: *mut LeanObject,
    mut v_a_1631_: *mut LeanObject,
    mut v_a_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
    mut v_a_1634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1635_: *mut LeanObject = core::ptr::null_mut();
    v_res_1635_ = l_Lean_Meta_tryURefl(v_mvarId_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
    lean_dec(v_a_1633_);
    lean_dec_ref(v_a_1632_);
    lean_dec(v_a_1631_);
    lean_dec_ref(v_a_1630_);
    return v_res_1635_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg___lam__0(
    mut v_k_1636_: *mut LeanObject,
    mut v_b_1637_: *mut LeanObject,
    mut v_c_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1642_);
    lean_inc_ref(v___y_1641_);
    lean_inc(v___y_1640_);
    lean_inc_ref(v___y_1639_);
    v___x_1644_ = lean_apply_7(
        v_k_1636_,
        v_b_1637_,
        v_c_1638_,
        v___y_1639_,
        v___y_1640_,
        v___y_1641_,
        v___y_1642_,
        lean_box(0),
    );
    return v___x_1644_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg___lam__0___boxed(
    mut v_k_1645_: *mut LeanObject,
    mut v_b_1646_: *mut LeanObject,
    mut v_c_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1653_: *mut LeanObject = core::ptr::null_mut();
    v_res_1653_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg___lam__0(v_k_1645_, v_b_1646_, v_c_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
    lean_dec(v___y_1651_);
    lean_dec_ref(v___y_1650_);
    lean_dec(v___y_1649_);
    lean_dec_ref(v___y_1648_);
    return v_res_1653_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg(
    mut v_type_1654_: *mut LeanObject,
    mut v_k_1655_: *mut LeanObject,
    mut v_cleanupAnnotations_1656_: u8,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1669_: u8 = 0;
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1673_: u8 = 0;
    let mut v_a_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1662_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1662_, 0, v_k_1655_);
                v___x_1663_ = 0;
                v___x_1664_ = lean_box(0);
                v___x_1665_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
                        v___x_1663_,
                        v___x_1664_,
                        v_type_1654_,
                        v___f_1662_,
                        v_cleanupAnnotations_1656_,
                        v___x_1663_,
                        v___y_1657_,
                        v___y_1658_,
                        v___y_1659_,
                        v___y_1660_,
                    );
                if lean_obj_tag(v___x_1665_) == 0 {
                    v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
                    v_isSharedCheck_1673_ = (!lean_is_exclusive(v___x_1665_)) as u8;
                    if v_isSharedCheck_1673_ == 0 {
                        v___x_1668_ = v___x_1665_;
                        v_isShared_1669_ = v_isSharedCheck_1673_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1666_);
                        lean_dec(v___x_1665_);
                        v___x_1668_ = lean_box(0);
                        v_isShared_1669_ = v_isSharedCheck_1673_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1674_ = lean_ctor_get(v___x_1665_, 0);
                    v_isSharedCheck_1681_ = (!lean_is_exclusive(v___x_1665_)) as u8;
                    if v_isSharedCheck_1681_ == 0 {
                        v___x_1676_ = v___x_1665_;
                        v_isShared_1677_ = v_isSharedCheck_1681_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1674_);
                        lean_dec(v___x_1665_);
                        v___x_1676_ = lean_box(0);
                        v_isShared_1677_ = v_isSharedCheck_1681_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1669_ == 0 {
                    v___x_1671_ = v___x_1668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
                    v___x_1671_ = v_reuseFailAlloc_1672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1671_;
            }
            3 => {
                if v_isShared_1677_ == 0 {
                    v___x_1679_ = v___x_1676_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
                    v___x_1679_ = v_reuseFailAlloc_1680_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg___boxed(
    mut v_type_1682_: *mut LeanObject,
    mut v_k_1683_: *mut LeanObject,
    mut v_cleanupAnnotations_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1690_: u8 = 0;
    let mut v_res_1691_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1690_ = (lean_unbox(v_cleanupAnnotations_1684_) as u8);
    v_res_1691_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg(
            v_type_1682_,
            v_k_1683_,
            v_cleanupAnnotations_boxed_1690_,
            v___y_1685_,
            v___y_1686_,
            v___y_1687_,
            v___y_1688_,
        );
    lean_dec(v___y_1688_);
    lean_dec_ref(v___y_1687_);
    lean_dec(v___y_1686_);
    lean_dec_ref(v___y_1685_);
    return v_res_1691_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6(
    mut v_00_u03b1_1692_: *mut LeanObject,
    mut v_type_1693_: *mut LeanObject,
    mut v_k_1694_: *mut LeanObject,
    mut v_cleanupAnnotations_1695_: u8,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    v___x_1701_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg(
            v_type_1693_,
            v_k_1694_,
            v_cleanupAnnotations_1695_,
            v___y_1696_,
            v___y_1697_,
            v___y_1698_,
            v___y_1699_,
        );
    return v___x_1701_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___boxed(
    mut v_00_u03b1_1702_: *mut LeanObject,
    mut v_type_1703_: *mut LeanObject,
    mut v_k_1704_: *mut LeanObject,
    mut v_cleanupAnnotations_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1711_: u8 = 0;
    let mut v_res_1712_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1711_ = (lean_unbox(v_cleanupAnnotations_1705_) as u8);
    v_res_1712_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6(
        v_00_u03b1_1702_,
        v_type_1703_,
        v_k_1704_,
        v_cleanupAnnotations_boxed_1711_,
        v___y_1706_,
        v___y_1707_,
        v___y_1708_,
        v___y_1709_,
    );
    lean_dec(v___y_1709_);
    lean_dec_ref(v___y_1708_);
    lean_dec(v___y_1707_);
    lean_dec_ref(v___y_1706_);
    return v_res_1712_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__7___redArg(
    mut v_e_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1736_: u8 = 0;
    let mut v_unused_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1716_ = l_Lean_Expr_hasMVar(v_e_1713_);
                if v___x_1716_ == 0 {
                    v___x_1717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1717_, 0, v_e_1713_);
                    return v___x_1717_;
                } else {
                    v___x_1718_ = lean_st_ref_get(v___y_1714_);
                    v_mctx_1719_ = lean_ctor_get(v___x_1718_, 0);
                    lean_inc_ref(v_mctx_1719_);
                    lean_dec(v___x_1718_);
                    v___x_1720_ = l_Lean_instantiateMVarsCore(v_mctx_1719_, v_e_1713_);
                    v_fst_1721_ = lean_ctor_get(v___x_1720_, 0);
                    lean_inc(v_fst_1721_);
                    v_snd_1722_ = lean_ctor_get(v___x_1720_, 1);
                    lean_inc(v_snd_1722_);
                    lean_dec_ref(v___x_1720_);
                    v___x_1723_ = lean_st_ref_take(v___y_1714_);
                    v_cache_1724_ = lean_ctor_get(v___x_1723_, 1);
                    v_zetaDeltaFVarIds_1725_ = lean_ctor_get(v___x_1723_, 2);
                    v_postponed_1726_ = lean_ctor_get(v___x_1723_, 3);
                    v_diag_1727_ = lean_ctor_get(v___x_1723_, 4);
                    v_isSharedCheck_1736_ = (!lean_is_exclusive(v___x_1723_)) as u8;
                    if v_isSharedCheck_1736_ == 0 {
                        v_unused_1737_ = lean_ctor_get(v___x_1723_, 0);
                        lean_dec(v_unused_1737_);
                        v___x_1729_ = v___x_1723_;
                        v_isShared_1730_ = v_isSharedCheck_1736_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1727_);
                        lean_inc(v_postponed_1726_);
                        lean_inc(v_zetaDeltaFVarIds_1725_);
                        lean_inc(v_cache_1724_);
                        lean_dec(v___x_1723_);
                        v___x_1729_ = lean_box(0);
                        v_isShared_1730_ = v_isSharedCheck_1736_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1730_ == 0 {
                    lean_ctor_set(v___x_1729_, 0, v_snd_1722_);
                    v___x_1732_ = v___x_1729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_snd_1722_);
                    lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_cache_1724_);
                    lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_zetaDeltaFVarIds_1725_);
                    lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_postponed_1726_);
                    lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_diag_1727_);
                    v___x_1732_ = v_reuseFailAlloc_1735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1733_ = lean_st_ref_set(v___y_1714_, v___x_1732_);
                v___x_1734_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1734_, 0, v_fst_1721_);
                return v___x_1734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__7___redArg___boxed(
    mut v_e_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1741_: *mut LeanObject = core::ptr::null_mut();
    v_res_1741_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__7___redArg(
            v_e_1738_,
            v___y_1739_,
        );
    lean_dec(v___y_1739_);
    return v_res_1741_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__7(
    mut v_e_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
    mut v___y_1744_: *mut LeanObject,
    mut v___y_1745_: *mut LeanObject,
    mut v___y_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__7___redArg(
            v_e_1742_,
            v___y_1744_,
        );
    return v___x_1748_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__7___boxed(
    mut v_e_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1755_: *mut LeanObject = core::ptr::null_mut();
    v_res_1755_ = l_Lean_instantiateMVars___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__7(
        v_e_1749_,
        v___y_1750_,
        v___y_1751_,
        v___y_1752_,
        v___y_1753_,
    );
    lean_dec(v___y_1753_);
    lean_dec_ref(v___y_1752_);
    lean_dec(v___y_1751_);
    lean_dec_ref(v___y_1750_);
    return v_res_1755_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__8___redArg(
    mut v_k_1756_: *mut LeanObject,
    mut v_allowLevelAssignments_1757_: u8,
    mut v___y_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_a_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1763_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_1757_,
                    v_k_1756_,
                    v___y_1758_,
                    v___y_1759_,
                    v___y_1760_,
                    v___y_1761_,
                );
                if lean_obj_tag(v___x_1763_) == 0 {
                    v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1771_ = (!lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1771_ == 0 {
                        v___x_1766_ = v___x_1763_;
                        v_isShared_1767_ = v_isSharedCheck_1771_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1764_);
                        lean_dec(v___x_1763_);
                        v___x_1766_ = lean_box(0);
                        v_isShared_1767_ = v_isSharedCheck_1771_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1772_ = lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1779_ = (!lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1779_ == 0 {
                        v___x_1774_ = v___x_1763_;
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1772_);
                        lean_dec(v___x_1763_);
                        v___x_1774_ = lean_box(0);
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1767_ == 0 {
                    v___x_1769_ = v___x_1766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
                    v___x_1769_ = v_reuseFailAlloc_1770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1769_;
            }
            3 => {
                if v_isShared_1775_ == 0 {
                    v___x_1777_ = v___x_1774_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
                    v___x_1777_ = v_reuseFailAlloc_1778_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__8___redArg___boxed(
    mut v_k_1780_: *mut LeanObject,
    mut v_allowLevelAssignments_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_1787_: u8 = 0;
    let mut v_res_1788_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1787_ = (lean_unbox(v_allowLevelAssignments_1781_) as u8);
    v_res_1788_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__8___redArg(
            v_k_1780_,
            v_allowLevelAssignments_boxed_1787_,
            v___y_1782_,
            v___y_1783_,
            v___y_1784_,
            v___y_1785_,
        );
    lean_dec(v___y_1785_);
    lean_dec_ref(v___y_1784_);
    lean_dec(v___y_1783_);
    lean_dec_ref(v___y_1782_);
    return v_res_1788_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__8(
    mut v_00_u03b1_1789_: *mut LeanObject,
    mut v_k_1790_: *mut LeanObject,
    mut v_allowLevelAssignments_1791_: u8,
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    v___x_1797_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__8___redArg(
            v_k_1790_,
            v_allowLevelAssignments_1791_,
            v___y_1792_,
            v___y_1793_,
            v___y_1794_,
            v___y_1795_,
        );
    return v___x_1797_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__8___boxed(
    mut v_00_u03b1_1798_: *mut LeanObject,
    mut v_k_1799_: *mut LeanObject,
    mut v_allowLevelAssignments_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
    mut v___y_1803_: *mut LeanObject,
    mut v___y_1804_: *mut LeanObject,
    mut v___y_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_1806_: u8 = 0;
    let mut v_res_1807_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1806_ = (lean_unbox(v_allowLevelAssignments_1800_) as u8);
    v_res_1807_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__8(
        v_00_u03b1_1798_,
        v_k_1799_,
        v_allowLevelAssignments_boxed_1806_,
        v___y_1801_,
        v___y_1802_,
        v___y_1803_,
        v___y_1804_,
    );
    lean_dec(v___y_1804_);
    lean_dec_ref(v___y_1803_);
    lean_dec(v___y_1802_);
    lean_dec_ref(v___y_1801_);
    return v_res_1807_;
}
pub unsafe fn l_panic___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__9(
    mut v_msg_1809_: *mut LeanObject,
    mut v___y_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9521__overap_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    v___f_1815_ = l_panic___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__9___closed__0;
    v___x_9521__overap_1816_ = lean_panic_fn_borrowed(v___f_1815_, v_msg_1809_);
    lean_inc(v___y_1813_);
    lean_inc_ref(v___y_1812_);
    lean_inc(v___y_1811_);
    lean_inc_ref(v___y_1810_);
    v___x_1817_ = lean_apply_5(
        v___x_9521__overap_1816_,
        v___y_1810_,
        v___y_1811_,
        v___y_1812_,
        v___y_1813_,
        lean_box(0),
    );
    return v___x_1817_;
}
pub unsafe fn l_panic___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__9___boxed(
    mut v_msg_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1824_: *mut LeanObject = core::ptr::null_mut();
    v_res_1824_ = l_panic___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__9(
        v_msg_1818_,
        v___y_1819_,
        v___y_1820_,
        v___y_1821_,
        v___y_1822_,
    );
    lean_dec(v___y_1822_);
    lean_dec_ref(v___y_1821_);
    lean_dec(v___y_1820_);
    lean_dec_ref(v___y_1819_);
    return v_res_1824_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0_spec__0(
    mut v_msgData_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    v___x_1831_ = lean_st_ref_get(v___y_1829_);
    v_env_1832_ = lean_ctor_get(v___x_1831_, 0);
    lean_inc_ref(v_env_1832_);
    lean_dec(v___x_1831_);
    v___x_1833_ = lean_st_ref_get(v___y_1827_);
    v_mctx_1834_ = lean_ctor_get(v___x_1833_, 0);
    lean_inc_ref(v_mctx_1834_);
    lean_dec(v___x_1833_);
    v_lctx_1835_ = lean_ctor_get(v___y_1826_, 2);
    v_options_1836_ = lean_ctor_get(v___y_1828_, 2);
    lean_inc_ref(v_options_1836_);
    lean_inc_ref(v_lctx_1835_);
    v___x_1837_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1837_, 0, v_env_1832_);
    lean_ctor_set(v___x_1837_, 1, v_mctx_1834_);
    lean_ctor_set(v___x_1837_, 2, v_lctx_1835_);
    lean_ctor_set(v___x_1837_, 3, v_options_1836_);
    v___x_1838_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1838_, 0, v___x_1837_);
    lean_ctor_set(v___x_1838_, 1, v_msgData_1825_);
    v___x_1839_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1839_, 0, v___x_1838_);
    return v___x_1839_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0_spec__0___boxed(
    mut v_msgData_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1846_: *mut LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0_spec__0(v_msgData_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
    lean_dec(v___y_1844_);
    lean_dec_ref(v___y_1843_);
    lean_dec(v___y_1842_);
    lean_dec_ref(v___y_1841_);
    return v_res_1846_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___redArg(
    mut v_msg_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1853_ = lean_ctor_get(v___y_1850_, 5);
                v___x_1854_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0_spec__0(v_msg_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
                v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
                v_isSharedCheck_1863_ = (!lean_is_exclusive(v___x_1854_)) as u8;
                if v_isSharedCheck_1863_ == 0 {
                    v___x_1857_ = v___x_1854_;
                    v_isShared_1858_ = v_isSharedCheck_1863_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1855_);
                    lean_dec(v___x_1854_);
                    v___x_1857_ = lean_box(0);
                    v_isShared_1858_ = v_isSharedCheck_1863_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1853_);
                v___x_1859_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1859_, 0, v_ref_1853_);
                lean_ctor_set(v___x_1859_, 1, v_a_1855_);
                if v_isShared_1858_ == 0 {
                    lean_ctor_set_tag(v___x_1857_, 1);
                    lean_ctor_set(v___x_1857_, 0, v___x_1859_);
                    v___x_1861_ = v___x_1857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
                    v___x_1861_ = v_reuseFailAlloc_1862_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___redArg___boxed(
    mut v_msg_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1870_: *mut LeanObject = core::ptr::null_mut();
    v_res_1870_ = l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___redArg(
        v_msg_1864_,
        v___y_1865_,
        v___y_1866_,
        v___y_1867_,
        v___y_1868_,
    );
    lean_dec(v___y_1868_);
    lean_dec_ref(v___y_1867_);
    lean_dec(v___y_1866_);
    lean_dec_ref(v___y_1865_);
    return v_res_1870_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__5___redArg(
    mut v_xs_1871_: *mut LeanObject,
    mut v_ys_1872_: *mut LeanObject,
    mut v_x_1873_: *mut LeanObject,
) -> u8 {
    let mut v_zero_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1875_: u8 = 0;
    let mut v_one_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1874_ = lean_unsigned_to_nat(0);
                v_isZero_1875_ = lean_nat_dec_eq(v_x_1873_, v_zero_1874_);
                if v_isZero_1875_ == 1 {
                    lean_dec(v_x_1873_);
                    return v_isZero_1875_;
                } else {
                    v_one_1876_ = lean_unsigned_to_nat(1);
                    v_n_1877_ = lean_nat_sub(v_x_1873_, v_one_1876_);
                    lean_dec(v_x_1873_);
                    v___x_1878_ = lean_array_fget_borrowed(v_xs_1871_, v_n_1877_);
                    v___x_1879_ = lean_array_fget_borrowed(v_ys_1872_, v_n_1877_);
                    v___x_1880_ = lean_expr_eqv(v___x_1878_, v___x_1879_);
                    if v___x_1880_ == 0 {
                        lean_dec(v_n_1877_);
                        return v___x_1880_;
                    } else {
                        v_x_1873_ = v_n_1877_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__5___redArg___boxed(
    mut v_xs_1882_: *mut LeanObject,
    mut v_ys_1883_: *mut LeanObject,
    mut v_x_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1885_: u8 = 0;
    let mut v_r_1886_: *mut LeanObject = core::ptr::null_mut();
    v_res_1885_ = l_Array_isEqvAux___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__5___redArg(
        v_xs_1882_, v_ys_1883_, v_x_1884_,
    );
    lean_dec_ref(v_ys_1883_);
    lean_dec_ref(v_xs_1882_);
    v_r_1886_ = lean_box((v_res_1885_) as usize);
    return v_r_1886_;
}
pub unsafe fn _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2;
    v___x_1892_ = l_Lean_stringToMessageData(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1893_ = lean_box(0);
    v_dummy_1894_ = l_Lean_Expr_sort___override(v___x_1893_);
    return v_dummy_1894_;
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0(
    mut v___x_1895_: *mut LeanObject,
    mut v___x_1896_: u8,
    mut v___x_1897_: u8,
    mut v_declName_1898_: *mut LeanObject,
    mut v_xs_1899_: *mut LeanObject,
    mut v_eq_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
    mut v___y_1903_: *mut LeanObject,
    mut v___y_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v___y_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u8 = 0;
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1906_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1;
                v___x_1907_ = lean_unsigned_to_nat(3);
                v___x_1908_ = l_Lean_Expr_isAppOfArity(v_eq_1900_, v___x_1906_, v___x_1907_);
                if v___x_1908_ == 0 {
                    v___x_1909_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3,
                    );
                    v___x_1910_ = l_Lean_MessageData_ofExpr(v___x_1895_);
                    v___x_1911_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1911_, 0, v___x_1909_);
                    lean_ctor_set(v___x_1911_, 1, v___x_1910_);
                    v___x_1912_ = l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___redArg(v___x_1911_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
                    return v___x_1912_;
                } else {
                    v___x_1913_ = l_Lean_Expr_appFn_x21(v_eq_1900_);
                    v___x_1914_ = l_Lean_Expr_appArg_x21(v___x_1913_);
                    lean_dec_ref(v___x_1913_);
                    v___x_1915_ = l_Lean_Expr_appArg_x21(v_eq_1900_);
                    v___x_1958_ = l_Lean_Expr_getAppFn(v___x_1914_);
                    v___x_1959_ = l_Lean_Expr_isConstOf(v___x_1958_, v_declName_1898_);
                    lean_dec_ref(v___x_1958_);
                    if v___x_1959_ == 0 {
                        lean_dec_ref(v___x_1915_);
                        lean_dec_ref(v___x_1914_);
                        v___x_1960_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3,
                        );
                        v___x_1961_ = l_Lean_MessageData_ofExpr(v___x_1895_);
                        v___x_1962_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1962_, 0, v___x_1960_);
                        lean_ctor_set(v___x_1962_, 1, v___x_1961_);
                        v___x_1963_ = l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___redArg(v___x_1962_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
                        v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
                        v_isSharedCheck_1971_ = (!lean_is_exclusive(v___x_1963_)) as u8;
                        if v_isSharedCheck_1971_ == 0 {
                            v___x_1966_ = v___x_1963_;
                            v_isShared_1967_ = v_isSharedCheck_1971_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1964_);
                            lean_dec(v___x_1963_);
                            v___x_1966_ = lean_box(0);
                            v_isShared_1967_ = v_isSharedCheck_1971_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___y_1944_ = v___y_1901_;
                        v___y_1945_ = v___y_1902_;
                        v___y_1946_ = v___y_1903_;
                        v___y_1947_ = v___y_1904_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1921_ = 1;
                v___x_1922_ = l_Lean_Meta_mkLambdaFVars(
                    v_xs_1899_,
                    v___x_1915_,
                    v___x_1896_,
                    v___x_1897_,
                    v___x_1896_,
                    v___x_1897_,
                    v___x_1921_,
                    v___y_1917_,
                    v___y_1918_,
                    v___y_1919_,
                    v___y_1920_,
                );
                if lean_obj_tag(v___x_1922_) == 0 {
                    v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
                    lean_inc(v_a_1923_);
                    lean_dec_ref_known(v___x_1922_, 1);
                    v___x_1924_ = l_Lean_Expr_getAppFn(v___x_1914_);
                    lean_dec_ref(v___x_1914_);
                    v___x_1925_ = l_Lean_Meta_mkEq(
                        v___x_1924_,
                        v_a_1923_,
                        v___y_1917_,
                        v___y_1918_,
                        v___y_1919_,
                        v___y_1920_,
                    );
                    return v___x_1925_;
                } else {
                    lean_dec_ref(v___x_1914_);
                    return v___x_1922_;
                }
            }
            2 => {
                v___x_1931_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3,
                );
                v___x_1932_ = l_Lean_MessageData_ofExpr(v___x_1895_);
                v___x_1933_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1933_, 0, v___x_1931_);
                lean_ctor_set(v___x_1933_, 1, v___x_1932_);
                v___x_1934_ =
                    l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___redArg(
                        v___x_1933_,
                        v___y_1929_,
                        v___y_1927_,
                        v___y_1928_,
                        v___y_1930_,
                    );
                v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
                v_isSharedCheck_1942_ = (!lean_is_exclusive(v___x_1934_)) as u8;
                if v_isSharedCheck_1942_ == 0 {
                    v___x_1937_ = v___x_1934_;
                    v_isShared_1938_ = v_isSharedCheck_1942_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_1935_);
                    lean_dec(v___x_1934_);
                    v___x_1937_ = lean_box(0);
                    v_isShared_1938_ = v_isSharedCheck_1942_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1938_ == 0 {
                    v___x_1940_ = v___x_1937_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
                    v___x_1940_ = v_reuseFailAlloc_1941_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1940_;
            }
            5 => {
                v_dummy_1948_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4_once
                    ),
                    _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4,
                );
                v_nargs_1949_ = l_Lean_Expr_getAppNumArgs(v___x_1914_);
                lean_inc(v_nargs_1949_);
                v___x_1950_ = lean_mk_array(v_nargs_1949_, v_dummy_1948_);
                v___x_1951_ = lean_unsigned_to_nat(1);
                v___x_1952_ = lean_nat_sub(v_nargs_1949_, v___x_1951_);
                lean_dec(v_nargs_1949_);
                lean_inc_ref(v___x_1914_);
                v___x_1953_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v___x_1914_,
                    v___x_1950_,
                    v___x_1952_,
                );
                v___x_1954_ = lean_array_get_size(v___x_1953_);
                v___x_1955_ = lean_array_get_size(v_xs_1899_);
                v___x_1956_ = lean_nat_dec_eq(v___x_1954_, v___x_1955_);
                if v___x_1956_ == 0 {
                    lean_dec_ref(v___x_1953_);
                    lean_dec_ref(v___x_1915_);
                    lean_dec_ref(v___x_1914_);
                    v___y_1927_ = v___y_1945_;
                    v___y_1928_ = v___y_1946_;
                    v___y_1929_ = v___y_1944_;
                    v___y_1930_ = v___y_1947_;
                    state = 2;
                    continue;
                } else {
                    v___x_1957_ = l_Array_isEqvAux___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__5___redArg(v___x_1953_, v_xs_1899_, v___x_1954_);
                    lean_dec_ref(v___x_1953_);
                    if v___x_1957_ == 0 {
                        lean_dec_ref(v___x_1915_);
                        lean_dec_ref(v___x_1914_);
                        v___y_1927_ = v___y_1945_;
                        v___y_1928_ = v___y_1946_;
                        v___y_1929_ = v___y_1944_;
                        v___y_1930_ = v___y_1947_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v___x_1895_);
                        v___y_1917_ = v___y_1944_;
                        v___y_1918_ = v___y_1945_;
                        v___y_1919_ = v___y_1946_;
                        v___y_1920_ = v___y_1947_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1967_ == 0 {
                    v___x_1969_ = v___x_1966_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
                    v___x_1969_ = v_reuseFailAlloc_1970_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___boxed(
    mut v___x_1972_: *mut LeanObject,
    mut v___x_1973_: *mut LeanObject,
    mut v___x_1974_: *mut LeanObject,
    mut v_declName_1975_: *mut LeanObject,
    mut v_xs_1976_: *mut LeanObject,
    mut v_eq_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_12673__boxed_1983_: u8 = 0;
    let mut v___x_12674__boxed_1984_: u8 = 0;
    let mut v_res_1985_: *mut LeanObject = core::ptr::null_mut();
    v___x_12673__boxed_1983_ = (lean_unbox(v___x_1973_) as u8);
    v___x_12674__boxed_1984_ = (lean_unbox(v___x_1974_) as u8);
    v_res_1985_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0(
        v___x_1972_,
        v___x_12673__boxed_1983_,
        v___x_12674__boxed_1984_,
        v_declName_1975_,
        v_xs_1976_,
        v_eq_1977_,
        v___y_1978_,
        v___y_1979_,
        v___y_1980_,
        v___y_1981_,
    );
    lean_dec(v___y_1981_);
    lean_dec_ref(v___y_1980_);
    lean_dec(v___y_1979_);
    lean_dec_ref(v___y_1978_);
    lean_dec_ref(v_eq_1977_);
    lean_dec_ref(v_xs_1976_);
    lean_dec(v_declName_1975_);
    return v_res_1985_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    v___x_1986_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1986_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    v___x_1987_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__0);
    v___x_1988_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1988_, 0, v___x_1987_);
    return v___x_1988_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    v___x_1989_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1);
    v___x_1990_ = lean_unsigned_to_nat(0);
    v___x_1991_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1991_, 0, v___x_1990_);
    lean_ctor_set(v___x_1991_, 1, v___x_1990_);
    lean_ctor_set(v___x_1991_, 2, v___x_1990_);
    lean_ctor_set(v___x_1991_, 3, v___x_1990_);
    lean_ctor_set(v___x_1991_, 4, v___x_1989_);
    lean_ctor_set(v___x_1991_, 5, v___x_1989_);
    lean_ctor_set(v___x_1991_, 6, v___x_1989_);
    lean_ctor_set(v___x_1991_, 7, v___x_1989_);
    lean_ctor_set(v___x_1991_, 8, v___x_1989_);
    lean_ctor_set(v___x_1991_, 9, v___x_1989_);
    return v___x_1991_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    v___x_1992_ = lean_unsigned_to_nat(32);
    v___x_1993_ = lean_mk_empty_array_with_capacity(v___x_1992_);
    v___x_1994_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1994_, 0, v___x_1993_);
    return v___x_1994_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1995_ = 5usize;
    v___x_1996_ = lean_unsigned_to_nat(0);
    v___x_1997_ = lean_unsigned_to_nat(32);
    v___x_1998_ = lean_mk_empty_array_with_capacity(v___x_1997_);
    v___x_1999_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__3);
    v___x_2000_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2000_, 0, v___x_1999_);
    lean_ctor_set(v___x_2000_, 1, v___x_1998_);
    lean_ctor_set(v___x_2000_, 2, v___x_1996_);
    lean_ctor_set(v___x_2000_, 3, v___x_1996_);
    lean_ctor_set_usize(v___x_2000_, 4, v___x_1995_);
    return v___x_2000_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    v___x_2001_ = lean_box(1);
    v___x_2002_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4);
    v___x_2003_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__1);
    v___x_2004_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2004_, 0, v___x_2003_);
    lean_ctor_set(v___x_2004_, 1, v___x_2002_);
    lean_ctor_set(v___x_2004_, 2, v___x_2001_);
    return v___x_2004_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    v___x_2006_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__6;
    v___x_2007_ = l_Lean_stringToMessageData(v___x_2006_);
    return v___x_2007_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__8;
    v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
    return v___x_2010_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__10;
    v___x_2013_ = l_Lean_stringToMessageData(v___x_2012_);
    return v___x_2013_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__12;
    v___x_2016_ = l_Lean_stringToMessageData(v___x_2015_);
    return v___x_2016_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    v___x_2018_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__14;
    v___x_2019_ = l_Lean_stringToMessageData(v___x_2018_);
    return v___x_2019_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    v___x_2021_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__16;
    v___x_2022_ = l_Lean_stringToMessageData(v___x_2021_);
    return v___x_2022_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    v___x_2024_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__18;
    v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
    return v___x_2025_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg(
    mut v_msg_2026_: *mut LeanObject,
    mut v_declHint_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: u8 = 0;
    let mut v_isExporting_2033_: u8 = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2055_: u8 = 0;
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: u8 = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2087_: u8 = 0;
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2030_ = lean_st_ref_get(v___y_2028_);
                v_env_2031_ = lean_ctor_get(v___x_2030_, 0);
                lean_inc_ref(v_env_2031_);
                lean_dec(v___x_2030_);
                v___x_2032_ = l_Lean_Name_isAnonymous(v_declHint_2027_);
                if v___x_2032_ == 0 {
                    v_isExporting_2033_ = lean_ctor_get_uint8(
                        v_env_2031_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2033_ == 0 {
                        lean_dec_ref(v_env_2031_);
                        lean_dec(v_declHint_2027_);
                        v___x_2034_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2034_, 0, v_msg_2026_);
                        return v___x_2034_;
                    } else {
                        lean_inc_ref(v_env_2031_);
                        v___x_2035_ = l_Lean_Environment_setExporting(v_env_2031_, v___x_2032_);
                        lean_inc(v_declHint_2027_);
                        lean_inc_ref(v___x_2035_);
                        v___x_2036_ = l_Lean_Environment_contains(
                            v___x_2035_,
                            v_declHint_2027_,
                            v_isExporting_2033_,
                        );
                        if v___x_2036_ == 0 {
                            lean_dec_ref(v___x_2035_);
                            lean_dec_ref(v_env_2031_);
                            lean_dec(v_declHint_2027_);
                            v___x_2037_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2037_, 0, v_msg_2026_);
                            return v___x_2037_;
                        } else {
                            v___x_2038_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__2);
                            v___x_2039_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__5);
                            v___x_2040_ = l_Lean_Options_empty;
                            v___x_2041_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_2041_, 0, v___x_2035_);
                            lean_ctor_set(v___x_2041_, 1, v___x_2038_);
                            lean_ctor_set(v___x_2041_, 2, v___x_2039_);
                            lean_ctor_set(v___x_2041_, 3, v___x_2040_);
                            lean_inc(v_declHint_2027_);
                            v___x_2042_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2027_, v___x_2032_);
                            v_c_2043_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_2043_, 0, v___x_2041_);
                            lean_ctor_set(v_c_2043_, 1, v___x_2042_);
                            v___x_2044_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2031_,
                                v_declHint_2027_,
                            );
                            if lean_obj_tag(v___x_2044_) == 0 {
                                lean_dec_ref(v_env_2031_);
                                lean_dec(v_declHint_2027_);
                                v___x_2045_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7);
                                v___x_2046_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2046_, 0, v___x_2045_);
                                lean_ctor_set(v___x_2046_, 1, v_c_2043_);
                                v___x_2047_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__9);
                                v___x_2048_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2048_, 0, v___x_2046_);
                                lean_ctor_set(v___x_2048_, 1, v___x_2047_);
                                v___x_2049_ = l_Lean_MessageData_note(v___x_2048_);
                                v___x_2050_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2050_, 0, v_msg_2026_);
                                lean_ctor_set(v___x_2050_, 1, v___x_2049_);
                                v___x_2051_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2051_, 0, v___x_2050_);
                                return v___x_2051_;
                            } else {
                                v_val_2052_ = lean_ctor_get(v___x_2044_, 0);
                                v_isSharedCheck_2087_ = (!lean_is_exclusive(v___x_2044_)) as u8;
                                if v_isSharedCheck_2087_ == 0 {
                                    v___x_2054_ = v___x_2044_;
                                    v_isShared_2055_ = v_isSharedCheck_2087_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_2052_);
                                    lean_dec(v___x_2044_);
                                    v___x_2054_ = lean_box(0);
                                    v_isShared_2055_ = v_isSharedCheck_2087_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_2031_);
                    lean_dec(v_declHint_2027_);
                    v___x_2088_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2088_, 0, v_msg_2026_);
                    return v___x_2088_;
                }
            }
            1 => {
                v___x_2056_ = lean_box(0);
                v___x_2057_ = l_Lean_Environment_header(v_env_2031_);
                lean_dec_ref(v_env_2031_);
                v___x_2058_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2057_);
                v_mod_2059_ = lean_array_get(v___x_2056_, v___x_2058_, v_val_2052_);
                lean_dec(v_val_2052_);
                lean_dec_ref(v___x_2058_);
                v___x_2060_ = l_Lean_isPrivateName(v_declHint_2027_);
                lean_dec(v_declHint_2027_);
                if v___x_2060_ == 0 {
                    v___x_2061_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__11);
                    v___x_2062_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2062_, 0, v___x_2061_);
                    lean_ctor_set(v___x_2062_, 1, v_c_2043_);
                    v___x_2063_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__13);
                    v___x_2064_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2064_, 0, v___x_2062_);
                    lean_ctor_set(v___x_2064_, 1, v___x_2063_);
                    v___x_2065_ = l_Lean_MessageData_ofName(v_mod_2059_);
                    v___x_2066_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2066_, 0, v___x_2064_);
                    lean_ctor_set(v___x_2066_, 1, v___x_2065_);
                    v___x_2067_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__15);
                    v___x_2068_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2068_, 0, v___x_2066_);
                    lean_ctor_set(v___x_2068_, 1, v___x_2067_);
                    v___x_2069_ = l_Lean_MessageData_note(v___x_2068_);
                    v___x_2070_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2070_, 0, v_msg_2026_);
                    lean_ctor_set(v___x_2070_, 1, v___x_2069_);
                    if v_isShared_2055_ == 0 {
                        lean_ctor_set_tag(v___x_2054_, 0);
                        lean_ctor_set(v___x_2054_, 0, v___x_2070_);
                        v___x_2072_ = v___x_2054_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
                        v___x_2072_ = v_reuseFailAlloc_2073_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2074_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__7);
                    v___x_2075_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2075_, 0, v___x_2074_);
                    lean_ctor_set(v___x_2075_, 1, v_c_2043_);
                    v___x_2076_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__17);
                    v___x_2077_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2077_, 0, v___x_2075_);
                    lean_ctor_set(v___x_2077_, 1, v___x_2076_);
                    v___x_2078_ = l_Lean_MessageData_ofName(v_mod_2059_);
                    v___x_2079_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2079_, 0, v___x_2077_);
                    lean_ctor_set(v___x_2079_, 1, v___x_2078_);
                    v___x_2080_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__19);
                    v___x_2081_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2081_, 0, v___x_2079_);
                    lean_ctor_set(v___x_2081_, 1, v___x_2080_);
                    v___x_2082_ = l_Lean_MessageData_note(v___x_2081_);
                    v___x_2083_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2083_, 0, v_msg_2026_);
                    lean_ctor_set(v___x_2083_, 1, v___x_2082_);
                    if v_isShared_2055_ == 0 {
                        lean_ctor_set_tag(v___x_2054_, 0);
                        lean_ctor_set(v___x_2054_, 0, v___x_2083_);
                        v___x_2085_ = v___x_2054_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
                        v___x_2085_ = v_reuseFailAlloc_2086_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2072_;
            }
            3 => {
                return v___x_2085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___boxed(
    mut v_msg_2089_: *mut LeanObject,
    mut v_declHint_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2093_: *mut LeanObject = core::ptr::null_mut();
    v_res_2093_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg(v_msg_2089_, v_declHint_2090_, v___y_2091_);
    lean_dec(v___y_2091_);
    return v_res_2093_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15(
    mut v_msg_2094_: *mut LeanObject,
    mut v_declHint_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2105_: u8 = 0;
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2101_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg(v_msg_2094_, v_declHint_2095_, v___y_2099_);
                v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
                v_isSharedCheck_2111_ = (!lean_is_exclusive(v___x_2101_)) as u8;
                if v_isSharedCheck_2111_ == 0 {
                    v___x_2104_ = v___x_2101_;
                    v_isShared_2105_ = v_isSharedCheck_2111_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2102_);
                    lean_dec(v___x_2101_);
                    v___x_2104_ = lean_box(0);
                    v_isShared_2105_ = v_isSharedCheck_2111_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2106_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2107_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2107_, 0, v___x_2106_);
                lean_ctor_set(v___x_2107_, 1, v_a_2102_);
                if v_isShared_2105_ == 0 {
                    lean_ctor_set(v___x_2104_, 0, v___x_2107_);
                    v___x_2109_ = v___x_2104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
                    v___x_2109_ = v_reuseFailAlloc_2110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15___boxed(
    mut v_msg_2112_: *mut LeanObject,
    mut v_declHint_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2119_: *mut LeanObject = core::ptr::null_mut();
    v_res_2119_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15(v_msg_2112_, v_declHint_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
    lean_dec(v___y_2117_);
    lean_dec_ref(v___y_2116_);
    lean_dec(v___y_2115_);
    lean_dec_ref(v___y_2114_);
    return v_res_2119_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__16___redArg(
    mut v_ref_2120_: *mut LeanObject,
    mut v_msg_2121_: *mut LeanObject,
    mut v___y_2122_: *mut LeanObject,
    mut v___y_2123_: *mut LeanObject,
    mut v___y_2124_: *mut LeanObject,
    mut v___y_2125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2139_: u8 = 0;
    let mut v_cancelTk_x3f_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2141_: u8 = 0;
    let mut v_inheritedTraceOptions_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2127_ = lean_ctor_get(v___y_2124_, 0);
    v_fileMap_2128_ = lean_ctor_get(v___y_2124_, 1);
    v_options_2129_ = lean_ctor_get(v___y_2124_, 2);
    v_currRecDepth_2130_ = lean_ctor_get(v___y_2124_, 3);
    v_maxRecDepth_2131_ = lean_ctor_get(v___y_2124_, 4);
    v_ref_2132_ = lean_ctor_get(v___y_2124_, 5);
    v_currNamespace_2133_ = lean_ctor_get(v___y_2124_, 6);
    v_openDecls_2134_ = lean_ctor_get(v___y_2124_, 7);
    v_initHeartbeats_2135_ = lean_ctor_get(v___y_2124_, 8);
    v_maxHeartbeats_2136_ = lean_ctor_get(v___y_2124_, 9);
    v_quotContext_2137_ = lean_ctor_get(v___y_2124_, 10);
    v_currMacroScope_2138_ = lean_ctor_get(v___y_2124_, 11);
    v_diag_2139_ = lean_ctor_get_uint8(
        v___y_2124_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2140_ = lean_ctor_get(v___y_2124_, 12);
    v_suppressElabErrors_2141_ = lean_ctor_get_uint8(
        v___y_2124_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2142_ = lean_ctor_get(v___y_2124_, 13);
    v_ref_2143_ = l_Lean_replaceRef(v_ref_2120_, v_ref_2132_);
    lean_inc_ref(v_inheritedTraceOptions_2142_);
    lean_inc(v_cancelTk_x3f_2140_);
    lean_inc(v_currMacroScope_2138_);
    lean_inc(v_quotContext_2137_);
    lean_inc(v_maxHeartbeats_2136_);
    lean_inc(v_initHeartbeats_2135_);
    lean_inc(v_openDecls_2134_);
    lean_inc(v_currNamespace_2133_);
    lean_inc(v_maxRecDepth_2131_);
    lean_inc(v_currRecDepth_2130_);
    lean_inc_ref(v_options_2129_);
    lean_inc_ref(v_fileMap_2128_);
    lean_inc_ref(v_fileName_2127_);
    v___x_2144_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2144_, 0, v_fileName_2127_);
    lean_ctor_set(v___x_2144_, 1, v_fileMap_2128_);
    lean_ctor_set(v___x_2144_, 2, v_options_2129_);
    lean_ctor_set(v___x_2144_, 3, v_currRecDepth_2130_);
    lean_ctor_set(v___x_2144_, 4, v_maxRecDepth_2131_);
    lean_ctor_set(v___x_2144_, 5, v_ref_2143_);
    lean_ctor_set(v___x_2144_, 6, v_currNamespace_2133_);
    lean_ctor_set(v___x_2144_, 7, v_openDecls_2134_);
    lean_ctor_set(v___x_2144_, 8, v_initHeartbeats_2135_);
    lean_ctor_set(v___x_2144_, 9, v_maxHeartbeats_2136_);
    lean_ctor_set(v___x_2144_, 10, v_quotContext_2137_);
    lean_ctor_set(v___x_2144_, 11, v_currMacroScope_2138_);
    lean_ctor_set(v___x_2144_, 12, v_cancelTk_x3f_2140_);
    lean_ctor_set(v___x_2144_, 13, v_inheritedTraceOptions_2142_);
    lean_ctor_set_uint8(
        v___x_2144_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2139_,
    );
    lean_ctor_set_uint8(
        v___x_2144_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2141_,
    );
    v___x_2145_ = l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___redArg(
        v_msg_2121_,
        v___y_2122_,
        v___y_2123_,
        v___x_2144_,
        v___y_2125_,
    );
    lean_dec_ref_known(v___x_2144_, 14);
    return v___x_2145_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__16___redArg___boxed(
    mut v_ref_2146_: *mut LeanObject,
    mut v_msg_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2153_: *mut LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_2146_, v_msg_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
    lean_dec(v___y_2151_);
    lean_dec_ref(v___y_2150_);
    lean_dec(v___y_2149_);
    lean_dec_ref(v___y_2148_);
    lean_dec(v_ref_2146_);
    return v_res_2153_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14___redArg(
    mut v_ref_2154_: *mut LeanObject,
    mut v_msg_2155_: *mut LeanObject,
    mut v_declHint_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
    mut v___y_2159_: *mut LeanObject,
    mut v___y_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15(v_msg_2155_, v_declHint_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
    v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
    lean_inc(v_a_2163_);
    lean_dec_ref(v___x_2162_);
    v___x_2164_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_2154_, v_a_2163_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
    return v___x_2164_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14___redArg___boxed(
    mut v_ref_2165_: *mut LeanObject,
    mut v_msg_2166_: *mut LeanObject,
    mut v_declHint_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
    mut v___y_2169_: *mut LeanObject,
    mut v___y_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2173_: *mut LeanObject = core::ptr::null_mut();
    v_res_2173_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14___redArg(v_ref_2165_, v_msg_2166_, v_declHint_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
    lean_dec(v___y_2171_);
    lean_dec_ref(v___y_2170_);
    lean_dec(v___y_2169_);
    lean_dec_ref(v___y_2168_);
    lean_dec(v_ref_2165_);
    return v_res_2173_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    v___x_2175_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__0;
    v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
    return v___x_2176_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__2;
    v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
    return v___x_2179_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg(
    mut v_ref_2180_: *mut LeanObject,
    mut v_constName_2181_: *mut LeanObject,
    mut v___y_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
    mut v___y_2184_: *mut LeanObject,
    mut v___y_2185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    v___x_2187_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__1);
    v___x_2188_ = 0;
    lean_inc(v_constName_2181_);
    v___x_2189_ = l_Lean_MessageData_ofConstName(v_constName_2181_, v___x_2188_);
    v___x_2190_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2190_, 0, v___x_2187_);
    lean_ctor_set(v___x_2190_, 1, v___x_2189_);
    v___x_2191_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___closed__3);
    v___x_2192_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2192_, 0, v___x_2190_);
    lean_ctor_set(v___x_2192_, 1, v___x_2191_);
    v___x_2193_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14___redArg(v_ref_2180_, v___x_2192_, v_constName_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
    return v___x_2193_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg___boxed(
    mut v_ref_2194_: *mut LeanObject,
    mut v_constName_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
    mut v___y_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2201_: *mut LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg(v_ref_2194_, v_constName_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
    lean_dec(v___y_2199_);
    lean_dec_ref(v___y_2198_);
    lean_dec(v___y_2197_);
    lean_dec_ref(v___y_2196_);
    lean_dec(v_ref_2194_);
    return v_res_2201_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6___redArg(
    mut v_constName_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2208_ = lean_ctor_get(v___y_2205_, 5);
    v___x_2209_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg(v_ref_2208_, v_constName_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
    return v___x_2209_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6___redArg___boxed(
    mut v_constName_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
    mut v___y_2213_: *mut LeanObject,
    mut v___y_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2216_: *mut LeanObject = core::ptr::null_mut();
    v_res_2216_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6___redArg(v_constName_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
    lean_dec(v___y_2214_);
    lean_dec_ref(v___y_2213_);
    lean_dec(v___y_2212_);
    lean_dec_ref(v___y_2211_);
    return v_res_2216_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1_spec__2(
    mut v_constName_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2223_ = lean_st_ref_get(v___y_2221_);
                v_env_2224_ = lean_ctor_get(v___x_2223_, 0);
                lean_inc_ref(v_env_2224_);
                lean_dec(v___x_2223_);
                v___x_2225_ = 0;
                lean_inc(v_constName_2217_);
                v___x_2226_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2224_,
                    v_constName_2217_,
                    v___x_2225_,
                );
                if lean_obj_tag(v___x_2226_) == 0 {
                    v___x_2227_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6___redArg(v_constName_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
                    return v___x_2227_;
                } else {
                    lean_dec(v_constName_2217_);
                    v_val_2228_ = lean_ctor_get(v___x_2226_, 0);
                    v_isSharedCheck_2235_ = (!lean_is_exclusive(v___x_2226_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2230_ = v___x_2226_;
                        v_isShared_2231_ = v_isSharedCheck_2235_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2228_);
                        lean_dec(v___x_2226_);
                        v___x_2230_ = lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2235_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2231_ == 0 {
                    lean_ctor_set_tag(v___x_2230_, 0);
                    v___x_2233_ = v___x_2230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_val_2228_);
                    v___x_2233_ = v_reuseFailAlloc_2234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1_spec__2___boxed(
    mut v_constName_2236_: *mut LeanObject,
    mut v___y_2237_: *mut LeanObject,
    mut v___y_2238_: *mut LeanObject,
    mut v___y_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
    mut v___y_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2242_: *mut LeanObject = core::ptr::null_mut();
    v_res_2242_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1_spec__2(v_constName_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
    lean_dec(v___y_2240_);
    lean_dec_ref(v___y_2239_);
    lean_dec(v___y_2238_);
    lean_dec_ref(v___y_2237_);
    return v_res_2242_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1_spec__3(
    mut v_a_2243_: *mut LeanObject,
    mut v_a_2244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2243_) == 0 {
                    v___x_2245_ = l_List_reverse___redArg(v_a_2244_);
                    return v___x_2245_;
                } else {
                    v_head_2246_ = lean_ctor_get(v_a_2243_, 0);
                    v_tail_2247_ = lean_ctor_get(v_a_2243_, 1);
                    v_isSharedCheck_2256_ = (!lean_is_exclusive(v_a_2243_)) as u8;
                    if v_isSharedCheck_2256_ == 0 {
                        v___x_2249_ = v_a_2243_;
                        v_isShared_2250_ = v_isSharedCheck_2256_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2247_);
                        lean_inc(v_head_2246_);
                        lean_dec(v_a_2243_);
                        v___x_2249_ = lean_box(0);
                        v_isShared_2250_ = v_isSharedCheck_2256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2251_ = l_Lean_mkLevelParam(v_head_2246_);
                if v_isShared_2250_ == 0 {
                    lean_ctor_set(v___x_2249_, 1, v_a_2244_);
                    lean_ctor_set(v___x_2249_, 0, v___x_2251_);
                    v___x_2253_ = v___x_2249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2251_);
                    lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_a_2244_);
                    v___x_2253_ = v_reuseFailAlloc_2255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2243_ = v_tail_2247_;
                v_a_2244_ = v___x_2253_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1(
    mut v_constName_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v_levelParams_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_a_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_2257_);
                v___x_2263_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1_spec__2(v_constName_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
                if lean_obj_tag(v___x_2263_) == 0 {
                    v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
                    v_isSharedCheck_2275_ = (!lean_is_exclusive(v___x_2263_)) as u8;
                    if v_isSharedCheck_2275_ == 0 {
                        v___x_2266_ = v___x_2263_;
                        v_isShared_2267_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2264_);
                        lean_dec(v___x_2263_);
                        v___x_2266_ = lean_box(0);
                        v_isShared_2267_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_2257_);
                    v_a_2276_ = lean_ctor_get(v___x_2263_, 0);
                    v_isSharedCheck_2283_ = (!lean_is_exclusive(v___x_2263_)) as u8;
                    if v_isSharedCheck_2283_ == 0 {
                        v___x_2278_ = v___x_2263_;
                        v_isShared_2279_ = v_isSharedCheck_2283_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2276_);
                        lean_dec(v___x_2263_);
                        v___x_2278_ = lean_box(0);
                        v_isShared_2279_ = v_isSharedCheck_2283_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_2268_ = lean_ctor_get(v_a_2264_, 1);
                lean_inc(v_levelParams_2268_);
                lean_dec(v_a_2264_);
                v___x_2269_ = lean_box(0);
                v___x_2270_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1_spec__3(v_levelParams_2268_, v___x_2269_);
                v___x_2271_ = l_Lean_mkConst(v_constName_2257_, v___x_2270_);
                if v_isShared_2267_ == 0 {
                    lean_ctor_set(v___x_2266_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2273_;
            }
            3 => {
                if v_isShared_2279_ == 0 {
                    v___x_2281_ = v___x_2278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
                    v___x_2281_ = v_reuseFailAlloc_2282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1___boxed(
    mut v_constName_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2290_: *mut LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1(
        v_constName_2284_,
        v___y_2285_,
        v___y_2286_,
        v___y_2287_,
        v___y_2288_,
    );
    lean_dec(v___y_2288_);
    lean_dec_ref(v___y_2287_);
    lean_dec(v___y_2286_);
    lean_dec_ref(v___y_2285_);
    return v_res_2290_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2(
    mut v_as_2294_: *mut LeanObject,
    mut v_sz_2295_: usize,
    mut v_i_2296_: usize,
    mut v_b_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v_a_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: usize = 0;
    let mut v___x_2318_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2303_ = lean_usize_dec_lt(v_i_2296_, v_sz_2295_);
                if v___x_2303_ == 0 {
                    v___x_2304_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2304_, 0, v_b_2297_);
                    return v___x_2304_;
                } else {
                    v___x_2305_ = 0;
                    v_a_2306_ = lean_array_uget_borrowed(v_as_2294_, v_i_2296_);
                    v___x_2307_ = lean_unsigned_to_nat(1);
                    v___x_2308_ = lean_mk_empty_array_with_capacity(v___x_2307_);
                    lean_inc(v_a_2306_);
                    lean_inc_ref(v___x_2308_);
                    v___x_2309_ = lean_array_push(v___x_2308_, v_a_2306_);
                    v___x_2310_ = 1;
                    v___x_2311_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_2309_,
                        v_b_2297_,
                        v___x_2305_,
                        v___x_2303_,
                        v___x_2305_,
                        v___x_2303_,
                        v___x_2310_,
                        v___y_2298_,
                        v___y_2299_,
                        v___y_2300_,
                        v___y_2301_,
                    );
                    lean_dec_ref(v___x_2309_);
                    if lean_obj_tag(v___x_2311_) == 0 {
                        v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
                        lean_inc(v_a_2312_);
                        lean_dec_ref_known(v___x_2311_, 1);
                        v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___closed__1;
                        v___x_2314_ = lean_array_push(v___x_2308_, v_a_2312_);
                        v___x_2315_ = l_Lean_Meta_mkAppM(
                            v___x_2313_,
                            v___x_2314_,
                            v___y_2298_,
                            v___y_2299_,
                            v___y_2300_,
                            v___y_2301_,
                        );
                        if lean_obj_tag(v___x_2315_) == 0 {
                            v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
                            lean_inc(v_a_2316_);
                            lean_dec_ref_known(v___x_2315_, 1);
                            v___x_2317_ = 1usize;
                            v___x_2318_ = lean_usize_add(v_i_2296_, v___x_2317_);
                            v_i_2296_ = v___x_2318_;
                            v_b_2297_ = v_a_2316_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2315_;
                        }
                    } else {
                        lean_dec_ref(v___x_2308_);
                        return v___x_2311_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2___boxed(
    mut v_as_2320_: *mut LeanObject,
    mut v_sz_2321_: *mut LeanObject,
    mut v_i_2322_: *mut LeanObject,
    mut v_b_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2329_: usize = 0;
    let mut v_i_boxed_2330_: usize = 0;
    let mut v_res_2331_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2329_ = lean_unbox_usize(v_sz_2321_);
    lean_dec(v_sz_2321_);
    v_i_boxed_2330_ = lean_unbox_usize(v_i_2322_);
    lean_dec(v_i_2322_);
    v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2(v_as_2320_, v_sz_boxed_2329_, v_i_boxed_2330_, v_b_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
    lean_dec(v___y_2327_);
    lean_dec_ref(v___y_2326_);
    lean_dec(v___y_2325_);
    lean_dec_ref(v___y_2324_);
    lean_dec_ref(v_as_2320_);
    return v_res_2331_;
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1(
    mut v_val_2332_: *mut LeanObject,
    mut v_xs_2333_: *mut LeanObject,
    mut v___eq_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    v___x_2340_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__1(
        v_val_2332_,
        v___y_2335_,
        v___y_2336_,
        v___y_2337_,
        v___y_2338_,
    );
    if lean_obj_tag(v___x_2340_) == 0 {
        let mut v_a_2341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_2344_: usize = 0;
        let mut v___x_2345_: usize = 0;
        let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
        v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
        lean_inc(v_a_2341_);
        lean_dec_ref_known(v___x_2340_, 1);
        v___x_2342_ = l_Lean_mkAppN(v_a_2341_, v_xs_2333_);
        v___x_2343_ = l_Array_reverse___redArg(v_xs_2333_);
        v_sz_2344_ = lean_array_size(v___x_2343_);
        v___x_2345_ = 0usize;
        v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__2(v___x_2343_, v_sz_2344_, v___x_2345_, v___x_2342_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
        lean_dec_ref(v___x_2343_);
        return v___x_2346_;
    } else {
        lean_dec_ref(v_xs_2333_);
        return v___x_2340_;
    }
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1___boxed(
    mut v_val_2347_: *mut LeanObject,
    mut v_xs_2348_: *mut LeanObject,
    mut v___eq_2349_: *mut LeanObject,
    mut v___y_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
    mut v___y_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2355_: *mut LeanObject = core::ptr::null_mut();
    v_res_2355_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1(
        v_val_2347_,
        v_xs_2348_,
        v___eq_2349_,
        v___y_2350_,
        v___y_2351_,
        v___y_2352_,
        v___y_2353_,
    );
    lean_dec(v___y_2353_);
    lean_dec_ref(v___y_2352_);
    lean_dec(v___y_2351_);
    lean_dec_ref(v___y_2350_);
    lean_dec_ref(v___eq_2349_);
    return v_res_2355_;
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2(
    mut v_a_2356_: *mut LeanObject,
    mut v___x_2357_: *mut LeanObject,
    mut v___x_2358_: *mut LeanObject,
    mut v___f_2359_: *mut LeanObject,
    mut v___x_2360_: u8,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2366_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v_a_2356_,
                    v___x_2357_,
                    v___y_2361_,
                    v___y_2362_,
                    v___y_2363_,
                    v___y_2364_,
                );
                if lean_obj_tag(v___x_2366_) == 0 {
                    v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
                    lean_inc(v_a_2367_);
                    lean_dec_ref_known(v___x_2366_, 1);
                    v___x_2368_ = l_Lean_Expr_mvarId_x21(v_a_2367_);
                    v___x_2369_ = l_Lean_Meta_tryURefl(
                        v___x_2368_,
                        v___y_2361_,
                        v___y_2362_,
                        v___y_2363_,
                        v___y_2364_,
                    );
                    if lean_obj_tag(v___x_2369_) == 0 {
                        v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
                        lean_inc(v_a_2370_);
                        lean_dec_ref_known(v___x_2369_, 1);
                        v___x_2371_ = (lean_unbox(v_a_2370_) as u8);
                        lean_dec(v_a_2370_);
                        if v___x_2371_ == 0 {
                            lean_dec(v_a_2367_);
                            v___x_2372_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg(v___x_2358_, v___f_2359_, v___x_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
                            return v___x_2372_;
                        } else {
                            lean_dec_ref(v___f_2359_);
                            lean_dec_ref(v___x_2358_);
                            v___x_2373_ = l_Lean_instantiateMVars___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__7___redArg(v_a_2367_, v___y_2362_);
                            return v___x_2373_;
                        }
                    } else {
                        lean_dec(v_a_2367_);
                        lean_dec_ref(v___f_2359_);
                        lean_dec_ref(v___x_2358_);
                        v_a_2374_ = lean_ctor_get(v___x_2369_, 0);
                        v_isSharedCheck_2381_ = (!lean_is_exclusive(v___x_2369_)) as u8;
                        if v_isSharedCheck_2381_ == 0 {
                            v___x_2376_ = v___x_2369_;
                            v_isShared_2377_ = v_isSharedCheck_2381_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2374_);
                            lean_dec(v___x_2369_);
                            v___x_2376_ = lean_box(0);
                            v_isShared_2377_ = v_isSharedCheck_2381_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___f_2359_);
                    lean_dec_ref(v___x_2358_);
                    return v___x_2366_;
                }
            }
            1 => {
                if v_isShared_2377_ == 0 {
                    v___x_2379_ = v___x_2376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2___boxed(
    mut v_a_2382_: *mut LeanObject,
    mut v___x_2383_: *mut LeanObject,
    mut v___x_2384_: *mut LeanObject,
    mut v___f_2385_: *mut LeanObject,
    mut v___x_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_13449__boxed_2392_: u8 = 0;
    let mut v_res_2393_: *mut LeanObject = core::ptr::null_mut();
    v___x_13449__boxed_2392_ = (lean_unbox(v___x_2386_) as u8);
    v_res_2393_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2(
        v_a_2382_,
        v___x_2383_,
        v___x_2384_,
        v___f_2385_,
        v___x_13449__boxed_2392_,
        v___y_2387_,
        v___y_2388_,
        v___y_2389_,
        v___y_2390_,
    );
    lean_dec(v___y_2390_);
    lean_dec_ref(v___y_2389_);
    lean_dec(v___y_2388_);
    lean_dec_ref(v___y_2387_);
    return v_res_2393_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3(
    mut v_constName_2394_: *mut LeanObject,
    mut v___y_2395_: *mut LeanObject,
    mut v___y_2396_: *mut LeanObject,
    mut v___y_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2400_ = lean_st_ref_get(v___y_2398_);
                v_env_2401_ = lean_ctor_get(v___x_2400_, 0);
                lean_inc_ref(v_env_2401_);
                lean_dec(v___x_2400_);
                v___x_2402_ = 0;
                lean_inc(v_constName_2394_);
                v___x_2403_ =
                    l_Lean_Environment_find_x3f(v_env_2401_, v_constName_2394_, v___x_2402_);
                if lean_obj_tag(v___x_2403_) == 0 {
                    v___x_2404_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6___redArg(v_constName_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
                    return v___x_2404_;
                } else {
                    lean_dec(v_constName_2394_);
                    v_val_2405_ = lean_ctor_get(v___x_2403_, 0);
                    v_isSharedCheck_2412_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                    if v_isSharedCheck_2412_ == 0 {
                        v___x_2407_ = v___x_2403_;
                        v_isShared_2408_ = v_isSharedCheck_2412_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2405_);
                        lean_dec(v___x_2403_);
                        v___x_2407_ = lean_box(0);
                        v_isShared_2408_ = v_isSharedCheck_2412_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2408_ == 0 {
                    lean_ctor_set_tag(v___x_2407_, 0);
                    v___x_2410_ = v___x_2407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_val_2405_);
                    v___x_2410_ = v_reuseFailAlloc_2411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3___boxed(
    mut v_constName_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2419_: *mut LeanObject = core::ptr::null_mut();
    v_res_2419_ = l_Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3(
        v_constName_2413_,
        v___y_2414_,
        v___y_2415_,
        v___y_2416_,
        v___y_2417_,
    );
    lean_dec(v___y_2417_);
    lean_dec_ref(v___y_2416_);
    lean_dec(v___y_2415_);
    lean_dec_ref(v___y_2414_);
    return v_res_2419_;
}
pub unsafe fn _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3() -> *mut LeanObject {
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2;
    v___x_2424_ = lean_unsigned_to_nat(74);
    v___x_2425_ = lean_unsigned_to_nat(33);
    v___x_2426_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1;
    v___x_2427_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0;
    v___x_2428_ = l_mkPanicMessageWithDecl(
        v___x_2427_,
        v___x_2426_,
        v___x_2425_,
        v___x_2424_,
        v___x_2423_,
    );
    return v___x_2428_;
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3(
    mut v_declName_2429_: *mut LeanObject,
    mut v___x_2430_: u8,
    mut v___x_2431_: u8,
    mut v___x_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
    mut v___y_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut v_a_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2483_: u8 = 0;
    let mut v_a_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_2429_);
                v___x_2438_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                    v_declName_2429_,
                    v___x_2430_,
                    v___y_2433_,
                    v___y_2434_,
                    v___y_2435_,
                    v___y_2436_,
                );
                if lean_obj_tag(v___x_2438_) == 0 {
                    v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
                    lean_inc(v_a_2439_);
                    lean_dec_ref_known(v___x_2438_, 1);
                    if lean_obj_tag(v_a_2439_) == 1 {
                        v_val_2440_ = lean_ctor_get(v_a_2439_, 0);
                        v_isSharedCheck_2492_ = (!lean_is_exclusive(v_a_2439_)) as u8;
                        if v_isSharedCheck_2492_ == 0 {
                            v___x_2442_ = v_a_2439_;
                            v_isShared_2443_ = v_isSharedCheck_2492_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2440_);
                            lean_dec(v_a_2439_);
                            v___x_2442_ = lean_box(0);
                            v_isShared_2443_ = v_isSharedCheck_2492_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2439_);
                        lean_dec(v___x_2432_);
                        lean_dec(v_declName_2429_);
                        v___x_2493_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3_once
                            ),
                            _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3,
                        );
                        v___x_2494_ = l_panic___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__9(
                            v___x_2493_,
                            v___y_2433_,
                            v___y_2434_,
                            v___y_2435_,
                            v___y_2436_,
                        );
                        return v___x_2494_;
                    }
                } else {
                    lean_dec(v___x_2432_);
                    lean_dec(v_declName_2429_);
                    v_a_2495_ = lean_ctor_get(v___x_2438_, 0);
                    v_isSharedCheck_2502_ = (!lean_is_exclusive(v___x_2438_)) as u8;
                    if v_isSharedCheck_2502_ == 0 {
                        v___x_2497_ = v___x_2438_;
                        v_isShared_2498_ = v_isSharedCheck_2502_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2495_);
                        lean_dec(v___x_2438_);
                        v___x_2497_ = lean_box(0);
                        v_isShared_2498_ = v_isSharedCheck_2502_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_val_2440_);
                v___x_2444_ =
                    l_Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3(
                        v_val_2440_,
                        v___y_2433_,
                        v___y_2434_,
                        v___y_2435_,
                        v___y_2436_,
                    );
                if lean_obj_tag(v___x_2444_) == 0 {
                    v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
                    lean_inc(v_a_2445_);
                    lean_dec_ref_known(v___x_2444_, 1);
                    v___x_2446_ = l_Lean_ConstantInfo_type(v_a_2445_);
                    v___x_2447_ = lean_box((v___x_2431_) as usize);
                    v___x_2448_ = lean_box((v___x_2430_) as usize);
                    lean_inc_ref_n(v___x_2446_, 2);
                    v___f_2449_ = lean_alloc_closure(
                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        4,
                    );
                    lean_closure_set(v___f_2449_, 0, v___x_2446_);
                    lean_closure_set(v___f_2449_, 1, v___x_2447_);
                    lean_closure_set(v___f_2449_, 2, v___x_2448_);
                    lean_closure_set(v___f_2449_, 3, v_declName_2429_);
                    v___x_2450_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__6___redArg(v___x_2446_, v___f_2449_, v___x_2431_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
                    if lean_obj_tag(v___x_2450_) == 0 {
                        v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
                        lean_inc_n(v_a_2451_, 2);
                        lean_dec_ref_known(v___x_2450_, 1);
                        v___f_2452_ = lean_alloc_closure(
                            l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1___boxed
                                as *mut core::ffi::c_void,
                            8,
                            1,
                        );
                        lean_closure_set(v___f_2452_, 0, v_val_2440_);
                        v___x_2453_ = lean_box(0);
                        v___x_2454_ = lean_box((v___x_2431_) as usize);
                        v___f_2455_ = lean_alloc_closure(
                            l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2___boxed
                                as *mut core::ffi::c_void,
                            10,
                            5,
                        );
                        lean_closure_set(v___f_2455_, 0, v_a_2451_);
                        lean_closure_set(v___f_2455_, 1, v___x_2453_);
                        lean_closure_set(v___f_2455_, 2, v___x_2446_);
                        lean_closure_set(v___f_2455_, 3, v___f_2452_);
                        lean_closure_set(v___f_2455_, 4, v___x_2454_);
                        v___x_2456_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__8___redArg(v___f_2455_, v___x_2431_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
                        if lean_obj_tag(v___x_2456_) == 0 {
                            v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
                            lean_inc(v_a_2457_);
                            lean_dec_ref_known(v___x_2456_, 1);
                            v___x_2458_ = l_Lean_ConstantInfo_levelParams(v_a_2445_);
                            lean_dec(v_a_2445_);
                            lean_inc_n(v___x_2432_, 2);
                            v___x_2459_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_2459_, 0, v___x_2432_);
                            lean_ctor_set(v___x_2459_, 1, v___x_2458_);
                            lean_ctor_set(v___x_2459_, 2, v_a_2451_);
                            v___x_2460_ = lean_box(0);
                            v___x_2461_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_2461_, 0, v___x_2432_);
                            lean_ctor_set(v___x_2461_, 1, v___x_2460_);
                            v___x_2462_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_2462_, 0, v___x_2459_);
                            lean_ctor_set(v___x_2462_, 1, v_a_2457_);
                            lean_ctor_set(v___x_2462_, 2, v___x_2461_);
                            if v_isShared_2443_ == 0 {
                                lean_ctor_set_tag(v___x_2442_, 2);
                                lean_ctor_set(v___x_2442_, 0, v___x_2462_);
                                v___x_2464_ = v___x_2442_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_2467_ = lean_alloc_ctor(2, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2462_);
                                v___x_2464_ = v_reuseFailAlloc_2467_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2451_);
                            lean_dec(v_a_2445_);
                            lean_del_object(v___x_2442_);
                            lean_dec(v___x_2432_);
                            v_a_2468_ = lean_ctor_get(v___x_2456_, 0);
                            v_isSharedCheck_2475_ = (!lean_is_exclusive(v___x_2456_)) as u8;
                            if v_isSharedCheck_2475_ == 0 {
                                v___x_2470_ = v___x_2456_;
                                v_isShared_2471_ = v_isSharedCheck_2475_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2468_);
                                lean_dec(v___x_2456_);
                                v___x_2470_ = lean_box(0);
                                v_isShared_2471_ = v_isSharedCheck_2475_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2446_);
                        lean_dec(v_a_2445_);
                        lean_del_object(v___x_2442_);
                        lean_dec(v_val_2440_);
                        lean_dec(v___x_2432_);
                        v_a_2476_ = lean_ctor_get(v___x_2450_, 0);
                        v_isSharedCheck_2483_ = (!lean_is_exclusive(v___x_2450_)) as u8;
                        if v_isSharedCheck_2483_ == 0 {
                            v___x_2478_ = v___x_2450_;
                            v_isShared_2479_ = v_isSharedCheck_2483_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2476_);
                            lean_dec(v___x_2450_);
                            v___x_2478_ = lean_box(0);
                            v_isShared_2479_ = v_isSharedCheck_2483_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2442_);
                    lean_dec(v_val_2440_);
                    lean_dec(v___x_2432_);
                    lean_dec(v_declName_2429_);
                    v_a_2484_ = lean_ctor_get(v___x_2444_, 0);
                    v_isSharedCheck_2491_ = (!lean_is_exclusive(v___x_2444_)) as u8;
                    if v_isSharedCheck_2491_ == 0 {
                        v___x_2486_ = v___x_2444_;
                        v_isShared_2487_ = v_isSharedCheck_2491_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2484_);
                        lean_dec(v___x_2444_);
                        v___x_2486_ = lean_box(0);
                        v_isShared_2487_ = v_isSharedCheck_2491_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2465_ = l_Lean_addDecl(v___x_2464_, v___x_2431_, v___y_2435_, v___y_2436_);
                if lean_obj_tag(v___x_2465_) == 0 {
                    lean_dec_ref_known(v___x_2465_, 1);
                    v___x_2466_ = l_Lean_inferDefEqAttr(
                        v___x_2432_,
                        v___y_2433_,
                        v___y_2434_,
                        v___y_2435_,
                        v___y_2436_,
                    );
                    return v___x_2466_;
                } else {
                    lean_dec(v___x_2432_);
                    return v___x_2465_;
                }
            }
            3 => {
                if v_isShared_2471_ == 0 {
                    v___x_2473_ = v___x_2470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
                    v___x_2473_ = v_reuseFailAlloc_2474_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2473_;
            }
            5 => {
                if v_isShared_2479_ == 0 {
                    v___x_2481_ = v___x_2478_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
                    v___x_2481_ = v_reuseFailAlloc_2482_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2481_;
            }
            7 => {
                if v_isShared_2487_ == 0 {
                    v___x_2489_ = v___x_2486_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
                    v___x_2489_ = v_reuseFailAlloc_2490_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2489_;
            }
            9 => {
                if v_isShared_2498_ == 0 {
                    v___x_2500_ = v___x_2497_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
                    v___x_2500_ = v_reuseFailAlloc_2501_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___boxed(
    mut v_declName_2503_: *mut LeanObject,
    mut v___x_2504_: *mut LeanObject,
    mut v___x_2505_: *mut LeanObject,
    mut v___x_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
    mut v___y_2509_: *mut LeanObject,
    mut v___y_2510_: *mut LeanObject,
    mut v___y_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_13565__boxed_2512_: u8 = 0;
    let mut v___x_13566__boxed_2513_: u8 = 0;
    let mut v_res_2514_: *mut LeanObject = core::ptr::null_mut();
    v___x_13565__boxed_2512_ = (lean_unbox(v___x_2504_) as u8);
    v___x_13566__boxed_2513_ = (lean_unbox(v___x_2505_) as u8);
    v_res_2514_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3(
        v_declName_2503_,
        v___x_13565__boxed_2512_,
        v___x_13566__boxed_2513_,
        v___x_2506_,
        v___y_2507_,
        v___y_2508_,
        v___y_2509_,
        v___y_2510_,
    );
    lean_dec(v___y_2510_);
    lean_dec_ref(v___y_2509_);
    lean_dec(v___y_2508_);
    lean_dec_ref(v___y_2507_);
    return v_res_2514_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0()
-> f64 {
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: f64 = 0.0;
    v___x_2515_ = lean_unsigned_to_nat(0);
    v___x_2516_ = lean_float_of_nat(v___x_2515_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0(
    mut v_cls_2520_: *mut LeanObject,
    mut v_msg_2521_: *mut LeanObject,
    mut v___y_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2545_: u8 = 0;
    let mut v_tid_2546_: u64 = 0;
    let mut v_traces_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2550_: u8 = 0;
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: f64 = 0.0;
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v_isSharedCheck_2572_: u8 = 0;
    let mut v_isSharedCheck_2573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2527_ = lean_ctor_get(v___y_2524_, 5);
                v___x_2528_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0_spec__0(v_msg_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
                v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
                v_isSharedCheck_2573_ = (!lean_is_exclusive(v___x_2528_)) as u8;
                if v_isSharedCheck_2573_ == 0 {
                    v___x_2531_ = v___x_2528_;
                    v_isShared_2532_ = v_isSharedCheck_2573_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2529_);
                    lean_dec(v___x_2528_);
                    v___x_2531_ = lean_box(0);
                    v_isShared_2532_ = v_isSharedCheck_2573_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2533_ = lean_st_ref_take(v___y_2525_);
                v_traceState_2534_ = lean_ctor_get(v___x_2533_, 4);
                v_env_2535_ = lean_ctor_get(v___x_2533_, 0);
                v_nextMacroScope_2536_ = lean_ctor_get(v___x_2533_, 1);
                v_ngen_2537_ = lean_ctor_get(v___x_2533_, 2);
                v_auxDeclNGen_2538_ = lean_ctor_get(v___x_2533_, 3);
                v_cache_2539_ = lean_ctor_get(v___x_2533_, 5);
                v_messages_2540_ = lean_ctor_get(v___x_2533_, 6);
                v_infoState_2541_ = lean_ctor_get(v___x_2533_, 7);
                v_snapshotTasks_2542_ = lean_ctor_get(v___x_2533_, 8);
                v_isSharedCheck_2572_ = (!lean_is_exclusive(v___x_2533_)) as u8;
                if v_isSharedCheck_2572_ == 0 {
                    v___x_2544_ = v___x_2533_;
                    v_isShared_2545_ = v_isSharedCheck_2572_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2542_);
                    lean_inc(v_infoState_2541_);
                    lean_inc(v_messages_2540_);
                    lean_inc(v_cache_2539_);
                    lean_inc(v_traceState_2534_);
                    lean_inc(v_auxDeclNGen_2538_);
                    lean_inc(v_ngen_2537_);
                    lean_inc(v_nextMacroScope_2536_);
                    lean_inc(v_env_2535_);
                    lean_dec(v___x_2533_);
                    v___x_2544_ = lean_box(0);
                    v_isShared_2545_ = v_isSharedCheck_2572_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2546_ = lean_ctor_get_uint64(
                    v_traceState_2534_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2547_ = lean_ctor_get(v_traceState_2534_, 0);
                v_isSharedCheck_2571_ = (!lean_is_exclusive(v_traceState_2534_)) as u8;
                if v_isSharedCheck_2571_ == 0 {
                    v___x_2549_ = v_traceState_2534_;
                    v_isShared_2550_ = v_isSharedCheck_2571_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2547_);
                    lean_dec(v_traceState_2534_);
                    v___x_2549_ = lean_box(0);
                    v_isShared_2550_ = v_isSharedCheck_2571_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2551_ = lean_box(0);
                v___x_2552_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0);
                v___x_2553_ = 0;
                v___x_2554_ =
                    l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1;
                v___x_2555_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2555_, 0, v_cls_2520_);
                lean_ctor_set(v___x_2555_, 1, v___x_2551_);
                lean_ctor_set(v___x_2555_, 2, v___x_2554_);
                lean_ctor_set_float(
                    v___x_2555_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2552_,
                );
                lean_ctor_set_float(
                    v___x_2555_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2552_,
                );
                lean_ctor_set_uint8(
                    v___x_2555_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2553_,
                );
                v___x_2556_ =
                    l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2;
                v___x_2557_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2557_, 0, v___x_2555_);
                lean_ctor_set(v___x_2557_, 1, v_a_2529_);
                lean_ctor_set(v___x_2557_, 2, v___x_2556_);
                lean_inc(v_ref_2527_);
                v___x_2558_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2558_, 0, v_ref_2527_);
                lean_ctor_set(v___x_2558_, 1, v___x_2557_);
                v___x_2559_ = l_Lean_PersistentArray_push___redArg(v_traces_2547_, v___x_2558_);
                if v_isShared_2550_ == 0 {
                    lean_ctor_set(v___x_2549_, 0, v___x_2559_);
                    v___x_2561_ = v___x_2549_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2559_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2570_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2546_,
                    );
                    v___x_2561_ = v_reuseFailAlloc_2570_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2545_ == 0 {
                    lean_ctor_set(v___x_2544_, 4, v___x_2561_);
                    v___x_2563_ = v___x_2544_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_env_2535_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_nextMacroScope_2536_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_ngen_2537_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_auxDeclNGen_2538_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 4, v___x_2561_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 5, v_cache_2539_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 6, v_messages_2540_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 7, v_infoState_2541_);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 8, v_snapshotTasks_2542_);
                    v___x_2563_ = v_reuseFailAlloc_2569_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2564_ = lean_st_ref_set(v___y_2525_, v___x_2563_);
                v___x_2565_ = lean_box(0);
                if v_isShared_2532_ == 0 {
                    lean_ctor_set(v___x_2531_, 0, v___x_2565_);
                    v___x_2567_ = v___x_2531_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
                    v___x_2567_ = v_reuseFailAlloc_2568_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___boxed(
    mut v_cls_2574_: *mut LeanObject,
    mut v_msg_2575_: *mut LeanObject,
    mut v___y_2576_: *mut LeanObject,
    mut v___y_2577_: *mut LeanObject,
    mut v___y_2578_: *mut LeanObject,
    mut v___y_2579_: *mut LeanObject,
    mut v___y_2580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2581_: *mut LeanObject = core::ptr::null_mut();
    v_res_2581_ = l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0(
        v_cls_2574_,
        v_msg_2575_,
        v___y_2576_,
        v___y_2577_,
        v___y_2578_,
        v___y_2579_,
    );
    lean_dec(v___y_2579_);
    lean_dec_ref(v___y_2578_);
    lean_dec(v___y_2577_);
    lean_dec_ref(v___y_2576_);
    return v_res_2581_;
}
pub unsafe fn _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    v___x_2585_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1;
    v___x_2586_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_tryURefl_spec__0_spec__0___closed__1;
    v___x_2587_ = l_Lean_Name_append(v___x_2586_, v___x_2585_);
    return v___x_2587_;
}
pub unsafe fn _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    v___x_2589_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3;
    v___x_2590_ = l_Lean_stringToMessageData(v___x_2589_);
    return v___x_2590_;
}
pub unsafe fn _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6() -> *mut LeanObject {
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    v___x_2592_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5;
    v___x_2593_ = l_Lean_stringToMessageData(v___x_2592_);
    return v___x_2593_;
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f(
    mut v_declName_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
    mut v_a_2596_: *mut LeanObject,
    mut v_a_2597_: *mut LeanObject,
    mut v_a_2598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2600_: u8 = 0;
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2604_: u8 = 0;
    let mut v_inheritedTraceOptions_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v_unused_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2626_: u8 = 0;
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2633_: u8 = 0;
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: u8 = 0;
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2653_: u8 = 0;
    let mut v_unused_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v_unused_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2600_ = 1;
                lean_inc(v_declName_2594_);
                v___x_2601_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                    v_declName_2594_,
                    v___x_2600_,
                    v_a_2595_,
                    v_a_2596_,
                    v_a_2597_,
                    v_a_2598_,
                );
                if lean_obj_tag(v___x_2601_) == 0 {
                    v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
                    lean_inc(v_a_2602_);
                    if lean_obj_tag(v_a_2602_) == 0 {
                        v_options_2603_ = lean_ctor_get(v_a_2597_, 2);
                        v_hasTrace_2604_ = lean_ctor_get_uint8(
                            v_options_2603_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_2604_ == 0 {
                            lean_dec(v_declName_2594_);
                            return v___x_2601_;
                        } else {
                            v_inheritedTraceOptions_2605_ = lean_ctor_get(v_a_2597_, 13);
                            v___x_2606_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1;
                            v___x_2607_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2_once
                                ),
                                _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2,
                            );
                            v___x_2608_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2605_,
                                v_options_2603_,
                                v___x_2607_,
                            );
                            if v___x_2608_ == 0 {
                                lean_dec(v_declName_2594_);
                                return v___x_2601_;
                            } else {
                                lean_dec_ref_known(v___x_2601_, 1);
                                v___x_2609_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4_once
                                    ),
                                    _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4,
                                );
                                v___x_2610_ = l_Lean_MessageData_ofName(v_declName_2594_);
                                v___x_2611_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2611_, 0, v___x_2609_);
                                lean_ctor_set(v___x_2611_, 1, v___x_2610_);
                                v___x_2612_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6_once
                                    ),
                                    _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6,
                                );
                                v___x_2613_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2613_, 0, v___x_2611_);
                                lean_ctor_set(v___x_2613_, 1, v___x_2612_);
                                v___x_2614_ = l_Lean_addTrace___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0(v___x_2606_, v___x_2613_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
                                if lean_obj_tag(v___x_2614_) == 0 {
                                    v_isSharedCheck_2621_ = (!lean_is_exclusive(v___x_2614_)) as u8;
                                    if v_isSharedCheck_2621_ == 0 {
                                        v_unused_2622_ = lean_ctor_get(v___x_2614_, 0);
                                        lean_dec(v_unused_2622_);
                                        v___x_2616_ = v___x_2614_;
                                        v_isShared_2617_ = v_isSharedCheck_2621_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2614_);
                                        v___x_2616_ = lean_box(0);
                                        v_isShared_2617_ = v_isSharedCheck_2621_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_2623_ = lean_ctor_get(v___x_2614_, 0);
                                    v_isSharedCheck_2630_ = (!lean_is_exclusive(v___x_2614_)) as u8;
                                    if v_isSharedCheck_2630_ == 0 {
                                        v___x_2625_ = v___x_2614_;
                                        v_isShared_2626_ = v_isSharedCheck_2630_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2623_);
                                        lean_dec(v___x_2614_);
                                        v___x_2625_ = lean_box(0);
                                        v_isShared_2626_ = v_isSharedCheck_2630_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref_known(v___x_2601_, 1);
                        v_isSharedCheck_2663_ = (!lean_is_exclusive(v_a_2602_)) as u8;
                        if v_isSharedCheck_2663_ == 0 {
                            v_unused_2664_ = lean_ctor_get(v_a_2602_, 0);
                            lean_dec(v_unused_2664_);
                            v___x_2632_ = v_a_2602_;
                            v_isShared_2633_ = v_isSharedCheck_2663_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_a_2602_);
                            v___x_2632_ = lean_box(0);
                            v_isShared_2633_ = v_isSharedCheck_2663_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_2594_);
                    return v___x_2601_;
                }
            }
            1 => {
                if v_isShared_2617_ == 0 {
                    lean_ctor_set(v___x_2616_, 0, v_a_2602_);
                    v___x_2619_ = v___x_2616_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2602_);
                    v___x_2619_ = v_reuseFailAlloc_2620_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2619_;
            }
            3 => {
                if v_isShared_2626_ == 0 {
                    v___x_2628_ = v___x_2625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
                    v___x_2628_ = v_reuseFailAlloc_2629_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2628_;
            }
            5 => {
                v___x_2634_ = lean_st_ref_get(v_a_2598_);
                v_env_2635_ = lean_ctor_get(v___x_2634_, 0);
                lean_inc_ref(v_env_2635_);
                lean_dec(v___x_2634_);
                v___x_2636_ = 0;
                v___x_2637_ = l_Lean_Meta_eqUnfoldThmSuffix;
                lean_inc_n(v_declName_2594_, 3);
                v___x_2638_ =
                    l_Lean_Meta_mkEqLikeNameFor(v_env_2635_, v_declName_2594_, v___x_2637_);
                v___x_2639_ = lean_box((v___x_2600_) as usize);
                v___x_2640_ = lean_box((v___x_2636_) as usize);
                lean_inc_n(v___x_2638_, 2);
                v___f_2641_ = lean_alloc_closure(
                    l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___f_2641_, 0, v_declName_2594_);
                lean_closure_set(v___f_2641_, 1, v___x_2639_);
                lean_closure_set(v___f_2641_, 2, v___x_2640_);
                lean_closure_set(v___f_2641_, 3, v___x_2638_);
                v___x_2642_ = lean_alloc_closure(
                    l_Lean_Meta_withEqnOptions___boxed as *mut core::ffi::c_void,
                    8,
                    3,
                );
                lean_closure_set(v___x_2642_, 0, lean_box(0));
                lean_closure_set(v___x_2642_, 1, v_declName_2594_);
                lean_closure_set(v___x_2642_, 2, v___f_2641_);
                v___x_2643_ = l_Lean_Meta_realizeConst(
                    v_declName_2594_,
                    v___x_2638_,
                    v___x_2642_,
                    v_a_2595_,
                    v_a_2596_,
                    v_a_2597_,
                    v_a_2598_,
                );
                if lean_obj_tag(v___x_2643_) == 0 {
                    v_isSharedCheck_2653_ = (!lean_is_exclusive(v___x_2643_)) as u8;
                    if v_isSharedCheck_2653_ == 0 {
                        v_unused_2654_ = lean_ctor_get(v___x_2643_, 0);
                        lean_dec(v_unused_2654_);
                        v___x_2645_ = v___x_2643_;
                        v_isShared_2646_ = v_isSharedCheck_2653_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v___x_2643_);
                        v___x_2645_ = lean_box(0);
                        v_isShared_2646_ = v_isSharedCheck_2653_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2638_);
                    lean_del_object(v___x_2632_);
                    v_a_2655_ = lean_ctor_get(v___x_2643_, 0);
                    v_isSharedCheck_2662_ = (!lean_is_exclusive(v___x_2643_)) as u8;
                    if v_isSharedCheck_2662_ == 0 {
                        v___x_2657_ = v___x_2643_;
                        v_isShared_2658_ = v_isSharedCheck_2662_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2655_);
                        lean_dec(v___x_2643_);
                        v___x_2657_ = lean_box(0);
                        v_isShared_2658_ = v_isSharedCheck_2662_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_2633_ == 0 {
                    lean_ctor_set(v___x_2632_, 0, v___x_2638_);
                    v___x_2648_ = v___x_2632_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2638_);
                    v___x_2648_ = v_reuseFailAlloc_2652_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2646_ == 0 {
                    lean_ctor_set(v___x_2645_, 0, v___x_2648_);
                    v___x_2650_ = v___x_2645_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
                    v___x_2650_ = v_reuseFailAlloc_2651_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2650_;
            }
            9 => {
                if v_isShared_2658_ == 0 {
                    v___x_2660_ = v___x_2657_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
                    v___x_2660_ = v_reuseFailAlloc_2661_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getConstUnfoldEqnFor_x3f___boxed(
    mut v_declName_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
    mut v_a_2669_: *mut LeanObject,
    mut v_a_2670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2671_: *mut LeanObject = core::ptr::null_mut();
    v_res_2671_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f(
        v_declName_2665_,
        v_a_2666_,
        v_a_2667_,
        v_a_2668_,
        v_a_2669_,
    );
    lean_dec(v_a_2669_);
    lean_dec_ref(v_a_2668_);
    lean_dec(v_a_2667_);
    lean_dec_ref(v_a_2666_);
    return v_res_2671_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4(
    mut v_00_u03b1_2672_: *mut LeanObject,
    mut v_msg_2673_: *mut LeanObject,
    mut v___y_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
    mut v___y_2677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    v___x_2679_ = l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___redArg(
        v_msg_2673_,
        v___y_2674_,
        v___y_2675_,
        v___y_2676_,
        v___y_2677_,
    );
    return v___x_2679_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4___boxed(
    mut v_00_u03b1_2680_: *mut LeanObject,
    mut v_msg_2681_: *mut LeanObject,
    mut v___y_2682_: *mut LeanObject,
    mut v___y_2683_: *mut LeanObject,
    mut v___y_2684_: *mut LeanObject,
    mut v___y_2685_: *mut LeanObject,
    mut v___y_2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2687_: *mut LeanObject = core::ptr::null_mut();
    v_res_2687_ = l_Lean_throwError___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__4(
        v_00_u03b1_2680_,
        v_msg_2681_,
        v___y_2682_,
        v___y_2683_,
        v___y_2684_,
        v___y_2685_,
    );
    lean_dec(v___y_2685_);
    lean_dec_ref(v___y_2684_);
    lean_dec(v___y_2683_);
    lean_dec_ref(v___y_2682_);
    return v_res_2687_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__5(
    mut v_xs_2688_: *mut LeanObject,
    mut v_ys_2689_: *mut LeanObject,
    mut v_hsz_2690_: *mut LeanObject,
    mut v_x_2691_: *mut LeanObject,
    mut v_x_2692_: *mut LeanObject,
) -> u8 {
    let mut v___x_2693_: u8 = 0;
    v___x_2693_ = l_Array_isEqvAux___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__5___redArg(
        v_xs_2688_, v_ys_2689_, v_x_2691_,
    );
    return v___x_2693_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__5___boxed(
    mut v_xs_2694_: *mut LeanObject,
    mut v_ys_2695_: *mut LeanObject,
    mut v_hsz_2696_: *mut LeanObject,
    mut v_x_2697_: *mut LeanObject,
    mut v_x_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2699_: u8 = 0;
    let mut v_r_2700_: *mut LeanObject = core::ptr::null_mut();
    v_res_2699_ = l_Array_isEqvAux___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__5(
        v_xs_2694_,
        v_ys_2695_,
        v_hsz_2696_,
        v_x_2697_,
        v_x_2698_,
    );
    lean_dec_ref(v_ys_2695_);
    lean_dec_ref(v_xs_2694_);
    v_r_2700_ = lean_box((v_res_2699_) as usize);
    return v_r_2700_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6(
    mut v_00_u03b1_2701_: *mut LeanObject,
    mut v_constName_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    v___x_2708_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6___redArg(v_constName_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
    return v___x_2708_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6___boxed(
    mut v_00_u03b1_2709_: *mut LeanObject,
    mut v_constName_2710_: *mut LeanObject,
    mut v___y_2711_: *mut LeanObject,
    mut v___y_2712_: *mut LeanObject,
    mut v___y_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2716_: *mut LeanObject = core::ptr::null_mut();
    v_res_2716_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6(v_00_u03b1_2709_, v_constName_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
    lean_dec(v___y_2714_);
    lean_dec_ref(v___y_2713_);
    lean_dec(v___y_2712_);
    lean_dec_ref(v___y_2711_);
    return v_res_2716_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11(
    mut v_00_u03b1_2717_: *mut LeanObject,
    mut v_ref_2718_: *mut LeanObject,
    mut v_constName_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    v___x_2725_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___redArg(v_ref_2718_, v_constName_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
    return v___x_2725_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11___boxed(
    mut v_00_u03b1_2726_: *mut LeanObject,
    mut v_ref_2727_: *mut LeanObject,
    mut v_constName_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
    mut v___y_2732_: *mut LeanObject,
    mut v___y_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2734_: *mut LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11(v_00_u03b1_2726_, v_ref_2727_, v_constName_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
    lean_dec(v___y_2732_);
    lean_dec_ref(v___y_2731_);
    lean_dec(v___y_2730_);
    lean_dec_ref(v___y_2729_);
    lean_dec(v_ref_2727_);
    return v_res_2734_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14(
    mut v_00_u03b1_2735_: *mut LeanObject,
    mut v_ref_2736_: *mut LeanObject,
    mut v_msg_2737_: *mut LeanObject,
    mut v_declHint_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    v___x_2744_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14___redArg(v_ref_2736_, v_msg_2737_, v_declHint_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
    return v___x_2744_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14___boxed(
    mut v_00_u03b1_2745_: *mut LeanObject,
    mut v_ref_2746_: *mut LeanObject,
    mut v_msg_2747_: *mut LeanObject,
    mut v_declHint_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2754_: *mut LeanObject = core::ptr::null_mut();
    v_res_2754_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14(v_00_u03b1_2745_, v_ref_2746_, v_msg_2747_, v_declHint_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
    lean_dec(v___y_2752_);
    lean_dec_ref(v___y_2751_);
    lean_dec(v___y_2750_);
    lean_dec_ref(v___y_2749_);
    lean_dec(v_ref_2746_);
    return v_res_2754_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16(
    mut v_msg_2755_: *mut LeanObject,
    mut v_declHint_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    v___x_2762_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg(v_msg_2755_, v_declHint_2756_, v___y_2760_);
    return v___x_2762_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___boxed(
    mut v_msg_2763_: *mut LeanObject,
    mut v_declHint_2764_: *mut LeanObject,
    mut v___y_2765_: *mut LeanObject,
    mut v___y_2766_: *mut LeanObject,
    mut v___y_2767_: *mut LeanObject,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2770_: *mut LeanObject = core::ptr::null_mut();
    v_res_2770_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16(v_msg_2763_, v_declHint_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
    lean_dec(v___y_2768_);
    lean_dec_ref(v___y_2767_);
    lean_dec(v___y_2766_);
    lean_dec_ref(v___y_2765_);
    return v_res_2770_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__16(
    mut v_00_u03b1_2771_: *mut LeanObject,
    mut v_ref_2772_: *mut LeanObject,
    mut v_msg_2773_: *mut LeanObject,
    mut v___y_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    v___x_2779_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_2772_, v_msg_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
    return v___x_2779_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__16___boxed(
    mut v_00_u03b1_2780_: *mut LeanObject,
    mut v_ref_2781_: *mut LeanObject,
    mut v_msg_2782_: *mut LeanObject,
    mut v___y_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
    mut v___y_2787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2788_: *mut LeanObject = core::ptr::null_mut();
    v_res_2788_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__16(v_00_u03b1_2780_, v_ref_2781_, v_msg_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
    lean_dec(v___y_2786_);
    lean_dec_ref(v___y_2785_);
    lean_dec(v___y_2784_);
    lean_dec_ref(v___y_2783_);
    lean_dec(v_ref_2781_);
    return v_res_2788_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    v___x_2792_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2792_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    v___x_2793_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__1);
    v___x_2794_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2794_, 0, v___x_2793_);
    return v___x_2794_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    v___x_2795_ = lean_box(1);
    v___x_2796_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4);
    v___x_2797_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2);
    v___x_2798_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2798_, 0, v___x_2797_);
    lean_ctor_set(v___x_2798_, 1, v___x_2796_);
    lean_ctor_set(v___x_2798_, 2, v___x_2795_);
    return v___x_2798_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    v___x_2801_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2);
    v___x_2802_ = lean_unsigned_to_nat(0);
    v___x_2803_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2803_, 0, v___x_2802_);
    lean_ctor_set(v___x_2803_, 1, v___x_2802_);
    lean_ctor_set(v___x_2803_, 2, v___x_2802_);
    lean_ctor_set(v___x_2803_, 3, v___x_2802_);
    lean_ctor_set(v___x_2803_, 4, v___x_2801_);
    lean_ctor_set(v___x_2803_, 5, v___x_2801_);
    lean_ctor_set(v___x_2803_, 6, v___x_2801_);
    lean_ctor_set(v___x_2803_, 7, v___x_2801_);
    lean_ctor_set(v___x_2803_, 8, v___x_2801_);
    lean_ctor_set(v___x_2803_, 9, v___x_2801_);
    return v___x_2803_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    v___x_2804_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2);
    v___x_2805_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2805_, 0, v___x_2804_);
    lean_ctor_set(v___x_2805_, 1, v___x_2804_);
    lean_ctor_set(v___x_2805_, 2, v___x_2804_);
    lean_ctor_set(v___x_2805_, 3, v___x_2804_);
    lean_ctor_set(v___x_2805_, 4, v___x_2804_);
    lean_ctor_set(v___x_2805_, 5, v___x_2804_);
    return v___x_2805_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    v___x_2806_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__2);
    v___x_2807_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2807_, 0, v___x_2806_);
    lean_ctor_set(v___x_2807_, 1, v___x_2806_);
    lean_ctor_set(v___x_2807_, 2, v___x_2806_);
    lean_ctor_set(v___x_2807_, 3, v___x_2806_);
    lean_ctor_set(v___x_2807_, 4, v___x_2806_);
    return v___x_2807_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    v___x_2808_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__7_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__7);
    v___x_2809_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getConstUnfoldEqnFor_x3f_spec__3_spec__6_spec__11_spec__14_spec__15_spec__16___redArg___closed__4);
    v___x_2810_ = lean_box(1);
    v___x_2811_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__6_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__6);
    v___x_2812_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__5);
    v___x_2813_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2813_, 0, v___x_2812_);
    lean_ctor_set(v___x_2813_, 1, v___x_2811_);
    lean_ctor_set(v___x_2813_, 2, v___x_2810_);
    lean_ctor_set(v___x_2813_, 3, v___x_2809_);
    lean_ctor_set(v___x_2813_, 4, v___x_2808_);
    return v___x_2813_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg(
    mut v___x_2814_: *mut LeanObject,
    mut v_str_2815_: *mut LeanObject,
    mut v_as_x27_2816_: *mut LeanObject,
    mut v_b_2817_: *mut LeanObject,
    mut v___y_2818_: *mut LeanObject,
    mut v___y_2819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: u8 = 0;
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    let mut v_a_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: u8 = 0;
    let mut v___x_2839_: u8 = 0;
    let mut v___x_2840_: u8 = 0;
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: u64 = 0;
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2816_) == 0 {
                    lean_dec_ref(v___x_2814_);
                    v___x_2821_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2821_, 0, v_b_2817_);
                    return v___x_2821_;
                } else {
                    lean_dec_ref(v_b_2817_);
                    v_head_2822_ = lean_ctor_get(v_as_x27_2816_, 0);
                    v_tail_2823_ = lean_ctor_get(v_as_x27_2816_, 1);
                    v___x_2824_ = lean_box(0);
                    lean_inc(v_head_2822_);
                    lean_inc_ref(v___x_2814_);
                    v___x_2831_ = l_Lean_Environment_isSafeDefinition(v___x_2814_, v_head_2822_);
                    if v___x_2831_ == 0 {
                        v___x_2832_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__0;
                        v_as_x27_2816_ = v_tail_2823_;
                        v_b_2817_ = v___x_2832_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___x_2814_);
                        v___x_2834_ = 0;
                        v___x_2837_ = l_Lean_Meta_eqUnfoldThmSuffix;
                        v___x_2838_ = lean_string_dec_eq(v_str_2815_, v___x_2837_);
                        v___x_2839_ = 1;
                        v___x_2840_ = 0;
                        v___x_2841_ = 2;
                        v___x_2842_ = lean_alloc_ctor(0, 0, (19) as u32);
                        lean_ctor_set_uint8(v___x_2842_, 0 as u32, v___x_2834_);
                        lean_ctor_set_uint8(v___x_2842_, 1 as u32, v___x_2834_);
                        lean_ctor_set_uint8(v___x_2842_, 2 as u32, v___x_2834_);
                        lean_ctor_set_uint8(v___x_2842_, 3 as u32, v___x_2834_);
                        lean_ctor_set_uint8(v___x_2842_, 4 as u32, v___x_2834_);
                        lean_ctor_set_uint8(v___x_2842_, 5 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 6 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 7 as u32, v___x_2834_);
                        lean_ctor_set_uint8(v___x_2842_, 8 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 9 as u32, v___x_2839_);
                        lean_ctor_set_uint8(v___x_2842_, 10 as u32, v___x_2840_);
                        lean_ctor_set_uint8(v___x_2842_, 11 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 12 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 13 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 14 as u32, v___x_2841_);
                        lean_ctor_set_uint8(v___x_2842_, 15 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 16 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 17 as u32, v___x_2831_);
                        lean_ctor_set_uint8(v___x_2842_, 18 as u32, v___x_2831_);
                        v___x_2843_ =
                            l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2842_);
                        v___x_2844_ = lean_alloc_ctor(0, 1, (8) as u32);
                        lean_ctor_set(v___x_2844_, 0, v___x_2842_);
                        lean_ctor_set_uint64(
                            v___x_2844_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2843_,
                        );
                        v___x_2845_ = lean_box(1);
                        v___x_2846_ = lean_unsigned_to_nat(0);
                        v___x_2847_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__3);
                        v___x_2848_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__4;
                        v___x_2849_ = lean_box(0);
                        v___x_2850_ = lean_alloc_ctor(0, 7, (4) as u32);
                        lean_ctor_set(v___x_2850_, 0, v___x_2844_);
                        lean_ctor_set(v___x_2850_, 1, v___x_2845_);
                        lean_ctor_set(v___x_2850_, 2, v___x_2847_);
                        lean_ctor_set(v___x_2850_, 3, v___x_2848_);
                        lean_ctor_set(v___x_2850_, 4, v___x_2849_);
                        lean_ctor_set(v___x_2850_, 5, v___x_2846_);
                        lean_ctor_set(v___x_2850_, 6, v___x_2849_);
                        lean_ctor_set_uint8(
                            v___x_2850_,
                            (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                            v___x_2834_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2850_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                            v___x_2834_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2850_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                            v___x_2834_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2850_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                            v___x_2838_,
                        );
                        v___x_2851_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__8);
                        v___x_2852_ = lean_st_mk_ref(v___x_2851_);
                        lean_inc(v_head_2822_);
                        v___x_2853_ = l_Lean_Meta_getConstUnfoldEqnFor_x3f(
                            v_head_2822_,
                            v___x_2850_,
                            v___x_2852_,
                            v___y_2818_,
                            v___y_2819_,
                        );
                        lean_dec_ref_known(v___x_2850_, 7);
                        if lean_obj_tag(v___x_2853_) == 0 {
                            v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
                            lean_inc(v_a_2854_);
                            lean_dec_ref_known(v___x_2853_, 1);
                            v___x_2855_ = lean_st_ref_get(v___x_2852_);
                            lean_dec(v___x_2852_);
                            lean_dec(v___x_2855_);
                            v_a_2836_ = v_a_2854_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_2852_);
                            if lean_obj_tag(v___x_2853_) == 0 {
                                v_a_2856_ = lean_ctor_get(v___x_2853_, 0);
                                lean_inc(v_a_2856_);
                                lean_dec_ref_known(v___x_2853_, 1);
                                v_a_2836_ = v_a_2856_;
                                state = 2;
                                continue;
                            } else {
                                v_a_2857_ = lean_ctor_get(v___x_2853_, 0);
                                v_isSharedCheck_2864_ = (!lean_is_exclusive(v___x_2853_)) as u8;
                                if v_isSharedCheck_2864_ == 0 {
                                    v___x_2859_ = v___x_2853_;
                                    v_isShared_2860_ = v_isSharedCheck_2864_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2857_);
                                    lean_dec(v___x_2853_);
                                    v___x_2859_ = lean_box(0);
                                    v_isShared_2860_ = v_isSharedCheck_2864_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2827_ = lean_box((v___y_2826_) as usize);
                v___x_2828_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2828_, 0, v___x_2827_);
                v___x_2829_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2829_, 0, v___x_2828_);
                lean_ctor_set(v___x_2829_, 1, v___x_2824_);
                v___x_2830_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2830_, 0, v___x_2829_);
                return v___x_2830_;
            }
            2 => {
                if lean_obj_tag(v_a_2836_) == 0 {
                    v___y_2826_ = v___x_2834_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_a_2836_, 1);
                    v___y_2826_ = v___x_2831_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2860_ == 0 {
                    v___x_2862_ = v___x_2859_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
                    v___x_2862_ = v_reuseFailAlloc_2863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v___x_2865_: *mut LeanObject,
    mut v_str_2866_: *mut LeanObject,
    mut v_as_x27_2867_: *mut LeanObject,
    mut v_b_2868_: *mut LeanObject,
    mut v___y_2869_: *mut LeanObject,
    mut v___y_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2872_: *mut LeanObject = core::ptr::null_mut();
    v_res_2872_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg(v___x_2865_, v_str_2866_, v_as_x27_2867_, v_b_2868_, v___y_2869_, v___y_2870_);
    lean_dec(v___y_2870_);
    lean_dec_ref(v___y_2869_);
    lean_dec(v_as_x27_2867_);
    lean_dec_ref(v_str_2866_);
    return v_res_2872_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2_(
    mut v_name_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2898_: u8 = 0;
    let mut v_fst_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v_a_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2912_: u8 = 0;
    let mut v___x_2913_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_name_2873_) == 1 {
                    v_pre_2881_ = lean_ctor_get(v_name_2873_, 0);
                    lean_inc(v_pre_2881_);
                    v_str_2882_ = lean_ctor_get(v_name_2873_, 1);
                    lean_inc_ref(v_str_2882_);
                    lean_dec_ref_known(v_name_2873_, 2);
                    v___x_2883_ = l_Lean_Meta_eqUnfoldThmSuffix;
                    v___x_2884_ = lean_string_dec_eq(v_str_2882_, v___x_2883_);
                    if v___x_2884_ == 0 {
                        lean_dec_ref(v_str_2882_);
                        lean_dec(v_pre_2881_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2885_ = lean_st_ref_get(v___y_2875_);
                        v_env_2886_ = lean_ctor_get(v___x_2885_, 0);
                        lean_inc_ref(v_env_2886_);
                        lean_dec(v___x_2885_);
                        v___x_2887_ = 0;
                        v___x_2888_ = l_Lean_Environment_setExporting(v_env_2886_, v___x_2887_);
                        lean_inc(v_pre_2881_);
                        v___x_2889_ = l_Lean_privateToUserName(v_pre_2881_);
                        v___x_2890_ = lean_box(0);
                        v___x_2891_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2891_, 0, v___x_2889_);
                        lean_ctor_set(v___x_2891_, 1, v___x_2890_);
                        v___x_2892_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2892_, 0, v_pre_2881_);
                        lean_ctor_set(v___x_2892_, 1, v___x_2891_);
                        v___x_2893_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg___closed__0;
                        v___x_2894_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg(v___x_2888_, v_str_2882_, v___x_2892_, v___x_2893_, v___y_2874_, v___y_2875_);
                        lean_dec_ref_known(v___x_2892_, 2);
                        lean_dec_ref(v_str_2882_);
                        if lean_obj_tag(v___x_2894_) == 0 {
                            v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
                            v_isSharedCheck_2904_ = (!lean_is_exclusive(v___x_2894_)) as u8;
                            if v_isSharedCheck_2904_ == 0 {
                                v___x_2897_ = v___x_2894_;
                                v_isShared_2898_ = v_isSharedCheck_2904_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2895_);
                                lean_dec(v___x_2894_);
                                v___x_2897_ = lean_box(0);
                                v_isShared_2898_ = v_isSharedCheck_2904_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_2905_ = lean_ctor_get(v___x_2894_, 0);
                            v_isSharedCheck_2912_ = (!lean_is_exclusive(v___x_2894_)) as u8;
                            if v_isSharedCheck_2912_ == 0 {
                                v___x_2907_ = v___x_2894_;
                                v_isShared_2908_ = v_isSharedCheck_2912_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2905_);
                                lean_dec(v___x_2894_);
                                v___x_2907_ = lean_box(0);
                                v_isShared_2908_ = v_isSharedCheck_2912_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_name_2873_);
                    v___x_2913_ = 0;
                    v___x_2914_ = lean_box((v___x_2913_) as usize);
                    v___x_2915_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2915_, 0, v___x_2914_);
                    return v___x_2915_;
                }
            }
            1 => {
                v___x_2878_ = 0;
                v___x_2879_ = lean_box((v___x_2878_) as usize);
                v___x_2880_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2880_, 0, v___x_2879_);
                return v___x_2880_;
            }
            2 => {
                v_fst_2899_ = lean_ctor_get(v_a_2895_, 0);
                lean_inc(v_fst_2899_);
                lean_dec(v_a_2895_);
                if lean_obj_tag(v_fst_2899_) == 0 {
                    lean_del_object(v___x_2897_);
                    state = 1;
                    continue;
                } else {
                    v_val_2900_ = lean_ctor_get(v_fst_2899_, 0);
                    lean_inc(v_val_2900_);
                    lean_dec_ref_known(v_fst_2899_, 1);
                    if v_isShared_2898_ == 0 {
                        lean_ctor_set(v___x_2897_, 0, v_val_2900_);
                        v___x_2902_ = v___x_2897_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_val_2900_);
                        v___x_2902_ = v_reuseFailAlloc_2903_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2902_;
            }
            4 => {
                if v_isShared_2908_ == 0 {
                    v___x_2910_ = v___x_2907_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
                    v___x_2910_ = v_reuseFailAlloc_2911_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2____boxed(
    mut v_name_2916_: *mut LeanObject,
    mut v___y_2917_: *mut LeanObject,
    mut v___y_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2920_: *mut LeanObject = core::ptr::null_mut();
    v_res_2920_ = l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2_(v_name_2916_, v___y_2917_, v___y_2918_);
    lean_dec(v___y_2918_);
    lean_dec_ref(v___y_2917_);
    return v_res_2920_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    v___f_2923_ = l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2_;
    v___x_2924_ = l_Lean_registerReservedNameAction(v___f_2923_);
    return v___x_2924_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2____boxed(
    mut v_a_2925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2926_: *mut LeanObject = core::ptr::null_mut();
    v_res_2926_ = l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2_();
    return v_res_2926_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0(
    mut v___x_2927_: *mut LeanObject,
    mut v_str_2928_: *mut LeanObject,
    mut v_as_2929_: *mut LeanObject,
    mut v_as_x27_2930_: *mut LeanObject,
    mut v_b_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
    mut v___y_2933_: *mut LeanObject,
    mut v___y_2934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    v___x_2936_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___redArg(v___x_2927_, v_str_2928_, v_as_x27_2930_, v_b_2931_, v___y_2933_, v___y_2934_);
    return v___x_2936_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0___boxed(
    mut v___x_2937_: *mut LeanObject,
    mut v_str_2938_: *mut LeanObject,
    mut v_as_2939_: *mut LeanObject,
    mut v_as_x27_2940_: *mut LeanObject,
    mut v_b_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v___y_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2946_: *mut LeanObject = core::ptr::null_mut();
    v_res_2946_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2__spec__0(v___x_2937_, v_str_2938_, v_as_2939_, v_as_x27_2940_, v_b_2941_, v_a_2942_, v___y_2943_, v___y_2944_);
    lean_dec(v___y_2944_);
    lean_dec_ref(v___y_2943_);
    lean_dec(v_as_x27_2940_);
    lean_dec(v_as_2939_);
    lean_dec_ref(v_str_2938_);
    return v_res_2946_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_EqUnfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_PreDefinition_EqUnfold_0__Lean_Meta_initFn_00___x40_Lean_Elab_PreDefinition_EqUnfold_1356299382____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_EqUnfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_EqUnfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_EqUnfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_EqUnfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_EqUnfold(builtin);
}
