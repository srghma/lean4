// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.CbvEvalExt
// Imports: Lean.Data.NameMap Lean.ScopedEnvExtension Lean.Elab.InfoTree Lean.Meta.Sym.Simp.Theorems Lean.Meta.Tactic.AuxLemma Lean.Meta.AppBuilder
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::NameMap::{
    initialize_Lean_Data_NameMap, runtime_initialize_Lean_Data_NameMap,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::InfoTree::{
    initialize_Lean_Elab_InfoTree, runtime_initialize_Lean_Elab_InfoTree,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constName_x3f, l_Lean_Expr_getAppFn,
    l_Lean_Expr_isAppOfArity, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqSymm,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Sym::Simp::Theorems::{
    initialize_Lean_Meta_Sym_Simp_Theorems, l_Lean_Meta_Sym_Simp_Theorems_insert,
    l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default, l_Lean_Meta_Sym_Simp_mkTheoremFromDecl,
    runtime_initialize_Lean_Meta_Sym_Simp_Theorems,
};
use crate::r#gen::Lean::Meta::Tactic::AuxLemma::{
    initialize_Lean_Meta_Tactic_AuxLemma, l_Lean_Meta_mkAuxLemma,
    runtime_initialize_Lean_Meta_Tactic_AuxLemma,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_addCore___redArg,
    l_Lean_ScopedEnvExtension_getState___redArg, l_Lean_ScopedEnvExtension_modifyState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg, runtime_initialize_Lean_ScopedEnvExtension,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
    lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__0_value)
            as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__2_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        84, 104, 101, 32, 99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__4_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 32, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__6_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__8_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [95, 99, 98, 118, 95, 101, 118, 97, 108, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__9_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__8_value)
            as *mut LeanObject,
        4717274133169104646 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__10_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__11_value:
    LeanStringObject<29> = LeanStringObject {
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
        84, 104, 101, 32, 114, 101, 119, 114, 105, 116, 101, 32, 115, 105, 100, 101, 32, 111, 102,
        32, 116, 104, 101, 111, 114, 101, 109, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__13_value:
    LeanStringObject<37> = LeanStringObject {
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
        32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105,
        111, 110, 32, 111, 102, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__0_value: LeanStringObject<70> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 70,
        m_capacity: 70,
        m_length: 69,
        m_data: [
            32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97,
            110, 100, 32, 116, 104, 117, 115, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 109,
            97, 114, 107, 101, 100, 32, 119, 105, 116, 104, 32, 96, 99, 98, 118, 95, 101, 118, 97,
            108, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value:
    LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 98, 118, 69, 118, 97, 108, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject,16939926138027044706 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut LeanObject,72621647814721793 as *mut LeanObject,65793 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 96, 91, 99, 98, 118, 95, 101, 118, 97, 108, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 98, 118, 69, 118, 97, 108, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject,1932357725600152060 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 98, 118, 95, 101, 118, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject,7347478309838019632 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanStringObject<81> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 81, m_capacity: 81, m_length: 80, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 32, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 115, 32, 97, 32, 114, 101, 119, 114, 105, 116, 101, 32, 114, 117, 108, 101, 32, 102, 111, 114, 32, 96, 99, 98, 118, 96, 32, 101, 118, 97, 108, 117, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97, 32, 103, 105, 118, 101, 110, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_declName(
    mut v_thm_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expr_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    v_expr_2236_ = lean_ctor_get(v_thm_2235_, 0);
    v___x_2237_ = l_Lean_Expr_getAppFn(v_expr_2236_);
    v___x_2238_ = l_Lean_Expr_constName_x3f(v___x_2237_);
    lean_dec_ref(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_declName___boxed(
    mut v_thm_2239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2240_: *mut LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lean_Meta_Sym_Simp_Theorem_declName(v_thm_2239_);
    lean_dec_ref(v_thm_2239_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry_beq(
    mut v_x_2241_: *mut LeanObject,
    mut v_x_2242_: *mut LeanObject,
) -> u8 {
    let mut v_origin_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_appFn_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thm_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_appFn_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thm_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    v_origin_2243_ = lean_ctor_get(v_x_2241_, 0);
    v_appFn_2244_ = lean_ctor_get(v_x_2241_, 1);
    v_thm_2245_ = lean_ctor_get(v_x_2241_, 2);
    v_origin_2246_ = lean_ctor_get(v_x_2242_, 0);
    v_appFn_2247_ = lean_ctor_get(v_x_2242_, 1);
    v_thm_2248_ = lean_ctor_get(v_x_2242_, 2);
    v___x_2249_ = lean_name_eq(v_origin_2243_, v_origin_2246_);
    if v___x_2249_ == 0 {
        return v___x_2249_;
    } else {
        let mut v___x_2250_: u8 = 0;
        v___x_2250_ = lean_name_eq(v_appFn_2244_, v_appFn_2247_);
        if v___x_2250_ == 0 {
            return v___x_2250_;
        } else {
            let mut v_expr_2251_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_2252_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2253_: u8 = 0;
            v_expr_2251_ = lean_ctor_get(v_thm_2245_, 0);
            v_expr_2252_ = lean_ctor_get(v_thm_2248_, 0);
            v___x_2253_ = lean_expr_eqv(v_expr_2251_, v_expr_2252_);
            return v___x_2253_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry_beq___boxed(
    mut v_x_2254_: *mut LeanObject,
    mut v_x_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2256_: u8 = 0;
    let mut v_r_2257_: *mut LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry_beq(v_x_2254_, v_x_2255_);
    lean_dec_ref(v_x_2255_);
    lean_dec_ref(v_x_2254_);
    v_r_2257_ = lean_box((v_res_2256_) as usize);
    return v_r_2257_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
    v___x_2261_ = lean_box(0);
    v___x_2262_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2262_, 0, v___x_2261_);
    lean_ctor_set(v___x_2262_, 1, v___x_2261_);
    lean_ctor_set(v___x_2262_, 2, v___x_2260_);
    return v___x_2262_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default() -> *mut LeanObject {
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    v___x_2263_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0,
    );
    return v___x_2263_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry() -> *mut LeanObject {
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    v___x_2264_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default;
    return v___x_2264_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___lam__0(
    mut v_k_2265_: *mut LeanObject,
    mut v_b_2266_: *mut LeanObject,
    mut v_c_2267_: *mut LeanObject,
    mut v___y_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2271_);
    lean_inc_ref(v___y_2270_);
    lean_inc(v___y_2269_);
    lean_inc_ref(v___y_2268_);
    v___x_2273_ = lean_apply_7(
        v_k_2265_,
        v_b_2266_,
        v_c_2267_,
        v___y_2268_,
        v___y_2269_,
        v___y_2270_,
        v___y_2271_,
        lean_box(0),
    );
    return v___x_2273_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___lam__0___boxed(
    mut v_k_2274_: *mut LeanObject,
    mut v_b_2275_: *mut LeanObject,
    mut v_c_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2282_: *mut LeanObject = core::ptr::null_mut();
    v_res_2282_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___lam__0(v_k_2274_, v_b_2275_, v_c_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
    lean_dec(v___y_2280_);
    lean_dec_ref(v___y_2279_);
    lean_dec(v___y_2278_);
    lean_dec_ref(v___y_2277_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg(
    mut v_type_2283_: *mut LeanObject,
    mut v_k_2284_: *mut LeanObject,
    mut v_cleanupAnnotations_2285_: u8,
    mut v___y_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2302_: u8 = 0;
    let mut v_a_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2306_: u8 = 0;
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2291_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_2291_, 0, v_k_2284_);
                v___x_2292_ = 0;
                v___x_2293_ = lean_box(0);
                v___x_2294_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
                        v___x_2292_,
                        v___x_2293_,
                        v_type_2283_,
                        v___f_2291_,
                        v_cleanupAnnotations_2285_,
                        v___x_2292_,
                        v___y_2286_,
                        v___y_2287_,
                        v___y_2288_,
                        v___y_2289_,
                    );
                if lean_obj_tag(v___x_2294_) == 0 {
                    v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
                    v_isSharedCheck_2302_ = (!lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2302_ == 0 {
                        v___x_2297_ = v___x_2294_;
                        v_isShared_2298_ = v_isSharedCheck_2302_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2295_);
                        lean_dec(v___x_2294_);
                        v___x_2297_ = lean_box(0);
                        v_isShared_2298_ = v_isSharedCheck_2302_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2303_ = lean_ctor_get(v___x_2294_, 0);
                    v_isSharedCheck_2310_ = (!lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2310_ == 0 {
                        v___x_2305_ = v___x_2294_;
                        v_isShared_2306_ = v_isSharedCheck_2310_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2303_);
                        lean_dec(v___x_2294_);
                        v___x_2305_ = lean_box(0);
                        v_isShared_2306_ = v_isSharedCheck_2310_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2298_ == 0 {
                    v___x_2300_ = v___x_2297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
                    v___x_2300_ = v_reuseFailAlloc_2301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2300_;
            }
            3 => {
                if v_isShared_2306_ == 0 {
                    v___x_2308_ = v___x_2305_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
                    v___x_2308_ = v_reuseFailAlloc_2309_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___boxed(
    mut v_type_2311_: *mut LeanObject,
    mut v_k_2312_: *mut LeanObject,
    mut v_cleanupAnnotations_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2319_: u8 = 0;
    let mut v_res_2320_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2319_ = (lean_unbox(v_cleanupAnnotations_2313_) as u8);
    v_res_2320_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg(v_type_2311_, v_k_2312_, v_cleanupAnnotations_boxed_2319_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
    lean_dec(v___y_2317_);
    lean_dec_ref(v___y_2316_);
    lean_dec(v___y_2315_);
    lean_dec_ref(v___y_2314_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3(
    mut v_00_u03b1_2321_: *mut LeanObject,
    mut v_type_2322_: *mut LeanObject,
    mut v_k_2323_: *mut LeanObject,
    mut v_cleanupAnnotations_2324_: u8,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    v___x_2330_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg(v_type_2322_, v_k_2323_, v_cleanupAnnotations_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
    return v___x_2330_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___boxed(
    mut v_00_u03b1_2331_: *mut LeanObject,
    mut v_type_2332_: *mut LeanObject,
    mut v_k_2333_: *mut LeanObject,
    mut v_cleanupAnnotations_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2340_: u8 = 0;
    let mut v_res_2341_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2340_ = (lean_unbox(v_cleanupAnnotations_2334_) as u8);
    v_res_2341_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3(
            v_00_u03b1_2331_,
            v_type_2332_,
            v_k_2333_,
            v_cleanupAnnotations_boxed_2340_,
            v___y_2335_,
            v___y_2336_,
            v___y_2337_,
            v___y_2338_,
        );
    lean_dec(v___y_2338_);
    lean_dec_ref(v___y_2337_);
    lean_dec(v___y_2336_);
    lean_dec_ref(v___y_2335_);
    return v_res_2341_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2_spec__3(
    mut v_msgData_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    v___x_2348_ = lean_st_ref_get(v___y_2346_);
    v_env_2349_ = lean_ctor_get(v___x_2348_, 0);
    lean_inc_ref(v_env_2349_);
    lean_dec(v___x_2348_);
    v___x_2350_ = lean_st_ref_get(v___y_2344_);
    v_mctx_2351_ = lean_ctor_get(v___x_2350_, 0);
    lean_inc_ref(v_mctx_2351_);
    lean_dec(v___x_2350_);
    v_lctx_2352_ = lean_ctor_get(v___y_2343_, 2);
    v_options_2353_ = lean_ctor_get(v___y_2345_, 2);
    lean_inc_ref(v_options_2353_);
    lean_inc_ref(v_lctx_2352_);
    v___x_2354_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2354_, 0, v_env_2349_);
    lean_ctor_set(v___x_2354_, 1, v_mctx_2351_);
    lean_ctor_set(v___x_2354_, 2, v_lctx_2352_);
    lean_ctor_set(v___x_2354_, 3, v_options_2353_);
    v___x_2355_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2355_, 0, v___x_2354_);
    lean_ctor_set(v___x_2355_, 1, v_msgData_2342_);
    v___x_2356_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2356_, 0, v___x_2355_);
    return v___x_2356_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2_spec__3___boxed(
    mut v_msgData_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2363_: *mut LeanObject = core::ptr::null_mut();
    v_res_2363_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2_spec__3(v_msgData_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
    lean_dec(v___y_2361_);
    lean_dec_ref(v___y_2360_);
    lean_dec(v___y_2359_);
    lean_dec_ref(v___y_2358_);
    return v_res_2363_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(
    mut v_msg_2364_: *mut LeanObject,
    mut v___y_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2370_ = lean_ctor_get(v___y_2367_, 5);
                v___x_2371_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2_spec__3(v_msg_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
                v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
                v_isSharedCheck_2380_ = (!lean_is_exclusive(v___x_2371_)) as u8;
                if v_isSharedCheck_2380_ == 0 {
                    v___x_2374_ = v___x_2371_;
                    v_isShared_2375_ = v_isSharedCheck_2380_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2372_);
                    lean_dec(v___x_2371_);
                    v___x_2374_ = lean_box(0);
                    v_isShared_2375_ = v_isSharedCheck_2380_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2370_);
                v___x_2376_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2376_, 0, v_ref_2370_);
                lean_ctor_set(v___x_2376_, 1, v_a_2372_);
                if v_isShared_2375_ == 0 {
                    lean_ctor_set_tag(v___x_2374_, 1);
                    lean_ctor_set(v___x_2374_, 0, v___x_2376_);
                    v___x_2378_ = v___x_2374_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg___boxed(
    mut v_msg_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2387_: *mut LeanObject = core::ptr::null_mut();
    v_res_2387_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(
            v_msg_2381_,
            v___y_2382_,
            v___y_2383_,
            v___y_2384_,
            v___y_2385_,
        );
    lean_dec(v___y_2385_);
    lean_dec_ref(v___y_2384_);
    lean_dec(v___y_2383_);
    lean_dec_ref(v___y_2382_);
    return v_res_2387_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__2;
    v___x_2393_ = l_Lean_stringToMessageData(v___x_2392_);
    return v___x_2393_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    v___x_2395_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__4;
    v___x_2396_ = l_Lean_stringToMessageData(v___x_2395_);
    return v___x_2396_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    v___x_2398_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__6;
    v___x_2399_ = l_Lean_stringToMessageData(v___x_2398_);
    return v___x_2399_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12()
-> *mut LeanObject {
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__11;
    v___x_2407_ = l_Lean_stringToMessageData(v___x_2406_);
    return v___x_2407_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14()
-> *mut LeanObject {
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__13;
    v___x_2410_ = l_Lean_stringToMessageData(v___x_2409_);
    return v___x_2410_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0(
    mut v_a_2411_: *mut LeanObject,
    mut v___x_2412_: *mut LeanObject,
    mut v_inv_2413_: u8,
    mut v_declName_2414_: *mut LeanObject,
    mut v_levelParams_2415_: *mut LeanObject,
    mut v_xs_2416_: *mut LeanObject,
    mut v_body_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
    mut v___y_2419_: *mut LeanObject,
    mut v___y_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmDeclName_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2453_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_a_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2475_: u8 = 0;
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut v_a_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_a_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2491_: u8 = 0;
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2495_: u8 = 0;
    let mut v_a_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__1;
                v___x_2429_ = lean_unsigned_to_nat(3);
                v___x_2430_ = l_Lean_Expr_isAppOfArity(v_body_2417_, v___x_2428_, v___x_2429_);
                if v___x_2430_ == 0 {
                    lean_dec(v_levelParams_2415_);
                    lean_dec(v_declName_2414_);
                    v___x_2431_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3,
                    );
                    v___x_2432_ = l_Lean_MessageData_ofExpr(v_a_2411_);
                    v___x_2433_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2433_, 0, v___x_2431_);
                    lean_ctor_set(v___x_2433_, 1, v___x_2432_);
                    v___x_2434_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5,
                    );
                    v___x_2435_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2435_, 0, v___x_2433_);
                    lean_ctor_set(v___x_2435_, 1, v___x_2434_);
                    v___x_2436_ = l_Lean_MessageData_ofExpr(v___x_2412_);
                    v___x_2437_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2437_, 0, v___x_2435_);
                    lean_ctor_set(v___x_2437_, 1, v___x_2436_);
                    v___x_2438_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7,
                    );
                    v___x_2439_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2439_, 0, v___x_2437_);
                    lean_ctor_set(v___x_2439_, 1, v___x_2438_);
                    v___x_2440_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(v___x_2439_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
                    return v___x_2440_;
                } else {
                    lean_dec_ref(v_a_2411_);
                    v___x_2441_ = l_Lean_Expr_appFn_x21(v_body_2417_);
                    v___x_2442_ = l_Lean_Expr_appArg_x21(v___x_2441_);
                    lean_dec_ref(v___x_2441_);
                    v___x_2443_ = l_Lean_Expr_appArg_x21(v_body_2417_);
                    if v_inv_2413_ == 0 {
                        lean_inc_ref(v___x_2442_);
                        v___y_2445_ = v___x_2442_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc_ref(v___x_2443_);
                        v___y_2445_ = v___x_2443_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2426_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2426_, 0, v___y_2424_);
                lean_ctor_set(v___x_2426_, 1, v_thmDeclName_2425_);
                v___x_2427_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2427_, 0, v___x_2426_);
                return v___x_2427_;
            }
            2 => {
                v___x_2446_ = l_Lean_Expr_getAppFn(v___y_2445_);
                lean_dec_ref(v___y_2445_);
                v___x_2447_ = l_Lean_Expr_constName_x3f(v___x_2446_);
                lean_dec_ref(v___x_2446_);
                if lean_obj_tag(v___x_2447_) == 1 {
                    if v_inv_2413_ == 0 {
                        lean_dec_ref(v___x_2443_);
                        lean_dec_ref(v___x_2442_);
                        lean_dec(v_levelParams_2415_);
                        lean_dec_ref(v___x_2412_);
                        v_val_2448_ = lean_ctor_get(v___x_2447_, 0);
                        lean_inc(v_val_2448_);
                        lean_dec_ref_known(v___x_2447_, 1);
                        v___y_2424_ = v_val_2448_;
                        v_thmDeclName_2425_ = v_declName_2414_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_declName_2414_);
                        v_val_2449_ = lean_ctor_get(v___x_2447_, 0);
                        lean_inc(v_val_2449_);
                        lean_dec_ref_known(v___x_2447_, 1);
                        v___x_2450_ = l_Lean_Meta_mkEq(
                            v___x_2443_,
                            v___x_2442_,
                            v___y_2418_,
                            v___y_2419_,
                            v___y_2420_,
                            v___y_2421_,
                        );
                        if lean_obj_tag(v___x_2450_) == 0 {
                            v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
                            lean_inc(v_a_2451_);
                            lean_dec_ref_known(v___x_2450_, 1);
                            v___x_2452_ = 0;
                            v___x_2453_ = 1;
                            v___x_2454_ = l_Lean_Meta_mkForallFVars(
                                v_xs_2416_,
                                v_a_2451_,
                                v___x_2452_,
                                v___x_2430_,
                                v___x_2430_,
                                v___x_2453_,
                                v___y_2418_,
                                v___y_2419_,
                                v___y_2420_,
                                v___y_2421_,
                            );
                            if lean_obj_tag(v___x_2454_) == 0 {
                                v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
                                lean_inc(v_a_2455_);
                                lean_dec_ref_known(v___x_2454_, 1);
                                v___x_2456_ = l_Lean_mkAppN(v___x_2412_, v_xs_2416_);
                                v___x_2457_ = l_Lean_Meta_mkEqSymm(
                                    v___x_2456_,
                                    v___y_2418_,
                                    v___y_2419_,
                                    v___y_2420_,
                                    v___y_2421_,
                                );
                                if lean_obj_tag(v___x_2457_) == 0 {
                                    v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
                                    lean_inc(v_a_2458_);
                                    lean_dec_ref_known(v___x_2457_, 1);
                                    v___x_2459_ = l_Lean_Meta_mkLambdaFVars(
                                        v_xs_2416_,
                                        v_a_2458_,
                                        v___x_2452_,
                                        v___x_2430_,
                                        v___x_2452_,
                                        v___x_2430_,
                                        v___x_2453_,
                                        v___y_2418_,
                                        v___y_2419_,
                                        v___y_2420_,
                                        v___y_2421_,
                                    );
                                    if lean_obj_tag(v___x_2459_) == 0 {
                                        v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
                                        lean_inc(v_a_2460_);
                                        lean_dec_ref_known(v___x_2459_, 1);
                                        v___x_2461_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__10;
                                        v___x_2462_ = l_Lean_Meta_mkAuxLemma(
                                            v_levelParams_2415_,
                                            v_a_2455_,
                                            v_a_2460_,
                                            v___x_2461_,
                                            v___x_2430_,
                                            v___x_2452_,
                                            v___x_2452_,
                                            v___x_2452_,
                                            v___y_2418_,
                                            v___y_2419_,
                                            v___y_2420_,
                                            v___y_2421_,
                                        );
                                        if lean_obj_tag(v___x_2462_) == 0 {
                                            v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
                                            lean_inc(v_a_2463_);
                                            lean_dec_ref_known(v___x_2462_, 1);
                                            v___y_2424_ = v_val_2449_;
                                            v_thmDeclName_2425_ = v_a_2463_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec(v_val_2449_);
                                            v_a_2464_ = lean_ctor_get(v___x_2462_, 0);
                                            v_isSharedCheck_2471_ =
                                                (!lean_is_exclusive(v___x_2462_)) as u8;
                                            if v_isSharedCheck_2471_ == 0 {
                                                v___x_2466_ = v___x_2462_;
                                                v_isShared_2467_ = v_isSharedCheck_2471_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2464_);
                                                lean_dec(v___x_2462_);
                                                v___x_2466_ = lean_box(0);
                                                v_isShared_2467_ = v_isSharedCheck_2471_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_2455_);
                                        lean_dec(v_val_2449_);
                                        lean_dec(v_levelParams_2415_);
                                        v_a_2472_ = lean_ctor_get(v___x_2459_, 0);
                                        v_isSharedCheck_2479_ =
                                            (!lean_is_exclusive(v___x_2459_)) as u8;
                                        if v_isSharedCheck_2479_ == 0 {
                                            v___x_2474_ = v___x_2459_;
                                            v_isShared_2475_ = v_isSharedCheck_2479_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2472_);
                                            lean_dec(v___x_2459_);
                                            v___x_2474_ = lean_box(0);
                                            v_isShared_2475_ = v_isSharedCheck_2479_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2455_);
                                    lean_dec(v_val_2449_);
                                    lean_dec(v_levelParams_2415_);
                                    v_a_2480_ = lean_ctor_get(v___x_2457_, 0);
                                    v_isSharedCheck_2487_ = (!lean_is_exclusive(v___x_2457_)) as u8;
                                    if v_isSharedCheck_2487_ == 0 {
                                        v___x_2482_ = v___x_2457_;
                                        v_isShared_2483_ = v_isSharedCheck_2487_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2480_);
                                        lean_dec(v___x_2457_);
                                        v___x_2482_ = lean_box(0);
                                        v_isShared_2483_ = v_isSharedCheck_2487_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2449_);
                                lean_dec(v_levelParams_2415_);
                                lean_dec_ref(v___x_2412_);
                                v_a_2488_ = lean_ctor_get(v___x_2454_, 0);
                                v_isSharedCheck_2495_ = (!lean_is_exclusive(v___x_2454_)) as u8;
                                if v_isSharedCheck_2495_ == 0 {
                                    v___x_2490_ = v___x_2454_;
                                    v_isShared_2491_ = v_isSharedCheck_2495_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2488_);
                                    lean_dec(v___x_2454_);
                                    v___x_2490_ = lean_box(0);
                                    v_isShared_2491_ = v_isSharedCheck_2495_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_2449_);
                            lean_dec(v_levelParams_2415_);
                            lean_dec_ref(v___x_2412_);
                            v_a_2496_ = lean_ctor_get(v___x_2450_, 0);
                            v_isSharedCheck_2503_ = (!lean_is_exclusive(v___x_2450_)) as u8;
                            if v_isSharedCheck_2503_ == 0 {
                                v___x_2498_ = v___x_2450_;
                                v_isShared_2499_ = v_isSharedCheck_2503_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_2496_);
                                lean_dec(v___x_2450_);
                                v___x_2498_ = lean_box(0);
                                v_isShared_2499_ = v_isSharedCheck_2503_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_2447_);
                    lean_dec_ref(v___x_2443_);
                    lean_dec_ref(v___x_2442_);
                    lean_dec(v_levelParams_2415_);
                    lean_dec(v_declName_2414_);
                    v___x_2504_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12,
                    );
                    v___x_2505_ = l_Lean_MessageData_ofExpr(v___x_2412_);
                    v___x_2506_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2506_, 0, v___x_2504_);
                    lean_ctor_set(v___x_2506_, 1, v___x_2505_);
                    v___x_2507_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14,
                    );
                    v___x_2508_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2508_, 0, v___x_2506_);
                    lean_ctor_set(v___x_2508_, 1, v___x_2507_);
                    v___x_2509_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(v___x_2508_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
                    return v___x_2509_;
                }
            }
            3 => {
                if v_isShared_2467_ == 0 {
                    v___x_2469_ = v___x_2466_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
                    v___x_2469_ = v_reuseFailAlloc_2470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2469_;
            }
            5 => {
                if v_isShared_2475_ == 0 {
                    v___x_2477_ = v___x_2474_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
                    v___x_2477_ = v_reuseFailAlloc_2478_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2477_;
            }
            7 => {
                if v_isShared_2483_ == 0 {
                    v___x_2485_ = v___x_2482_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
                    v___x_2485_ = v_reuseFailAlloc_2486_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2485_;
            }
            9 => {
                if v_isShared_2491_ == 0 {
                    v___x_2493_ = v___x_2490_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
                    v___x_2493_ = v_reuseFailAlloc_2494_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2493_;
            }
            11 => {
                if v_isShared_2499_ == 0 {
                    v___x_2501_ = v___x_2498_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
                    v___x_2501_ = v_reuseFailAlloc_2502_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___boxed(
    mut v_a_2510_: *mut LeanObject,
    mut v___x_2511_: *mut LeanObject,
    mut v_inv_2512_: *mut LeanObject,
    mut v_declName_2513_: *mut LeanObject,
    mut v_levelParams_2514_: *mut LeanObject,
    mut v_xs_2515_: *mut LeanObject,
    mut v_body_2516_: *mut LeanObject,
    mut v___y_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inv_boxed_2522_: u8 = 0;
    let mut v_res_2523_: *mut LeanObject = core::ptr::null_mut();
    v_inv_boxed_2522_ = (lean_unbox(v_inv_2512_) as u8);
    v_res_2523_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0(
        v_a_2510_,
        v___x_2511_,
        v_inv_boxed_2522_,
        v_declName_2513_,
        v_levelParams_2514_,
        v_xs_2515_,
        v_body_2516_,
        v___y_2517_,
        v___y_2518_,
        v___y_2519_,
        v___y_2520_,
    );
    lean_dec(v___y_2520_);
    lean_dec_ref(v___y_2519_);
    lean_dec(v___y_2518_);
    lean_dec_ref(v___y_2517_);
    lean_dec_ref(v_body_2516_);
    lean_dec_ref(v_xs_2515_);
    return v_res_2523_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2524_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    v___x_2525_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0);
    v___x_2526_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2526_, 0, v___x_2525_);
    return v___x_2526_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    v___x_2527_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1);
    v___x_2528_ = lean_unsigned_to_nat(0);
    v___x_2529_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2529_, 0, v___x_2528_);
    lean_ctor_set(v___x_2529_, 1, v___x_2528_);
    lean_ctor_set(v___x_2529_, 2, v___x_2528_);
    lean_ctor_set(v___x_2529_, 3, v___x_2528_);
    lean_ctor_set(v___x_2529_, 4, v___x_2527_);
    lean_ctor_set(v___x_2529_, 5, v___x_2527_);
    lean_ctor_set(v___x_2529_, 6, v___x_2527_);
    lean_ctor_set(v___x_2529_, 7, v___x_2527_);
    lean_ctor_set(v___x_2529_, 8, v___x_2527_);
    lean_ctor_set(v___x_2529_, 9, v___x_2527_);
    return v___x_2529_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    v___x_2530_ = lean_unsigned_to_nat(32);
    v___x_2531_ = lean_mk_empty_array_with_capacity(v___x_2530_);
    v___x_2532_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2532_, 0, v___x_2531_);
    return v___x_2532_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2533_: usize = 0;
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    v___x_2533_ = 5usize;
    v___x_2534_ = lean_unsigned_to_nat(0);
    v___x_2535_ = lean_unsigned_to_nat(32);
    v___x_2536_ = lean_mk_empty_array_with_capacity(v___x_2535_);
    v___x_2537_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3);
    v___x_2538_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2538_, 0, v___x_2537_);
    lean_ctor_set(v___x_2538_, 1, v___x_2536_);
    lean_ctor_set(v___x_2538_, 2, v___x_2534_);
    lean_ctor_set(v___x_2538_, 3, v___x_2534_);
    lean_ctor_set_usize(v___x_2538_, 4, v___x_2533_);
    return v___x_2538_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    v___x_2539_ = lean_box(1);
    v___x_2540_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4);
    v___x_2541_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1);
    v___x_2542_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2542_, 0, v___x_2541_);
    lean_ctor_set(v___x_2542_, 1, v___x_2540_);
    lean_ctor_set(v___x_2542_, 2, v___x_2539_);
    return v___x_2542_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    v___x_2544_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__6;
    v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
    return v___x_2545_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__8;
    v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
    return v___x_2548_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    v___x_2550_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__10;
    v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
    return v___x_2551_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    v___x_2553_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__12;
    v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
    return v___x_2554_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    v___x_2556_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__14;
    v___x_2557_ = l_Lean_stringToMessageData(v___x_2556_);
    return v___x_2557_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    v___x_2559_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__16;
    v___x_2560_ = l_Lean_stringToMessageData(v___x_2559_);
    return v___x_2560_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    v___x_2562_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__18;
    v___x_2563_ = l_Lean_stringToMessageData(v___x_2562_);
    return v___x_2563_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg(
    mut v_msg_2564_: *mut LeanObject,
    mut v_declHint_2565_: *mut LeanObject,
    mut v___y_2566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u8 = 0;
    let mut v_isExporting_2571_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2568_ = lean_st_ref_get(v___y_2566_);
                v_env_2569_ = lean_ctor_get(v___x_2568_, 0);
                lean_inc_ref(v_env_2569_);
                lean_dec(v___x_2568_);
                v___x_2570_ = l_Lean_Name_isAnonymous(v_declHint_2565_);
                if v___x_2570_ == 0 {
                    v_isExporting_2571_ = lean_ctor_get_uint8(
                        v_env_2569_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2571_ == 0 {
                        lean_dec_ref(v_env_2569_);
                        lean_dec(v_declHint_2565_);
                        v___x_2572_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2572_, 0, v_msg_2564_);
                        return v___x_2572_;
                    } else {
                        lean_inc_ref(v_env_2569_);
                        v___x_2573_ = l_Lean_Environment_setExporting(v_env_2569_, v___x_2570_);
                        lean_inc(v_declHint_2565_);
                        lean_inc_ref(v___x_2573_);
                        v___x_2574_ = l_Lean_Environment_contains(
                            v___x_2573_,
                            v_declHint_2565_,
                            v_isExporting_2571_,
                        );
                        if v___x_2574_ == 0 {
                            lean_dec_ref(v___x_2573_);
                            lean_dec_ref(v_env_2569_);
                            lean_dec(v_declHint_2565_);
                            v___x_2575_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2575_, 0, v_msg_2564_);
                            return v___x_2575_;
                        } else {
                            v___x_2576_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2);
                            v___x_2577_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5);
                            v___x_2578_ = l_Lean_Options_empty;
                            v___x_2579_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_2579_, 0, v___x_2573_);
                            lean_ctor_set(v___x_2579_, 1, v___x_2576_);
                            lean_ctor_set(v___x_2579_, 2, v___x_2577_);
                            lean_ctor_set(v___x_2579_, 3, v___x_2578_);
                            lean_inc(v_declHint_2565_);
                            v___x_2580_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2565_, v___x_2570_);
                            v_c_2581_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_2581_, 0, v___x_2579_);
                            lean_ctor_set(v_c_2581_, 1, v___x_2580_);
                            v___x_2582_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2569_,
                                v_declHint_2565_,
                            );
                            if lean_obj_tag(v___x_2582_) == 0 {
                                lean_dec_ref(v_env_2569_);
                                lean_dec(v_declHint_2565_);
                                v___x_2583_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7);
                                v___x_2584_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2584_, 0, v___x_2583_);
                                lean_ctor_set(v___x_2584_, 1, v_c_2581_);
                                v___x_2585_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9);
                                v___x_2586_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2586_, 0, v___x_2584_);
                                lean_ctor_set(v___x_2586_, 1, v___x_2585_);
                                v___x_2587_ = l_Lean_MessageData_note(v___x_2586_);
                                v___x_2588_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2588_, 0, v_msg_2564_);
                                lean_ctor_set(v___x_2588_, 1, v___x_2587_);
                                v___x_2589_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2589_, 0, v___x_2588_);
                                return v___x_2589_;
                            } else {
                                v_val_2590_ = lean_ctor_get(v___x_2582_, 0);
                                v_isSharedCheck_2625_ = (!lean_is_exclusive(v___x_2582_)) as u8;
                                if v_isSharedCheck_2625_ == 0 {
                                    v___x_2592_ = v___x_2582_;
                                    v_isShared_2593_ = v_isSharedCheck_2625_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_2590_);
                                    lean_dec(v___x_2582_);
                                    v___x_2592_ = lean_box(0);
                                    v_isShared_2593_ = v_isSharedCheck_2625_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_2569_);
                    lean_dec(v_declHint_2565_);
                    v___x_2626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2626_, 0, v_msg_2564_);
                    return v___x_2626_;
                }
            }
            1 => {
                v___x_2594_ = lean_box(0);
                v___x_2595_ = l_Lean_Environment_header(v_env_2569_);
                lean_dec_ref(v_env_2569_);
                v___x_2596_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2595_);
                v_mod_2597_ = lean_array_get(v___x_2594_, v___x_2596_, v_val_2590_);
                lean_dec(v_val_2590_);
                lean_dec_ref(v___x_2596_);
                v___x_2598_ = l_Lean_isPrivateName(v_declHint_2565_);
                lean_dec(v_declHint_2565_);
                if v___x_2598_ == 0 {
                    v___x_2599_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11);
                    v___x_2600_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2600_, 0, v___x_2599_);
                    lean_ctor_set(v___x_2600_, 1, v_c_2581_);
                    v___x_2601_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13);
                    v___x_2602_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2602_, 0, v___x_2600_);
                    lean_ctor_set(v___x_2602_, 1, v___x_2601_);
                    v___x_2603_ = l_Lean_MessageData_ofName(v_mod_2597_);
                    v___x_2604_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2604_, 0, v___x_2602_);
                    lean_ctor_set(v___x_2604_, 1, v___x_2603_);
                    v___x_2605_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15);
                    v___x_2606_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2606_, 0, v___x_2604_);
                    lean_ctor_set(v___x_2606_, 1, v___x_2605_);
                    v___x_2607_ = l_Lean_MessageData_note(v___x_2606_);
                    v___x_2608_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2608_, 0, v_msg_2564_);
                    lean_ctor_set(v___x_2608_, 1, v___x_2607_);
                    if v_isShared_2593_ == 0 {
                        lean_ctor_set_tag(v___x_2592_, 0);
                        lean_ctor_set(v___x_2592_, 0, v___x_2608_);
                        v___x_2610_ = v___x_2592_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
                        v___x_2610_ = v_reuseFailAlloc_2611_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2612_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7);
                    v___x_2613_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2613_, 0, v___x_2612_);
                    lean_ctor_set(v___x_2613_, 1, v_c_2581_);
                    v___x_2614_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17);
                    v___x_2615_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2615_, 0, v___x_2613_);
                    lean_ctor_set(v___x_2615_, 1, v___x_2614_);
                    v___x_2616_ = l_Lean_MessageData_ofName(v_mod_2597_);
                    v___x_2617_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2617_, 0, v___x_2615_);
                    lean_ctor_set(v___x_2617_, 1, v___x_2616_);
                    v___x_2618_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19);
                    v___x_2619_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2619_, 0, v___x_2617_);
                    lean_ctor_set(v___x_2619_, 1, v___x_2618_);
                    v___x_2620_ = l_Lean_MessageData_note(v___x_2619_);
                    v___x_2621_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2621_, 0, v_msg_2564_);
                    lean_ctor_set(v___x_2621_, 1, v___x_2620_);
                    if v_isShared_2593_ == 0 {
                        lean_ctor_set_tag(v___x_2592_, 0);
                        lean_ctor_set(v___x_2592_, 0, v___x_2621_);
                        v___x_2623_ = v___x_2592_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
                        v___x_2623_ = v_reuseFailAlloc_2624_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2610_;
            }
            3 => {
                return v___x_2623_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___boxed(
    mut v_msg_2627_: *mut LeanObject,
    mut v_declHint_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2631_: *mut LeanObject = core::ptr::null_mut();
    v_res_2631_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg(v_msg_2627_, v_declHint_2628_, v___y_2629_);
    lean_dec(v___y_2629_);
    return v_res_2631_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7(
    mut v_msg_2632_: *mut LeanObject,
    mut v_declHint_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2639_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg(v_msg_2632_, v_declHint_2633_, v___y_2637_);
                v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
                v_isSharedCheck_2649_ = (!lean_is_exclusive(v___x_2639_)) as u8;
                if v_isSharedCheck_2649_ == 0 {
                    v___x_2642_ = v___x_2639_;
                    v_isShared_2643_ = v_isSharedCheck_2649_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2640_);
                    lean_dec(v___x_2639_);
                    v___x_2642_ = lean_box(0);
                    v_isShared_2643_ = v_isSharedCheck_2649_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2644_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2645_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                lean_ctor_set(v___x_2645_, 1, v_a_2640_);
                if v_isShared_2643_ == 0 {
                    lean_ctor_set(v___x_2642_, 0, v___x_2645_);
                    v___x_2647_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
                    v___x_2647_ = v_reuseFailAlloc_2648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(
    mut v_msg_2650_: *mut LeanObject,
    mut v_declHint_2651_: *mut LeanObject,
    mut v___y_2652_: *mut LeanObject,
    mut v___y_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
    mut v___y_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2657_: *mut LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7(v_msg_2650_, v_declHint_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
    lean_dec(v___y_2655_);
    lean_dec_ref(v___y_2654_);
    lean_dec(v___y_2653_);
    lean_dec_ref(v___y_2652_);
    return v_res_2657_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg(
    mut v_ref_2658_: *mut LeanObject,
    mut v_msg_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
    mut v___y_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
    mut v___y_2663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2677_: u8 = 0;
    let mut v_cancelTk_x3f_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2679_: u8 = 0;
    let mut v_inheritedTraceOptions_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2665_ = lean_ctor_get(v___y_2662_, 0);
    v_fileMap_2666_ = lean_ctor_get(v___y_2662_, 1);
    v_options_2667_ = lean_ctor_get(v___y_2662_, 2);
    v_currRecDepth_2668_ = lean_ctor_get(v___y_2662_, 3);
    v_maxRecDepth_2669_ = lean_ctor_get(v___y_2662_, 4);
    v_ref_2670_ = lean_ctor_get(v___y_2662_, 5);
    v_currNamespace_2671_ = lean_ctor_get(v___y_2662_, 6);
    v_openDecls_2672_ = lean_ctor_get(v___y_2662_, 7);
    v_initHeartbeats_2673_ = lean_ctor_get(v___y_2662_, 8);
    v_maxHeartbeats_2674_ = lean_ctor_get(v___y_2662_, 9);
    v_quotContext_2675_ = lean_ctor_get(v___y_2662_, 10);
    v_currMacroScope_2676_ = lean_ctor_get(v___y_2662_, 11);
    v_diag_2677_ = lean_ctor_get_uint8(
        v___y_2662_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2678_ = lean_ctor_get(v___y_2662_, 12);
    v_suppressElabErrors_2679_ = lean_ctor_get_uint8(
        v___y_2662_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2680_ = lean_ctor_get(v___y_2662_, 13);
    v_ref_2681_ = l_Lean_replaceRef(v_ref_2658_, v_ref_2670_);
    lean_inc_ref(v_inheritedTraceOptions_2680_);
    lean_inc(v_cancelTk_x3f_2678_);
    lean_inc(v_currMacroScope_2676_);
    lean_inc(v_quotContext_2675_);
    lean_inc(v_maxHeartbeats_2674_);
    lean_inc(v_initHeartbeats_2673_);
    lean_inc(v_openDecls_2672_);
    lean_inc(v_currNamespace_2671_);
    lean_inc(v_maxRecDepth_2669_);
    lean_inc(v_currRecDepth_2668_);
    lean_inc_ref(v_options_2667_);
    lean_inc_ref(v_fileMap_2666_);
    lean_inc_ref(v_fileName_2665_);
    v___x_2682_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2682_, 0, v_fileName_2665_);
    lean_ctor_set(v___x_2682_, 1, v_fileMap_2666_);
    lean_ctor_set(v___x_2682_, 2, v_options_2667_);
    lean_ctor_set(v___x_2682_, 3, v_currRecDepth_2668_);
    lean_ctor_set(v___x_2682_, 4, v_maxRecDepth_2669_);
    lean_ctor_set(v___x_2682_, 5, v_ref_2681_);
    lean_ctor_set(v___x_2682_, 6, v_currNamespace_2671_);
    lean_ctor_set(v___x_2682_, 7, v_openDecls_2672_);
    lean_ctor_set(v___x_2682_, 8, v_initHeartbeats_2673_);
    lean_ctor_set(v___x_2682_, 9, v_maxHeartbeats_2674_);
    lean_ctor_set(v___x_2682_, 10, v_quotContext_2675_);
    lean_ctor_set(v___x_2682_, 11, v_currMacroScope_2676_);
    lean_ctor_set(v___x_2682_, 12, v_cancelTk_x3f_2678_);
    lean_ctor_set(v___x_2682_, 13, v_inheritedTraceOptions_2680_);
    lean_ctor_set_uint8(
        v___x_2682_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2677_,
    );
    lean_ctor_set_uint8(
        v___x_2682_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2679_,
    );
    v___x_2683_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(
            v_msg_2659_,
            v___y_2660_,
            v___y_2661_,
            v___x_2682_,
            v___y_2663_,
        );
    lean_dec_ref_known(v___x_2682_, 14);
    return v___x_2683_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg___boxed(
    mut v_ref_2684_: *mut LeanObject,
    mut v_msg_2685_: *mut LeanObject,
    mut v___y_2686_: *mut LeanObject,
    mut v___y_2687_: *mut LeanObject,
    mut v___y_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2691_: *mut LeanObject = core::ptr::null_mut();
    v_res_2691_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg(v_ref_2684_, v_msg_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
    lean_dec(v___y_2689_);
    lean_dec_ref(v___y_2688_);
    lean_dec(v___y_2687_);
    lean_dec_ref(v___y_2686_);
    lean_dec(v_ref_2684_);
    return v_res_2691_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_ref_2692_: *mut LeanObject,
    mut v_msg_2693_: *mut LeanObject,
    mut v_declHint_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    v___x_2700_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7(v_msg_2693_, v_declHint_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
    v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
    lean_inc(v_a_2701_);
    lean_dec_ref(v___x_2700_);
    v___x_2702_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg(v_ref_2692_, v_a_2701_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
    return v___x_2702_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_ref_2703_: *mut LeanObject,
    mut v_msg_2704_: *mut LeanObject,
    mut v_declHint_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2711_: *mut LeanObject = core::ptr::null_mut();
    v_res_2711_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg(v_ref_2703_, v_msg_2704_, v_declHint_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
    lean_dec(v___y_2709_);
    lean_dec_ref(v___y_2708_);
    lean_dec(v___y_2707_);
    lean_dec_ref(v___y_2706_);
    lean_dec(v_ref_2703_);
    return v_res_2711_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    v___x_2713_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
    return v___x_2714_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    v___x_2716_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_2717_ = l_Lean_stringToMessageData(v___x_2716_);
    return v___x_2717_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg(
    mut v_ref_2718_: *mut LeanObject,
    mut v_constName_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    v___x_2725_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_2726_ = 0;
    lean_inc(v_constName_2719_);
    v___x_2727_ = l_Lean_MessageData_ofConstName(v_constName_2719_, v___x_2726_);
    v___x_2728_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2728_, 0, v___x_2725_);
    lean_ctor_set(v___x_2728_, 1, v___x_2727_);
    v___x_2729_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_2730_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2730_, 0, v___x_2728_);
    lean_ctor_set(v___x_2730_, 1, v___x_2729_);
    v___x_2731_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg(v_ref_2718_, v___x_2730_, v_constName_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
    return v___x_2731_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_2732_: *mut LeanObject,
    mut v_constName_2733_: *mut LeanObject,
    mut v___y_2734_: *mut LeanObject,
    mut v___y_2735_: *mut LeanObject,
    mut v___y_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2739_: *mut LeanObject = core::ptr::null_mut();
    v_res_2739_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg(v_ref_2732_, v_constName_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
    lean_dec(v___y_2737_);
    lean_dec_ref(v___y_2736_);
    lean_dec(v___y_2735_);
    lean_dec_ref(v___y_2734_);
    lean_dec(v_ref_2732_);
    return v_res_2739_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg(
    mut v_constName_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2746_ = lean_ctor_get(v___y_2743_, 5);
    v___x_2747_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg(v_ref_2746_, v_constName_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
    return v___x_2747_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg___boxed(
    mut v_constName_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2754_: *mut LeanObject = core::ptr::null_mut();
    v_res_2754_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg(v_constName_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
    lean_dec(v___y_2752_);
    lean_dec_ref(v___y_2751_);
    lean_dec(v___y_2750_);
    lean_dec_ref(v___y_2749_);
    return v_res_2754_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0(
    mut v_constName_2755_: *mut LeanObject,
    mut v___y_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2769_: u8 = 0;
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2761_ = lean_st_ref_get(v___y_2759_);
                v_env_2762_ = lean_ctor_get(v___x_2761_, 0);
                lean_inc_ref(v_env_2762_);
                lean_dec(v___x_2761_);
                v___x_2763_ = 0;
                lean_inc(v_constName_2755_);
                v___x_2764_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2762_,
                    v_constName_2755_,
                    v___x_2763_,
                );
                if lean_obj_tag(v___x_2764_) == 0 {
                    v___x_2765_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg(v_constName_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
                    return v___x_2765_;
                } else {
                    lean_dec(v_constName_2755_);
                    v_val_2766_ = lean_ctor_get(v___x_2764_, 0);
                    v_isSharedCheck_2773_ = (!lean_is_exclusive(v___x_2764_)) as u8;
                    if v_isSharedCheck_2773_ == 0 {
                        v___x_2768_ = v___x_2764_;
                        v_isShared_2769_ = v_isSharedCheck_2773_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2766_);
                        lean_dec(v___x_2764_);
                        v___x_2768_ = lean_box(0);
                        v_isShared_2769_ = v_isSharedCheck_2773_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2769_ == 0 {
                    lean_ctor_set_tag(v___x_2768_, 0);
                    v___x_2771_ = v___x_2768_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_val_2766_);
                    v___x_2771_ = v_reuseFailAlloc_2772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0___boxed(
    mut v_constName_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2780_: *mut LeanObject = core::ptr::null_mut();
    v_res_2780_ = l_Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0(
        v_constName_2774_,
        v___y_2775_,
        v___y_2776_,
        v___y_2777_,
        v___y_2778_,
    );
    lean_dec(v___y_2778_);
    lean_dec_ref(v___y_2777_);
    lean_dec(v___y_2776_);
    lean_dec_ref(v___y_2775_);
    return v_res_2780_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__1(
    mut v_a_2781_: *mut LeanObject,
    mut v_a_2782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2781_) == 0 {
                    v___x_2783_ = l_List_reverse___redArg(v_a_2782_);
                    return v___x_2783_;
                } else {
                    v_head_2784_ = lean_ctor_get(v_a_2781_, 0);
                    v_tail_2785_ = lean_ctor_get(v_a_2781_, 1);
                    v_isSharedCheck_2794_ = (!lean_is_exclusive(v_a_2781_)) as u8;
                    if v_isSharedCheck_2794_ == 0 {
                        v___x_2787_ = v_a_2781_;
                        v_isShared_2788_ = v_isSharedCheck_2794_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2785_);
                        lean_inc(v_head_2784_);
                        lean_dec(v_a_2781_);
                        v___x_2787_ = lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_2794_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2789_ = l_Lean_mkLevelParam(v_head_2784_);
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 1, v_a_2782_);
                    lean_ctor_set(v___x_2787_, 0, v___x_2789_);
                    v___x_2791_ = v___x_2787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_a_2782_);
                    v___x_2791_ = v_reuseFailAlloc_2793_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2781_ = v_tail_2785_;
                v_a_2782_ = v___x_2791_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1() -> *mut LeanObject {
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    v___x_2796_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__0;
    v___x_2797_ = l_Lean_stringToMessageData(v___x_2796_);
    return v___x_2797_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst(
    mut v_declName_2798_: *mut LeanObject,
    mut v_inv_2799_: u8,
    mut v_a_2800_: *mut LeanObject,
    mut v_a_2801_: *mut LeanObject,
    mut v_a_2802_: *mut LeanObject,
    mut v_a_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2834_: u8 = 0;
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_a_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_a_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v___x_2858_: u8 = 0;
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v_a_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v_isSharedCheck_2887_: u8 = 0;
    let mut v_unused_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_2798_);
                v___x_2805_ =
                    l_Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0(
                        v_declName_2798_,
                        v_a_2800_,
                        v_a_2801_,
                        v_a_2802_,
                        v_a_2803_,
                    );
                if lean_obj_tag(v___x_2805_) == 0 {
                    v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
                    lean_inc(v_a_2806_);
                    lean_dec_ref_known(v___x_2805_, 1);
                    v_levelParams_2807_ = lean_ctor_get(v_a_2806_, 1);
                    v_isSharedCheck_2887_ = (!lean_is_exclusive(v_a_2806_)) as u8;
                    if v_isSharedCheck_2887_ == 0 {
                        v_unused_2888_ = lean_ctor_get(v_a_2806_, 2);
                        lean_dec(v_unused_2888_);
                        v_unused_2889_ = lean_ctor_get(v_a_2806_, 0);
                        lean_dec(v_unused_2889_);
                        v___x_2809_ = v_a_2806_;
                        v_isShared_2810_ = v_isSharedCheck_2887_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_levelParams_2807_);
                        lean_dec(v_a_2806_);
                        v___x_2809_ = lean_box(0);
                        v_isShared_2810_ = v_isSharedCheck_2887_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_2798_);
                    v_a_2890_ = lean_ctor_get(v___x_2805_, 0);
                    v_isSharedCheck_2897_ = (!lean_is_exclusive(v___x_2805_)) as u8;
                    if v_isSharedCheck_2897_ == 0 {
                        v___x_2892_ = v___x_2805_;
                        v_isShared_2893_ = v_isSharedCheck_2897_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2890_);
                        lean_dec(v___x_2805_);
                        v___x_2892_ = lean_box(0);
                        v_isShared_2893_ = v_isSharedCheck_2897_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2811_ = lean_box(0);
                lean_inc(v_levelParams_2807_);
                v___x_2812_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__1(
                        v_levelParams_2807_,
                        v___x_2811_,
                    );
                lean_inc(v_declName_2798_);
                v___x_2813_ = l_Lean_mkConst(v_declName_2798_, v___x_2812_);
                lean_inc(v_a_2803_);
                lean_inc_ref(v_a_2802_);
                lean_inc(v_a_2801_);
                lean_inc_ref(v_a_2800_);
                lean_inc_ref(v___x_2813_);
                v___x_2814_ =
                    lean_infer_type(v___x_2813_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
                if lean_obj_tag(v___x_2814_) == 0 {
                    v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
                    lean_inc_n(v_a_2815_, 2);
                    lean_dec_ref_known(v___x_2814_, 1);
                    v___x_2816_ =
                        l_Lean_Meta_isProp(v_a_2815_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
                    if lean_obj_tag(v___x_2816_) == 0 {
                        v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
                        lean_inc(v_a_2817_);
                        lean_dec_ref_known(v___x_2816_, 1);
                        v___x_2818_ = lean_box((v_inv_2799_) as usize);
                        lean_inc(v_declName_2798_);
                        lean_inc_ref(v___x_2813_);
                        lean_inc(v_a_2815_);
                        v___f_2819_ = lean_alloc_closure(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___boxed
                                as *mut core::ffi::c_void,
                            12,
                            5,
                        );
                        lean_closure_set(v___f_2819_, 0, v_a_2815_);
                        lean_closure_set(v___f_2819_, 1, v___x_2813_);
                        lean_closure_set(v___f_2819_, 2, v___x_2818_);
                        lean_closure_set(v___f_2819_, 3, v_declName_2798_);
                        lean_closure_set(v___f_2819_, 4, v_levelParams_2807_);
                        v___x_2858_ = (lean_unbox(v_a_2817_) as u8);
                        lean_dec(v_a_2817_);
                        if v___x_2858_ == 0 {
                            lean_dec_ref(v___f_2819_);
                            lean_dec(v_a_2815_);
                            lean_del_object(v___x_2809_);
                            lean_dec(v_declName_2798_);
                            v___x_2859_ = l_Lean_MessageData_ofExpr(v___x_2813_);
                            v___x_2860_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1_once
                                ),
                                _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1,
                            );
                            v___x_2861_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2861_, 0, v___x_2859_);
                            lean_ctor_set(v___x_2861_, 1, v___x_2860_);
                            v___x_2862_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(v___x_2861_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
                            v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
                            v_isSharedCheck_2870_ = (!lean_is_exclusive(v___x_2862_)) as u8;
                            if v_isSharedCheck_2870_ == 0 {
                                v___x_2865_ = v___x_2862_;
                                v_isShared_2866_ = v_isSharedCheck_2870_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_2863_);
                                lean_dec(v___x_2862_);
                                v___x_2865_ = lean_box(0);
                                v_isShared_2866_ = v_isSharedCheck_2870_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_2813_);
                            v___y_2821_ = v_a_2800_;
                            v___y_2822_ = v_a_2801_;
                            v___y_2823_ = v_a_2802_;
                            v___y_2824_ = v_a_2803_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2815_);
                        lean_dec_ref(v___x_2813_);
                        lean_del_object(v___x_2809_);
                        lean_dec(v_levelParams_2807_);
                        lean_dec(v_declName_2798_);
                        v_a_2871_ = lean_ctor_get(v___x_2816_, 0);
                        v_isSharedCheck_2878_ = (!lean_is_exclusive(v___x_2816_)) as u8;
                        if v_isSharedCheck_2878_ == 0 {
                            v___x_2873_ = v___x_2816_;
                            v_isShared_2874_ = v_isSharedCheck_2878_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2871_);
                            lean_dec(v___x_2816_);
                            v___x_2873_ = lean_box(0);
                            v_isShared_2874_ = v_isSharedCheck_2878_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2813_);
                    lean_del_object(v___x_2809_);
                    lean_dec(v_levelParams_2807_);
                    lean_dec(v_declName_2798_);
                    v_a_2879_ = lean_ctor_get(v___x_2814_, 0);
                    v_isSharedCheck_2886_ = (!lean_is_exclusive(v___x_2814_)) as u8;
                    if v_isSharedCheck_2886_ == 0 {
                        v___x_2881_ = v___x_2814_;
                        v_isShared_2882_ = v_isSharedCheck_2886_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2879_);
                        lean_dec(v___x_2814_);
                        v___x_2881_ = lean_box(0);
                        v_isShared_2882_ = v_isSharedCheck_2886_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2825_ = 0;
                v___x_2826_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg(v_a_2815_, v___f_2819_, v___x_2825_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
                if lean_obj_tag(v___x_2826_) == 0 {
                    v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
                    lean_inc(v_a_2827_);
                    lean_dec_ref_known(v___x_2826_, 1);
                    v_fst_2828_ = lean_ctor_get(v_a_2827_, 0);
                    lean_inc(v_fst_2828_);
                    v_snd_2829_ = lean_ctor_get(v_a_2827_, 1);
                    lean_inc(v_snd_2829_);
                    lean_dec(v_a_2827_);
                    v___x_2830_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
                        v_snd_2829_,
                        v___y_2821_,
                        v___y_2822_,
                        v___y_2823_,
                        v___y_2824_,
                    );
                    if lean_obj_tag(v___x_2830_) == 0 {
                        v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
                        v_isSharedCheck_2841_ = (!lean_is_exclusive(v___x_2830_)) as u8;
                        if v_isSharedCheck_2841_ == 0 {
                            v___x_2833_ = v___x_2830_;
                            v_isShared_2834_ = v_isSharedCheck_2841_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2831_);
                            lean_dec(v___x_2830_);
                            v___x_2833_ = lean_box(0);
                            v_isShared_2834_ = v_isSharedCheck_2841_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_fst_2828_);
                        lean_del_object(v___x_2809_);
                        lean_dec(v_declName_2798_);
                        v_a_2842_ = lean_ctor_get(v___x_2830_, 0);
                        v_isSharedCheck_2849_ = (!lean_is_exclusive(v___x_2830_)) as u8;
                        if v_isSharedCheck_2849_ == 0 {
                            v___x_2844_ = v___x_2830_;
                            v_isShared_2845_ = v_isSharedCheck_2849_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2842_);
                            lean_dec(v___x_2830_);
                            v___x_2844_ = lean_box(0);
                            v_isShared_2845_ = v_isSharedCheck_2849_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2809_);
                    lean_dec(v_declName_2798_);
                    v_a_2850_ = lean_ctor_get(v___x_2826_, 0);
                    v_isSharedCheck_2857_ = (!lean_is_exclusive(v___x_2826_)) as u8;
                    if v_isSharedCheck_2857_ == 0 {
                        v___x_2852_ = v___x_2826_;
                        v_isShared_2853_ = v_isSharedCheck_2857_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2850_);
                        lean_dec(v___x_2826_);
                        v___x_2852_ = lean_box(0);
                        v_isShared_2853_ = v_isSharedCheck_2857_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2810_ == 0 {
                    lean_ctor_set(v___x_2809_, 2, v_a_2831_);
                    lean_ctor_set(v___x_2809_, 1, v_fst_2828_);
                    lean_ctor_set(v___x_2809_, 0, v_declName_2798_);
                    v___x_2836_ = v___x_2809_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_declName_2798_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_fst_2828_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_a_2831_);
                    v___x_2836_ = v_reuseFailAlloc_2840_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2834_ == 0 {
                    lean_ctor_set(v___x_2833_, 0, v___x_2836_);
                    v___x_2838_ = v___x_2833_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
                    v___x_2838_ = v_reuseFailAlloc_2839_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2838_;
            }
            6 => {
                if v_isShared_2845_ == 0 {
                    v___x_2847_ = v___x_2844_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2847_;
            }
            8 => {
                if v_isShared_2853_ == 0 {
                    v___x_2855_ = v___x_2852_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
                    v___x_2855_ = v_reuseFailAlloc_2856_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2855_;
            }
            10 => {
                if v_isShared_2866_ == 0 {
                    v___x_2868_ = v___x_2865_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
                    v___x_2868_ = v_reuseFailAlloc_2869_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2868_;
            }
            12 => {
                if v_isShared_2874_ == 0 {
                    v___x_2876_ = v___x_2873_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2877_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2876_;
            }
            14 => {
                if v_isShared_2882_ == 0 {
                    v___x_2884_ = v___x_2881_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
                    v___x_2884_ = v_reuseFailAlloc_2885_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2884_;
            }
            16 => {
                if v_isShared_2893_ == 0 {
                    v___x_2895_ = v___x_2892_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
                    v___x_2895_ = v_reuseFailAlloc_2896_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___boxed(
    mut v_declName_2898_: *mut LeanObject,
    mut v_inv_2899_: *mut LeanObject,
    mut v_a_2900_: *mut LeanObject,
    mut v_a_2901_: *mut LeanObject,
    mut v_a_2902_: *mut LeanObject,
    mut v_a_2903_: *mut LeanObject,
    mut v_a_2904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inv_boxed_2905_: u8 = 0;
    let mut v_res_2906_: *mut LeanObject = core::ptr::null_mut();
    v_inv_boxed_2905_ = (lean_unbox(v_inv_2899_) as u8);
    v_res_2906_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst(
        v_declName_2898_,
        v_inv_boxed_2905_,
        v_a_2900_,
        v_a_2901_,
        v_a_2902_,
        v_a_2903_,
    );
    lean_dec(v_a_2903_);
    lean_dec_ref(v_a_2902_);
    lean_dec(v_a_2901_);
    lean_dec_ref(v_a_2900_);
    return v_res_2906_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2(
    mut v_00_u03b1_2907_: *mut LeanObject,
    mut v_msg_2908_: *mut LeanObject,
    mut v___y_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    v___x_2914_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(
            v_msg_2908_,
            v___y_2909_,
            v___y_2910_,
            v___y_2911_,
            v___y_2912_,
        );
    return v___x_2914_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___boxed(
    mut v_00_u03b1_2915_: *mut LeanObject,
    mut v_msg_2916_: *mut LeanObject,
    mut v___y_2917_: *mut LeanObject,
    mut v___y_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2922_: *mut LeanObject = core::ptr::null_mut();
    v_res_2922_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2(
        v_00_u03b1_2915_,
        v_msg_2916_,
        v___y_2917_,
        v___y_2918_,
        v___y_2919_,
        v___y_2920_,
    );
    lean_dec(v___y_2920_);
    lean_dec_ref(v___y_2919_);
    lean_dec(v___y_2918_);
    lean_dec_ref(v___y_2917_);
    return v_res_2922_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0(
    mut v_00_u03b1_2923_: *mut LeanObject,
    mut v_constName_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
    mut v___y_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    v___x_2930_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg(v_constName_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
    return v___x_2930_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___boxed(
    mut v_00_u03b1_2931_: *mut LeanObject,
    mut v_constName_2932_: *mut LeanObject,
    mut v___y_2933_: *mut LeanObject,
    mut v___y_2934_: *mut LeanObject,
    mut v___y_2935_: *mut LeanObject,
    mut v___y_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2938_: *mut LeanObject = core::ptr::null_mut();
    v_res_2938_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0(v_00_u03b1_2931_, v_constName_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
    lean_dec(v___y_2936_);
    lean_dec_ref(v___y_2935_);
    lean_dec(v___y_2934_);
    lean_dec_ref(v___y_2933_);
    return v_res_2938_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2(
    mut v_00_u03b1_2939_: *mut LeanObject,
    mut v_ref_2940_: *mut LeanObject,
    mut v_constName_2941_: *mut LeanObject,
    mut v___y_2942_: *mut LeanObject,
    mut v___y_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    v___x_2947_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg(v_ref_2940_, v_constName_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
    return v___x_2947_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_2948_: *mut LeanObject,
    mut v_ref_2949_: *mut LeanObject,
    mut v_constName_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
    mut v___y_2953_: *mut LeanObject,
    mut v___y_2954_: *mut LeanObject,
    mut v___y_2955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2956_: *mut LeanObject = core::ptr::null_mut();
    v_res_2956_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2(v_00_u03b1_2948_, v_ref_2949_, v_constName_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
    lean_dec(v___y_2954_);
    lean_dec_ref(v___y_2953_);
    lean_dec(v___y_2952_);
    lean_dec_ref(v___y_2951_);
    lean_dec(v_ref_2949_);
    return v_res_2956_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b1_2957_: *mut LeanObject,
    mut v_ref_2958_: *mut LeanObject,
    mut v_msg_2959_: *mut LeanObject,
    mut v_declHint_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    v___x_2966_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg(v_ref_2958_, v_msg_2959_, v_declHint_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
    return v___x_2966_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b1_2967_: *mut LeanObject,
    mut v_ref_2968_: *mut LeanObject,
    mut v_msg_2969_: *mut LeanObject,
    mut v_declHint_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
    mut v___y_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2976_: *mut LeanObject = core::ptr::null_mut();
    v_res_2976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6(v_00_u03b1_2967_, v_ref_2968_, v_msg_2969_, v_declHint_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
    lean_dec(v___y_2974_);
    lean_dec_ref(v___y_2973_);
    lean_dec(v___y_2972_);
    lean_dec_ref(v___y_2971_);
    lean_dec(v_ref_2968_);
    return v_res_2976_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8(
    mut v_msg_2977_: *mut LeanObject,
    mut v_declHint_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
    mut v___y_2981_: *mut LeanObject,
    mut v___y_2982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    v___x_2984_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg(v_msg_2977_, v_declHint_2978_, v___y_2982_);
    return v___x_2984_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___boxed(
    mut v_msg_2985_: *mut LeanObject,
    mut v_declHint_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2992_: *mut LeanObject = core::ptr::null_mut();
    v_res_2992_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8(v_msg_2985_, v_declHint_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
    lean_dec(v___y_2990_);
    lean_dec_ref(v___y_2989_);
    lean_dec(v___y_2988_);
    lean_dec_ref(v___y_2987_);
    return v_res_2992_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8(
    mut v_00_u03b1_2993_: *mut LeanObject,
    mut v_ref_2994_: *mut LeanObject,
    mut v_msg_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
    mut v___y_2997_: *mut LeanObject,
    mut v___y_2998_: *mut LeanObject,
    mut v___y_2999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    v___x_3001_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg(v_ref_2994_, v_msg_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
    return v___x_3001_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___boxed(
    mut v_00_u03b1_3002_: *mut LeanObject,
    mut v_ref_3003_: *mut LeanObject,
    mut v_msg_3004_: *mut LeanObject,
    mut v___y_3005_: *mut LeanObject,
    mut v___y_3006_: *mut LeanObject,
    mut v___y_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3010_: *mut LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8(v_00_u03b1_3002_, v_ref_3003_, v_msg_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
    lean_dec(v___y_3008_);
    lean_dec_ref(v___y_3007_);
    lean_dec(v___y_3006_);
    lean_dec_ref(v___y_3005_);
    lean_dec(v_ref_3003_);
    return v_res_3010_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1() -> *mut LeanObject {
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    v___x_3017_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3017_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2() -> *mut LeanObject {
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    v___x_3018_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1_once),
        _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1,
    );
    v___x_3019_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3019_, 0, v___x_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry(
    mut v_s_3020_: *mut LeanObject,
    mut v_e_3021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lemmas_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v_appFn_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thm_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lemmas_3022_ = lean_ctor_get(v_s_3020_, 0);
                v_entries_3023_ = lean_ctor_get(v_s_3020_, 1);
                v_isSharedCheck_3047_ = (!lean_is_exclusive(v_s_3020_)) as u8;
                if v_isSharedCheck_3047_ == 0 {
                    v___x_3025_ = v_s_3020_;
                    v_isShared_3026_ = v_isSharedCheck_3047_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_entries_3023_);
                    lean_inc(v_lemmas_3022_);
                    lean_dec(v_s_3020_);
                    v___x_3025_ = lean_box(0);
                    v_isShared_3026_ = v_isSharedCheck_3047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_appFn_3027_ = lean_ctor_get(v_e_3021_, 1);
                lean_inc(v_appFn_3027_);
                v_thm_3028_ = lean_ctor_get(v_e_3021_, 2);
                v___x_3044_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_lemmas_3022_, v_appFn_3027_);
                if lean_obj_tag(v___x_3044_) == 0 {
                    v___x_3045_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2,
                    );
                    v___y_3040_ = v___x_3045_;
                    state = 4;
                    continue;
                } else {
                    v_val_3046_ = lean_ctor_get(v___x_3044_, 0);
                    lean_inc(v_val_3046_);
                    lean_dec_ref_known(v___x_3044_, 1);
                    v___y_3040_ = v_val_3046_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_thm_3028_);
                v___x_3032_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v___y_3030_, v_thm_3028_);
                lean_inc(v_appFn_3027_);
                v___x_3033_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3027_, v___x_3032_, v_lemmas_3022_);
                v___x_3034_ = lean_array_push(v___y_3031_, v_e_3021_);
                v___x_3035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3027_, v___x_3034_, v_entries_3023_);
                if v_isShared_3026_ == 0 {
                    lean_ctor_set(v___x_3025_, 1, v___x_3035_);
                    lean_ctor_set(v___x_3025_, 0, v___x_3033_);
                    v___x_3037_ = v___x_3025_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3033_);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3035_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3037_;
            }
            4 => {
                v___x_3041_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_3023_, v_appFn_3027_);
                if lean_obj_tag(v___x_3041_) == 0 {
                    v___x_3042_ = l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__0;
                    v___y_3030_ = v___y_3040_;
                    v___y_3031_ = v___x_3042_;
                    state = 2;
                    continue;
                } else {
                    v_val_3043_ = lean_ctor_get(v___x_3041_, 0);
                    lean_inc(v_val_3043_);
                    lean_dec_ref_known(v___x_3041_, 1);
                    v___y_3030_ = v___y_3040_;
                    v___y_3031_ = v_val_3043_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg(
    mut v_t_3048_: *mut LeanObject,
    mut v_k_3049_: *mut LeanObject,
    mut v_fallback_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3048_) == 0 {
                    v_k_3051_ = lean_ctor_get(v_t_3048_, 1);
                    v_v_3052_ = lean_ctor_get(v_t_3048_, 2);
                    v_l_3053_ = lean_ctor_get(v_t_3048_, 3);
                    v_r_3054_ = lean_ctor_get(v_t_3048_, 4);
                    v___x_3055_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3049_, v_k_3051_);
                    match v___x_3055_ {
                        0 => {
                            v_t_3048_ = v_l_3053_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_3052_);
                            return v_v_3052_;
                        }
                        _ => {
                            v_t_3048_ = v_r_3054_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_fallback_3050_);
                    return v_fallback_3050_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg___boxed(
    mut v_t_3058_: *mut LeanObject,
    mut v_k_3059_: *mut LeanObject,
    mut v_fallback_3060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3061_: *mut LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg(v_t_3058_, v_k_3059_, v_fallback_3060_);
    lean_dec(v_fallback_3060_);
    lean_dec(v_k_3059_);
    lean_dec(v_t_3058_);
    return v_res_3061_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(
    mut v_k_3062_: *mut LeanObject,
    mut v_t_3063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3070_: u8 = 0;
    let mut v___x_3071_: u8 = 0;
    let mut v_impl_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: u8 = 0;
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3090_: u8 = 0;
    let mut v_size_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v_unused_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3140_: u8 = 0;
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_unused_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_unused_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v_size_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_unused_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v_k_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_unused_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut v_unused_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3215_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v_unused_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v_unused_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v_size_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_unused_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut v_unused_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v_k_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3354_: u8 = 0;
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v_unused_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut v_unused_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3393_: u8 = 0;
    let mut v_unused_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: u8 = 0;
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v_size_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3429_: u8 = 0;
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3445_: u8 = 0;
    let mut v_unused_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3464_: u8 = 0;
    let mut v_unused_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut v_unused_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v_k_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut v_unused_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v_k_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3535_: u8 = 0;
    let mut v_unused_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut v_unused_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_unused_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v_size_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3587_: u8 = 0;
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3613_: u8 = 0;
    let mut v_unused_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_unused_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut v_unused_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v_size_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut v_unused_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut v_unused_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v_k_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3706_: u8 = 0;
    let mut v_unused_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut v_unused_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3721_: u8 = 0;
    let mut v_unused_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3063_) == 0 {
                    v_k_3064_ = lean_ctor_get(v_t_3063_, 1);
                    v_v_3065_ = lean_ctor_get(v_t_3063_, 2);
                    v_l_3066_ = lean_ctor_get(v_t_3063_, 3);
                    v_r_3067_ = lean_ctor_get(v_t_3063_, 4);
                    v_isSharedCheck_3721_ = (!lean_is_exclusive(v_t_3063_)) as u8;
                    if v_isSharedCheck_3721_ == 0 {
                        v_unused_3722_ = lean_ctor_get(v_t_3063_, 0);
                        lean_dec(v_unused_3722_);
                        v___x_3069_ = v_t_3063_;
                        v_isShared_3070_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3067_);
                        lean_inc(v_l_3066_);
                        lean_inc(v_v_3065_);
                        lean_inc(v_k_3064_);
                        lean_dec(v_t_3063_);
                        v___x_3069_ = lean_box(0);
                        v_isShared_3070_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_3063_;
                }
            }
            1 => {
                v___x_3071_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3062_, v_k_3064_);
                match v___x_3071_ {
                    0 => {
                        v_impl_3072_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_k_3062_, v_l_3066_);
                        v___x_3073_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_impl_3072_) == 0 {
                            if lean_obj_tag(v_r_3067_) == 0 {
                                v_size_3074_ = lean_ctor_get(v_impl_3072_, 0);
                                lean_inc(v_size_3074_);
                                v_size_3075_ = lean_ctor_get(v_r_3067_, 0);
                                v_k_3076_ = lean_ctor_get(v_r_3067_, 1);
                                v_v_3077_ = lean_ctor_get(v_r_3067_, 2);
                                v_l_3078_ = lean_ctor_get(v_r_3067_, 3);
                                lean_inc(v_l_3078_);
                                v_r_3079_ = lean_ctor_get(v_r_3067_, 4);
                                v___x_3080_ = lean_unsigned_to_nat(3);
                                v___x_3081_ = lean_nat_mul(v___x_3080_, v_size_3074_);
                                v___x_3082_ = lean_nat_dec_lt(v___x_3081_, v_size_3075_);
                                lean_dec(v___x_3081_);
                                if v___x_3082_ == 0 {
                                    lean_dec(v_l_3078_);
                                    v___x_3083_ = lean_nat_add(v___x_3073_, v_size_3074_);
                                    lean_dec(v_size_3074_);
                                    v___x_3084_ = lean_nat_add(v___x_3083_, v_size_3075_);
                                    lean_dec(v___x_3083_);
                                    if v_isShared_3070_ == 0 {
                                        lean_ctor_set(v___x_3069_, 3, v_impl_3072_);
                                        lean_ctor_set(v___x_3069_, 0, v___x_3084_);
                                        v___x_3086_ = v___x_3069_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
                                        lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_k_3064_);
                                        lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_v_3065_);
                                        lean_ctor_set(v_reuseFailAlloc_3087_, 3, v_impl_3072_);
                                        lean_ctor_set(v_reuseFailAlloc_3087_, 4, v_r_3067_);
                                        v___x_3086_ = v_reuseFailAlloc_3087_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_r_3079_);
                                    lean_inc(v_v_3077_);
                                    lean_inc(v_k_3076_);
                                    lean_inc(v_size_3075_);
                                    v_isSharedCheck_3151_ = (!lean_is_exclusive(v_r_3067_)) as u8;
                                    if v_isSharedCheck_3151_ == 0 {
                                        v_unused_3152_ = lean_ctor_get(v_r_3067_, 4);
                                        lean_dec(v_unused_3152_);
                                        v_unused_3153_ = lean_ctor_get(v_r_3067_, 3);
                                        lean_dec(v_unused_3153_);
                                        v_unused_3154_ = lean_ctor_get(v_r_3067_, 2);
                                        lean_dec(v_unused_3154_);
                                        v_unused_3155_ = lean_ctor_get(v_r_3067_, 1);
                                        lean_dec(v_unused_3155_);
                                        v_unused_3156_ = lean_ctor_get(v_r_3067_, 0);
                                        lean_dec(v_unused_3156_);
                                        v___x_3089_ = v_r_3067_;
                                        v_isShared_3090_ = v_isSharedCheck_3151_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v_r_3067_);
                                        v___x_3089_ = lean_box(0);
                                        v_isShared_3090_ = v_isSharedCheck_3151_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3157_ = lean_ctor_get(v_impl_3072_, 0);
                                lean_inc(v_size_3157_);
                                v___x_3158_ = lean_nat_add(v___x_3073_, v_size_3157_);
                                lean_dec(v_size_3157_);
                                if v_isShared_3070_ == 0 {
                                    lean_ctor_set(v___x_3069_, 3, v_impl_3072_);
                                    lean_ctor_set(v___x_3069_, 0, v___x_3158_);
                                    v___x_3160_ = v___x_3069_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
                                    lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_k_3064_);
                                    lean_ctor_set(v_reuseFailAlloc_3161_, 2, v_v_3065_);
                                    lean_ctor_set(v_reuseFailAlloc_3161_, 3, v_impl_3072_);
                                    lean_ctor_set(v_reuseFailAlloc_3161_, 4, v_r_3067_);
                                    v___x_3160_ = v_reuseFailAlloc_3161_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v_r_3067_) == 0 {
                                v_l_3162_ = lean_ctor_get(v_r_3067_, 3);
                                lean_inc(v_l_3162_);
                                if lean_obj_tag(v_l_3162_) == 0 {
                                    v_r_3163_ = lean_ctor_get(v_r_3067_, 4);
                                    lean_inc(v_r_3163_);
                                    if lean_obj_tag(v_r_3163_) == 0 {
                                        v_size_3164_ = lean_ctor_get(v_r_3067_, 0);
                                        v_k_3165_ = lean_ctor_get(v_r_3067_, 1);
                                        v_v_3166_ = lean_ctor_get(v_r_3067_, 2);
                                        v_isSharedCheck_3179_ =
                                            (!lean_is_exclusive(v_r_3067_)) as u8;
                                        if v_isSharedCheck_3179_ == 0 {
                                            v_unused_3180_ = lean_ctor_get(v_r_3067_, 4);
                                            lean_dec(v_unused_3180_);
                                            v_unused_3181_ = lean_ctor_get(v_r_3067_, 3);
                                            lean_dec(v_unused_3181_);
                                            v___x_3168_ = v_r_3067_;
                                            v_isShared_3169_ = v_isSharedCheck_3179_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3166_);
                                            lean_inc(v_k_3165_);
                                            lean_inc(v_size_3164_);
                                            lean_dec(v_r_3067_);
                                            v___x_3168_ = lean_box(0);
                                            v_isShared_3169_ = v_isSharedCheck_3179_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_3182_ = lean_ctor_get(v_r_3067_, 1);
                                        v_v_3183_ = lean_ctor_get(v_r_3067_, 2);
                                        v_isSharedCheck_3206_ =
                                            (!lean_is_exclusive(v_r_3067_)) as u8;
                                        if v_isSharedCheck_3206_ == 0 {
                                            v_unused_3207_ = lean_ctor_get(v_r_3067_, 4);
                                            lean_dec(v_unused_3207_);
                                            v_unused_3208_ = lean_ctor_get(v_r_3067_, 3);
                                            lean_dec(v_unused_3208_);
                                            v_unused_3209_ = lean_ctor_get(v_r_3067_, 0);
                                            lean_dec(v_unused_3209_);
                                            v___x_3185_ = v_r_3067_;
                                            v_isShared_3186_ = v_isSharedCheck_3206_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3183_);
                                            lean_inc(v_k_3182_);
                                            lean_dec(v_r_3067_);
                                            v___x_3185_ = lean_box(0);
                                            v_isShared_3186_ = v_isSharedCheck_3206_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3210_ = lean_ctor_get(v_r_3067_, 4);
                                    lean_inc(v_r_3210_);
                                    if lean_obj_tag(v_r_3210_) == 0 {
                                        v_k_3211_ = lean_ctor_get(v_r_3067_, 1);
                                        v_v_3212_ = lean_ctor_get(v_r_3067_, 2);
                                        v_isSharedCheck_3223_ =
                                            (!lean_is_exclusive(v_r_3067_)) as u8;
                                        if v_isSharedCheck_3223_ == 0 {
                                            v_unused_3224_ = lean_ctor_get(v_r_3067_, 4);
                                            lean_dec(v_unused_3224_);
                                            v_unused_3225_ = lean_ctor_get(v_r_3067_, 3);
                                            lean_dec(v_unused_3225_);
                                            v_unused_3226_ = lean_ctor_get(v_r_3067_, 0);
                                            lean_dec(v_unused_3226_);
                                            v___x_3214_ = v_r_3067_;
                                            v_isShared_3215_ = v_isSharedCheck_3223_;
                                            state = 22;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3212_);
                                            lean_inc(v_k_3211_);
                                            lean_dec(v_r_3067_);
                                            v___x_3214_ = lean_box(0);
                                            v_isShared_3215_ = v_isSharedCheck_3223_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_3227_ = lean_ctor_get(v_r_3067_, 0);
                                        v_k_3228_ = lean_ctor_get(v_r_3067_, 1);
                                        v_v_3229_ = lean_ctor_get(v_r_3067_, 2);
                                        v_isSharedCheck_3240_ =
                                            (!lean_is_exclusive(v_r_3067_)) as u8;
                                        if v_isSharedCheck_3240_ == 0 {
                                            v_unused_3241_ = lean_ctor_get(v_r_3067_, 4);
                                            lean_dec(v_unused_3241_);
                                            v_unused_3242_ = lean_ctor_get(v_r_3067_, 3);
                                            lean_dec(v_unused_3242_);
                                            v___x_3231_ = v_r_3067_;
                                            v_isShared_3232_ = v_isSharedCheck_3240_;
                                            state = 25;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3229_);
                                            lean_inc(v_k_3228_);
                                            lean_inc(v_size_3227_);
                                            lean_dec(v_r_3067_);
                                            v___x_3231_ = lean_box(0);
                                            v_isShared_3232_ = v_isSharedCheck_3240_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3070_ == 0 {
                                    lean_ctor_set(v___x_3069_, 3, v_r_3067_);
                                    lean_ctor_set(v___x_3069_, 0, v___x_3073_);
                                    v___x_3244_ = v___x_3069_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3073_);
                                    lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_k_3064_);
                                    lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_v_3065_);
                                    lean_ctor_set(v_reuseFailAlloc_3245_, 3, v_r_3067_);
                                    lean_ctor_set(v_reuseFailAlloc_3245_, 4, v_r_3067_);
                                    v___x_3244_ = v_reuseFailAlloc_3245_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        lean_del_object(v___x_3069_);
                        lean_dec(v_v_3065_);
                        lean_dec(v_k_3064_);
                        if lean_obj_tag(v_l_3066_) == 0 {
                            if lean_obj_tag(v_r_3067_) == 0 {
                                v_size_3246_ = lean_ctor_get(v_l_3066_, 0);
                                v_k_3247_ = lean_ctor_get(v_l_3066_, 1);
                                v_v_3248_ = lean_ctor_get(v_l_3066_, 2);
                                v_l_3249_ = lean_ctor_get(v_l_3066_, 3);
                                v_r_3250_ = lean_ctor_get(v_l_3066_, 4);
                                lean_inc(v_r_3250_);
                                v_size_3251_ = lean_ctor_get(v_r_3067_, 0);
                                v_k_3252_ = lean_ctor_get(v_r_3067_, 1);
                                v_v_3253_ = lean_ctor_get(v_r_3067_, 2);
                                v_l_3254_ = lean_ctor_get(v_r_3067_, 3);
                                lean_inc(v_l_3254_);
                                v_r_3255_ = lean_ctor_get(v_r_3067_, 4);
                                v___x_3256_ = lean_unsigned_to_nat(1);
                                v___x_3257_ = lean_nat_dec_lt(v_size_3246_, v_size_3251_);
                                if v___x_3257_ == 0 {
                                    lean_inc(v_l_3249_);
                                    lean_inc(v_v_3248_);
                                    lean_inc(v_k_3247_);
                                    v_isSharedCheck_3393_ = (!lean_is_exclusive(v_l_3066_)) as u8;
                                    if v_isSharedCheck_3393_ == 0 {
                                        v_unused_3394_ = lean_ctor_get(v_l_3066_, 4);
                                        lean_dec(v_unused_3394_);
                                        v_unused_3395_ = lean_ctor_get(v_l_3066_, 3);
                                        lean_dec(v_unused_3395_);
                                        v_unused_3396_ = lean_ctor_get(v_l_3066_, 2);
                                        lean_dec(v_unused_3396_);
                                        v_unused_3397_ = lean_ctor_get(v_l_3066_, 1);
                                        lean_dec(v_unused_3397_);
                                        v_unused_3398_ = lean_ctor_get(v_l_3066_, 0);
                                        lean_dec(v_unused_3398_);
                                        v___x_3259_ = v_l_3066_;
                                        v_isShared_3260_ = v_isSharedCheck_3393_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_dec(v_l_3066_);
                                        v___x_3259_ = lean_box(0);
                                        v_isShared_3260_ = v_isSharedCheck_3393_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_r_3255_);
                                    lean_inc(v_v_3253_);
                                    lean_inc(v_k_3252_);
                                    v_isSharedCheck_3551_ = (!lean_is_exclusive(v_r_3067_)) as u8;
                                    if v_isSharedCheck_3551_ == 0 {
                                        v_unused_3552_ = lean_ctor_get(v_r_3067_, 4);
                                        lean_dec(v_unused_3552_);
                                        v_unused_3553_ = lean_ctor_get(v_r_3067_, 3);
                                        lean_dec(v_unused_3553_);
                                        v_unused_3554_ = lean_ctor_get(v_r_3067_, 2);
                                        lean_dec(v_unused_3554_);
                                        v_unused_3555_ = lean_ctor_get(v_r_3067_, 1);
                                        lean_dec(v_unused_3555_);
                                        v_unused_3556_ = lean_ctor_get(v_r_3067_, 0);
                                        lean_dec(v_unused_3556_);
                                        v___x_3400_ = v_r_3067_;
                                        v_isShared_3401_ = v_isSharedCheck_3551_;
                                        state = 51;
                                        continue;
                                    } else {
                                        lean_dec(v_r_3067_);
                                        v___x_3400_ = lean_box(0);
                                        v_isShared_3401_ = v_isSharedCheck_3551_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_3066_;
                            }
                        } else {
                            return v_r_3067_;
                        }
                    }
                    _ => {
                        v_impl_3557_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_k_3062_, v_r_3067_);
                        v___x_3558_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_impl_3557_) == 0 {
                            if lean_obj_tag(v_l_3066_) == 0 {
                                v_size_3559_ = lean_ctor_get(v_impl_3557_, 0);
                                lean_inc(v_size_3559_);
                                v_size_3560_ = lean_ctor_get(v_l_3066_, 0);
                                v_k_3561_ = lean_ctor_get(v_l_3066_, 1);
                                v_v_3562_ = lean_ctor_get(v_l_3066_, 2);
                                v_l_3563_ = lean_ctor_get(v_l_3066_, 3);
                                v_r_3564_ = lean_ctor_get(v_l_3066_, 4);
                                lean_inc(v_r_3564_);
                                v___x_3565_ = lean_unsigned_to_nat(3);
                                v___x_3566_ = lean_nat_mul(v___x_3565_, v_size_3559_);
                                v___x_3567_ = lean_nat_dec_lt(v___x_3566_, v_size_3560_);
                                lean_dec(v___x_3566_);
                                if v___x_3567_ == 0 {
                                    lean_dec(v_r_3564_);
                                    v___x_3568_ = lean_nat_add(v___x_3558_, v_size_3560_);
                                    v___x_3569_ = lean_nat_add(v___x_3568_, v_size_3559_);
                                    lean_dec(v_size_3559_);
                                    lean_dec(v___x_3568_);
                                    if v_isShared_3070_ == 0 {
                                        lean_ctor_set(v___x_3069_, 4, v_impl_3557_);
                                        lean_ctor_set(v___x_3069_, 0, v___x_3569_);
                                        v___x_3571_ = v___x_3069_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
                                        lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_k_3064_);
                                        lean_ctor_set(v_reuseFailAlloc_3572_, 2, v_v_3065_);
                                        lean_ctor_set(v_reuseFailAlloc_3572_, 3, v_l_3066_);
                                        lean_ctor_set(v_reuseFailAlloc_3572_, 4, v_impl_3557_);
                                        v___x_3571_ = v_reuseFailAlloc_3572_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_l_3563_);
                                    lean_inc(v_v_3562_);
                                    lean_inc(v_k_3561_);
                                    lean_inc(v_size_3560_);
                                    v_isSharedCheck_3638_ = (!lean_is_exclusive(v_l_3066_)) as u8;
                                    if v_isSharedCheck_3638_ == 0 {
                                        v_unused_3639_ = lean_ctor_get(v_l_3066_, 4);
                                        lean_dec(v_unused_3639_);
                                        v_unused_3640_ = lean_ctor_get(v_l_3066_, 3);
                                        lean_dec(v_unused_3640_);
                                        v_unused_3641_ = lean_ctor_get(v_l_3066_, 2);
                                        lean_dec(v_unused_3641_);
                                        v_unused_3642_ = lean_ctor_get(v_l_3066_, 1);
                                        lean_dec(v_unused_3642_);
                                        v_unused_3643_ = lean_ctor_get(v_l_3066_, 0);
                                        lean_dec(v_unused_3643_);
                                        v___x_3574_ = v_l_3066_;
                                        v_isShared_3575_ = v_isSharedCheck_3638_;
                                        state = 75;
                                        continue;
                                    } else {
                                        lean_dec(v_l_3066_);
                                        v___x_3574_ = lean_box(0);
                                        v_isShared_3575_ = v_isSharedCheck_3638_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3644_ = lean_ctor_get(v_impl_3557_, 0);
                                lean_inc(v_size_3644_);
                                v___x_3645_ = lean_nat_add(v___x_3558_, v_size_3644_);
                                lean_dec(v_size_3644_);
                                if v_isShared_3070_ == 0 {
                                    lean_ctor_set(v___x_3069_, 4, v_impl_3557_);
                                    lean_ctor_set(v___x_3069_, 0, v___x_3645_);
                                    v___x_3647_ = v___x_3069_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
                                    lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_k_3064_);
                                    lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_v_3065_);
                                    lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_l_3066_);
                                    lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_impl_3557_);
                                    v___x_3647_ = v_reuseFailAlloc_3648_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v_l_3066_) == 0 {
                                v_l_3649_ = lean_ctor_get(v_l_3066_, 3);
                                if lean_obj_tag(v_l_3649_) == 0 {
                                    lean_inc_ref(v_l_3649_);
                                    v_r_3650_ = lean_ctor_get(v_l_3066_, 4);
                                    lean_inc(v_r_3650_);
                                    if lean_obj_tag(v_r_3650_) == 0 {
                                        v_size_3651_ = lean_ctor_get(v_l_3066_, 0);
                                        v_k_3652_ = lean_ctor_get(v_l_3066_, 1);
                                        v_v_3653_ = lean_ctor_get(v_l_3066_, 2);
                                        v_isSharedCheck_3666_ =
                                            (!lean_is_exclusive(v_l_3066_)) as u8;
                                        if v_isSharedCheck_3666_ == 0 {
                                            v_unused_3667_ = lean_ctor_get(v_l_3066_, 4);
                                            lean_dec(v_unused_3667_);
                                            v_unused_3668_ = lean_ctor_get(v_l_3066_, 3);
                                            lean_dec(v_unused_3668_);
                                            v___x_3655_ = v_l_3066_;
                                            v_isShared_3656_ = v_isSharedCheck_3666_;
                                            state = 86;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3653_);
                                            lean_inc(v_k_3652_);
                                            lean_inc(v_size_3651_);
                                            lean_dec(v_l_3066_);
                                            v___x_3655_ = lean_box(0);
                                            v_isShared_3656_ = v_isSharedCheck_3666_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_3669_ = lean_ctor_get(v_l_3066_, 1);
                                        v_v_3670_ = lean_ctor_get(v_l_3066_, 2);
                                        v_isSharedCheck_3681_ =
                                            (!lean_is_exclusive(v_l_3066_)) as u8;
                                        if v_isSharedCheck_3681_ == 0 {
                                            v_unused_3682_ = lean_ctor_get(v_l_3066_, 4);
                                            lean_dec(v_unused_3682_);
                                            v_unused_3683_ = lean_ctor_get(v_l_3066_, 3);
                                            lean_dec(v_unused_3683_);
                                            v_unused_3684_ = lean_ctor_get(v_l_3066_, 0);
                                            lean_dec(v_unused_3684_);
                                            v___x_3672_ = v_l_3066_;
                                            v_isShared_3673_ = v_isSharedCheck_3681_;
                                            state = 89;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3670_);
                                            lean_inc(v_k_3669_);
                                            lean_dec(v_l_3066_);
                                            v___x_3672_ = lean_box(0);
                                            v_isShared_3673_ = v_isSharedCheck_3681_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3685_ = lean_ctor_get(v_l_3066_, 4);
                                    lean_inc(v_r_3685_);
                                    if lean_obj_tag(v_r_3685_) == 0 {
                                        lean_inc(v_l_3649_);
                                        v_k_3686_ = lean_ctor_get(v_l_3066_, 1);
                                        v_v_3687_ = lean_ctor_get(v_l_3066_, 2);
                                        v_isSharedCheck_3710_ =
                                            (!lean_is_exclusive(v_l_3066_)) as u8;
                                        if v_isSharedCheck_3710_ == 0 {
                                            v_unused_3711_ = lean_ctor_get(v_l_3066_, 4);
                                            lean_dec(v_unused_3711_);
                                            v_unused_3712_ = lean_ctor_get(v_l_3066_, 3);
                                            lean_dec(v_unused_3712_);
                                            v_unused_3713_ = lean_ctor_get(v_l_3066_, 0);
                                            lean_dec(v_unused_3713_);
                                            v___x_3689_ = v_l_3066_;
                                            v_isShared_3690_ = v_isSharedCheck_3710_;
                                            state = 92;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3687_);
                                            lean_inc(v_k_3686_);
                                            lean_dec(v_l_3066_);
                                            v___x_3689_ = lean_box(0);
                                            v_isShared_3690_ = v_isSharedCheck_3710_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_3714_ = lean_unsigned_to_nat(2);
                                        if v_isShared_3070_ == 0 {
                                            lean_ctor_set(v___x_3069_, 4, v_r_3685_);
                                            lean_ctor_set(v___x_3069_, 0, v___x_3714_);
                                            v___x_3716_ = v___x_3069_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3717_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
                                            lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_k_3064_);
                                            lean_ctor_set(v_reuseFailAlloc_3717_, 2, v_v_3065_);
                                            lean_ctor_set(v_reuseFailAlloc_3717_, 3, v_l_3066_);
                                            lean_ctor_set(v_reuseFailAlloc_3717_, 4, v_r_3685_);
                                            v___x_3716_ = v_reuseFailAlloc_3717_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3070_ == 0 {
                                    lean_ctor_set(v___x_3069_, 4, v_l_3066_);
                                    lean_ctor_set(v___x_3069_, 0, v___x_3558_);
                                    v___x_3719_ = v___x_3069_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3558_);
                                    lean_ctor_set(v_reuseFailAlloc_3720_, 1, v_k_3064_);
                                    lean_ctor_set(v_reuseFailAlloc_3720_, 2, v_v_3065_);
                                    lean_ctor_set(v_reuseFailAlloc_3720_, 3, v_l_3066_);
                                    lean_ctor_set(v_reuseFailAlloc_3720_, 4, v_l_3066_);
                                    v___x_3719_ = v_reuseFailAlloc_3720_;
                                    state = 98;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3086_;
            }
            3 => {
                v_size_3091_ = lean_ctor_get(v_l_3078_, 0);
                v_k_3092_ = lean_ctor_get(v_l_3078_, 1);
                v_v_3093_ = lean_ctor_get(v_l_3078_, 2);
                v_l_3094_ = lean_ctor_get(v_l_3078_, 3);
                v_r_3095_ = lean_ctor_get(v_l_3078_, 4);
                v_size_3096_ = lean_ctor_get(v_r_3079_, 0);
                v___x_3097_ = lean_unsigned_to_nat(2);
                v___x_3098_ = lean_nat_mul(v___x_3097_, v_size_3096_);
                v___x_3099_ = lean_nat_dec_lt(v_size_3091_, v___x_3098_);
                lean_dec(v___x_3098_);
                if v___x_3099_ == 0 {
                    lean_inc(v_r_3095_);
                    lean_inc(v_l_3094_);
                    lean_inc(v_v_3093_);
                    lean_inc(v_k_3092_);
                    v_isSharedCheck_3127_ = (!lean_is_exclusive(v_l_3078_)) as u8;
                    if v_isSharedCheck_3127_ == 0 {
                        v_unused_3128_ = lean_ctor_get(v_l_3078_, 4);
                        lean_dec(v_unused_3128_);
                        v_unused_3129_ = lean_ctor_get(v_l_3078_, 3);
                        lean_dec(v_unused_3129_);
                        v_unused_3130_ = lean_ctor_get(v_l_3078_, 2);
                        lean_dec(v_unused_3130_);
                        v_unused_3131_ = lean_ctor_get(v_l_3078_, 1);
                        lean_dec(v_unused_3131_);
                        v_unused_3132_ = lean_ctor_get(v_l_3078_, 0);
                        lean_dec(v_unused_3132_);
                        v___x_3101_ = v_l_3078_;
                        v_isShared_3102_ = v_isSharedCheck_3127_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_3078_);
                        v___x_3101_ = lean_box(0);
                        v_isShared_3102_ = v_isSharedCheck_3127_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3069_);
                    v___x_3133_ = lean_nat_add(v___x_3073_, v_size_3074_);
                    lean_dec(v_size_3074_);
                    v___x_3134_ = lean_nat_add(v___x_3133_, v_size_3075_);
                    lean_dec(v_size_3075_);
                    v___x_3135_ = lean_nat_add(v___x_3133_, v_size_3091_);
                    lean_dec(v___x_3133_);
                    lean_inc_ref(v_impl_3072_);
                    if v_isShared_3090_ == 0 {
                        lean_ctor_set(v___x_3089_, 4, v_l_3078_);
                        lean_ctor_set(v___x_3089_, 3, v_impl_3072_);
                        lean_ctor_set(v___x_3089_, 2, v_v_3065_);
                        lean_ctor_set(v___x_3089_, 1, v_k_3064_);
                        lean_ctor_set(v___x_3089_, 0, v___x_3135_);
                        v___x_3137_ = v___x_3089_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3135_);
                        lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_k_3064_);
                        lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_v_3065_);
                        lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_impl_3072_);
                        lean_ctor_set(v_reuseFailAlloc_3150_, 4, v_l_3078_);
                        v___x_3137_ = v_reuseFailAlloc_3150_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3103_ = lean_nat_add(v___x_3073_, v_size_3074_);
                lean_dec(v_size_3074_);
                v___x_3104_ = lean_nat_add(v___x_3103_, v_size_3075_);
                lean_dec(v_size_3075_);
                if lean_obj_tag(v_l_3094_) == 0 {
                    v_size_3125_ = lean_ctor_get(v_l_3094_, 0);
                    lean_inc(v_size_3125_);
                    v___y_3117_ = v_size_3125_;
                    state = 8;
                    continue;
                } else {
                    v___x_3126_ = lean_unsigned_to_nat(0);
                    v___y_3117_ = v___x_3126_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3109_ = lean_nat_add(v___y_3107_, v___y_3108_);
                lean_dec(v___y_3108_);
                lean_dec(v___y_3107_);
                if v_isShared_3102_ == 0 {
                    lean_ctor_set(v___x_3101_, 4, v_r_3079_);
                    lean_ctor_set(v___x_3101_, 3, v_r_3095_);
                    lean_ctor_set(v___x_3101_, 2, v_v_3077_);
                    lean_ctor_set(v___x_3101_, 1, v_k_3076_);
                    lean_ctor_set(v___x_3101_, 0, v___x_3109_);
                    v___x_3111_ = v___x_3101_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3109_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_k_3076_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_v_3077_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 3, v_r_3095_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_r_3079_);
                    v___x_3111_ = v_reuseFailAlloc_3115_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3090_ == 0 {
                    lean_ctor_set(v___x_3089_, 4, v___x_3111_);
                    lean_ctor_set(v___x_3089_, 3, v___y_3106_);
                    lean_ctor_set(v___x_3089_, 2, v_v_3093_);
                    lean_ctor_set(v___x_3089_, 1, v_k_3092_);
                    lean_ctor_set(v___x_3089_, 0, v___x_3104_);
                    v___x_3113_ = v___x_3089_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3104_);
                    lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_3092_);
                    lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_3093_);
                    lean_ctor_set(v_reuseFailAlloc_3114_, 3, v___y_3106_);
                    lean_ctor_set(v_reuseFailAlloc_3114_, 4, v___x_3111_);
                    v___x_3113_ = v_reuseFailAlloc_3114_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3113_;
            }
            8 => {
                v___x_3118_ = lean_nat_add(v___x_3103_, v___y_3117_);
                lean_dec(v___y_3117_);
                lean_dec(v___x_3103_);
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v_l_3094_);
                    lean_ctor_set(v___x_3069_, 3, v_impl_3072_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3118_);
                    v___x_3120_ = v___x_3069_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3118_);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 3, v_impl_3072_);
                    lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_l_3094_);
                    v___x_3120_ = v_reuseFailAlloc_3124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3121_ = lean_nat_add(v___x_3073_, v_size_3096_);
                if lean_obj_tag(v_r_3095_) == 0 {
                    v_size_3122_ = lean_ctor_get(v_r_3095_, 0);
                    lean_inc(v_size_3122_);
                    v___y_3106_ = v___x_3120_;
                    v___y_3107_ = v___x_3121_;
                    v___y_3108_ = v_size_3122_;
                    state = 5;
                    continue;
                } else {
                    v___x_3123_ = lean_unsigned_to_nat(0);
                    v___y_3106_ = v___x_3120_;
                    v___y_3107_ = v___x_3121_;
                    v___y_3108_ = v___x_3123_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3144_ = (!lean_is_exclusive(v_impl_3072_)) as u8;
                if v_isSharedCheck_3144_ == 0 {
                    v_unused_3145_ = lean_ctor_get(v_impl_3072_, 4);
                    lean_dec(v_unused_3145_);
                    v_unused_3146_ = lean_ctor_get(v_impl_3072_, 3);
                    lean_dec(v_unused_3146_);
                    v_unused_3147_ = lean_ctor_get(v_impl_3072_, 2);
                    lean_dec(v_unused_3147_);
                    v_unused_3148_ = lean_ctor_get(v_impl_3072_, 1);
                    lean_dec(v_unused_3148_);
                    v_unused_3149_ = lean_ctor_get(v_impl_3072_, 0);
                    lean_dec(v_unused_3149_);
                    v___x_3139_ = v_impl_3072_;
                    v_isShared_3140_ = v_isSharedCheck_3144_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_impl_3072_);
                    v___x_3139_ = lean_box(0);
                    v_isShared_3140_ = v_isSharedCheck_3144_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3140_ == 0 {
                    lean_ctor_set(v___x_3139_, 4, v_r_3079_);
                    lean_ctor_set(v___x_3139_, 3, v___x_3137_);
                    lean_ctor_set(v___x_3139_, 2, v_v_3077_);
                    lean_ctor_set(v___x_3139_, 1, v_k_3076_);
                    lean_ctor_set(v___x_3139_, 0, v___x_3134_);
                    v___x_3142_ = v___x_3139_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3134_);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_k_3076_);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_v_3077_);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 3, v___x_3137_);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_r_3079_);
                    v___x_3142_ = v_reuseFailAlloc_3143_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3142_;
            }
            13 => {
                return v___x_3160_;
            }
            14 => {
                v_size_3170_ = lean_ctor_get(v_l_3162_, 0);
                v___x_3171_ = lean_nat_add(v___x_3073_, v_size_3164_);
                lean_dec(v_size_3164_);
                v___x_3172_ = lean_nat_add(v___x_3073_, v_size_3170_);
                if v_isShared_3169_ == 0 {
                    lean_ctor_set(v___x_3168_, 4, v_l_3162_);
                    lean_ctor_set(v___x_3168_, 3, v_impl_3072_);
                    lean_ctor_set(v___x_3168_, 2, v_v_3065_);
                    lean_ctor_set(v___x_3168_, 1, v_k_3064_);
                    lean_ctor_set(v___x_3168_, 0, v___x_3172_);
                    v___x_3174_ = v___x_3168_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3172_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 3, v_impl_3072_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 4, v_l_3162_);
                    v___x_3174_ = v_reuseFailAlloc_3178_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v_r_3163_);
                    lean_ctor_set(v___x_3069_, 3, v___x_3174_);
                    lean_ctor_set(v___x_3069_, 2, v_v_3166_);
                    lean_ctor_set(v___x_3069_, 1, v_k_3165_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3171_);
                    v___x_3176_ = v___x_3069_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_k_3165_);
                    lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_v_3166_);
                    lean_ctor_set(v_reuseFailAlloc_3177_, 3, v___x_3174_);
                    lean_ctor_set(v_reuseFailAlloc_3177_, 4, v_r_3163_);
                    v___x_3176_ = v_reuseFailAlloc_3177_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3176_;
            }
            17 => {
                v_k_3187_ = lean_ctor_get(v_l_3162_, 1);
                v_v_3188_ = lean_ctor_get(v_l_3162_, 2);
                v_isSharedCheck_3202_ = (!lean_is_exclusive(v_l_3162_)) as u8;
                if v_isSharedCheck_3202_ == 0 {
                    v_unused_3203_ = lean_ctor_get(v_l_3162_, 4);
                    lean_dec(v_unused_3203_);
                    v_unused_3204_ = lean_ctor_get(v_l_3162_, 3);
                    lean_dec(v_unused_3204_);
                    v_unused_3205_ = lean_ctor_get(v_l_3162_, 0);
                    lean_dec(v_unused_3205_);
                    v___x_3190_ = v_l_3162_;
                    v_isShared_3191_ = v_isSharedCheck_3202_;
                    state = 18;
                    continue;
                } else {
                    lean_inc(v_v_3188_);
                    lean_inc(v_k_3187_);
                    lean_dec(v_l_3162_);
                    v___x_3190_ = lean_box(0);
                    v_isShared_3191_ = v_isSharedCheck_3202_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3192_ = lean_unsigned_to_nat(3);
                if v_isShared_3191_ == 0 {
                    lean_ctor_set(v___x_3190_, 4, v_r_3163_);
                    lean_ctor_set(v___x_3190_, 3, v_r_3163_);
                    lean_ctor_set(v___x_3190_, 2, v_v_3065_);
                    lean_ctor_set(v___x_3190_, 1, v_k_3064_);
                    lean_ctor_set(v___x_3190_, 0, v___x_3073_);
                    v___x_3194_ = v___x_3190_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3073_);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 3, v_r_3163_);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 4, v_r_3163_);
                    v___x_3194_ = v_reuseFailAlloc_3201_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3186_ == 0 {
                    lean_ctor_set(v___x_3185_, 3, v_r_3163_);
                    lean_ctor_set(v___x_3185_, 0, v___x_3073_);
                    v___x_3196_ = v___x_3185_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3073_);
                    lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_k_3182_);
                    lean_ctor_set(v_reuseFailAlloc_3200_, 2, v_v_3183_);
                    lean_ctor_set(v_reuseFailAlloc_3200_, 3, v_r_3163_);
                    lean_ctor_set(v_reuseFailAlloc_3200_, 4, v_r_3163_);
                    v___x_3196_ = v_reuseFailAlloc_3200_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v___x_3196_);
                    lean_ctor_set(v___x_3069_, 3, v___x_3194_);
                    lean_ctor_set(v___x_3069_, 2, v_v_3188_);
                    lean_ctor_set(v___x_3069_, 1, v_k_3187_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3192_);
                    v___x_3198_ = v___x_3069_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3192_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_k_3187_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_v_3188_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 3, v___x_3194_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 4, v___x_3196_);
                    v___x_3198_ = v_reuseFailAlloc_3199_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3198_;
            }
            22 => {
                v___x_3216_ = lean_unsigned_to_nat(3);
                if v_isShared_3215_ == 0 {
                    lean_ctor_set(v___x_3214_, 4, v_l_3162_);
                    lean_ctor_set(v___x_3214_, 2, v_v_3065_);
                    lean_ctor_set(v___x_3214_, 1, v_k_3064_);
                    lean_ctor_set(v___x_3214_, 0, v___x_3073_);
                    v___x_3218_ = v___x_3214_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3073_);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 3, v_l_3162_);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 4, v_l_3162_);
                    v___x_3218_ = v_reuseFailAlloc_3222_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v_r_3210_);
                    lean_ctor_set(v___x_3069_, 3, v___x_3218_);
                    lean_ctor_set(v___x_3069_, 2, v_v_3212_);
                    lean_ctor_set(v___x_3069_, 1, v_k_3211_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3216_);
                    v___x_3220_ = v___x_3069_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3216_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_k_3211_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_v_3212_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 3, v___x_3218_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_r_3210_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3220_;
            }
            25 => {
                if v_isShared_3232_ == 0 {
                    lean_ctor_set(v___x_3231_, 3, v_r_3210_);
                    v___x_3234_ = v___x_3231_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_size_3227_);
                    lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_k_3228_);
                    lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_v_3229_);
                    lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_r_3210_);
                    lean_ctor_set(v_reuseFailAlloc_3239_, 4, v_r_3210_);
                    v___x_3234_ = v_reuseFailAlloc_3239_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_3235_ = lean_unsigned_to_nat(2);
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v___x_3234_);
                    lean_ctor_set(v___x_3069_, 3, v_r_3210_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3235_);
                    v___x_3237_ = v___x_3069_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
                    lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3238_, 3, v_r_3210_);
                    lean_ctor_set(v_reuseFailAlloc_3238_, 4, v___x_3234_);
                    v___x_3237_ = v_reuseFailAlloc_3238_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3237_;
            }
            28 => {
                return v___x_3244_;
            }
            29 => {
                v___x_3261_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_3247_, v_v_3248_, v_l_3249_, v_r_3250_,
                );
                v_tree_3262_ = lean_ctor_get(v___x_3261_, 2);
                lean_inc(v_tree_3262_);
                if lean_obj_tag(v_tree_3262_) == 0 {
                    v_k_3263_ = lean_ctor_get(v___x_3261_, 0);
                    lean_inc(v_k_3263_);
                    v_v_3264_ = lean_ctor_get(v___x_3261_, 1);
                    lean_inc(v_v_3264_);
                    lean_dec_ref(v___x_3261_);
                    v_size_3265_ = lean_ctor_get(v_tree_3262_, 0);
                    v___x_3266_ = lean_unsigned_to_nat(3);
                    v___x_3267_ = lean_nat_mul(v___x_3266_, v_size_3265_);
                    v___x_3268_ = lean_nat_dec_lt(v___x_3267_, v_size_3251_);
                    lean_dec(v___x_3267_);
                    if v___x_3268_ == 0 {
                        lean_dec(v_l_3254_);
                        v___x_3269_ = lean_nat_add(v___x_3256_, v_size_3265_);
                        v___x_3270_ = lean_nat_add(v___x_3269_, v_size_3251_);
                        lean_dec(v___x_3269_);
                        if v_isShared_3260_ == 0 {
                            lean_ctor_set(v___x_3259_, 4, v_r_3067_);
                            lean_ctor_set(v___x_3259_, 3, v_tree_3262_);
                            lean_ctor_set(v___x_3259_, 2, v_v_3264_);
                            lean_ctor_set(v___x_3259_, 1, v_k_3263_);
                            lean_ctor_set(v___x_3259_, 0, v___x_3270_);
                            v___x_3272_ = v___x_3259_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
                            lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_k_3263_);
                            lean_ctor_set(v_reuseFailAlloc_3273_, 2, v_v_3264_);
                            lean_ctor_set(v_reuseFailAlloc_3273_, 3, v_tree_3262_);
                            lean_ctor_set(v_reuseFailAlloc_3273_, 4, v_r_3067_);
                            v___x_3272_ = v_reuseFailAlloc_3273_;
                            state = 30;
                            continue;
                        }
                    } else {
                        lean_inc(v_r_3255_);
                        lean_inc(v_v_3253_);
                        lean_inc(v_k_3252_);
                        lean_inc(v_size_3251_);
                        v_isSharedCheck_3328_ = (!lean_is_exclusive(v_r_3067_)) as u8;
                        if v_isSharedCheck_3328_ == 0 {
                            v_unused_3329_ = lean_ctor_get(v_r_3067_, 4);
                            lean_dec(v_unused_3329_);
                            v_unused_3330_ = lean_ctor_get(v_r_3067_, 3);
                            lean_dec(v_unused_3330_);
                            v_unused_3331_ = lean_ctor_get(v_r_3067_, 2);
                            lean_dec(v_unused_3331_);
                            v_unused_3332_ = lean_ctor_get(v_r_3067_, 1);
                            lean_dec(v_unused_3332_);
                            v_unused_3333_ = lean_ctor_get(v_r_3067_, 0);
                            lean_dec(v_unused_3333_);
                            v___x_3275_ = v_r_3067_;
                            v_isShared_3276_ = v_isSharedCheck_3328_;
                            state = 31;
                            continue;
                        } else {
                            lean_dec(v_r_3067_);
                            v___x_3275_ = lean_box(0);
                            v_isShared_3276_ = v_isSharedCheck_3328_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_r_3255_);
                    lean_inc(v_v_3253_);
                    lean_inc(v_k_3252_);
                    lean_inc(v_size_3251_);
                    v_isSharedCheck_3387_ = (!lean_is_exclusive(v_r_3067_)) as u8;
                    if v_isSharedCheck_3387_ == 0 {
                        v_unused_3388_ = lean_ctor_get(v_r_3067_, 4);
                        lean_dec(v_unused_3388_);
                        v_unused_3389_ = lean_ctor_get(v_r_3067_, 3);
                        lean_dec(v_unused_3389_);
                        v_unused_3390_ = lean_ctor_get(v_r_3067_, 2);
                        lean_dec(v_unused_3390_);
                        v_unused_3391_ = lean_ctor_get(v_r_3067_, 1);
                        lean_dec(v_unused_3391_);
                        v_unused_3392_ = lean_ctor_get(v_r_3067_, 0);
                        lean_dec(v_unused_3392_);
                        v___x_3335_ = v_r_3067_;
                        v_isShared_3336_ = v_isSharedCheck_3387_;
                        state = 40;
                        continue;
                    } else {
                        lean_dec(v_r_3067_);
                        v___x_3335_ = lean_box(0);
                        v_isShared_3336_ = v_isSharedCheck_3387_;
                        state = 40;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_3272_;
            }
            31 => {
                v_size_3277_ = lean_ctor_get(v_l_3254_, 0);
                v_k_3278_ = lean_ctor_get(v_l_3254_, 1);
                v_v_3279_ = lean_ctor_get(v_l_3254_, 2);
                v_l_3280_ = lean_ctor_get(v_l_3254_, 3);
                v_r_3281_ = lean_ctor_get(v_l_3254_, 4);
                v_size_3282_ = lean_ctor_get(v_r_3255_, 0);
                v___x_3283_ = lean_unsigned_to_nat(2);
                v___x_3284_ = lean_nat_mul(v___x_3283_, v_size_3282_);
                v___x_3285_ = lean_nat_dec_lt(v_size_3277_, v___x_3284_);
                lean_dec(v___x_3284_);
                if v___x_3285_ == 0 {
                    lean_inc(v_r_3281_);
                    lean_inc(v_l_3280_);
                    lean_inc(v_v_3279_);
                    lean_inc(v_k_3278_);
                    v_isSharedCheck_3313_ = (!lean_is_exclusive(v_l_3254_)) as u8;
                    if v_isSharedCheck_3313_ == 0 {
                        v_unused_3314_ = lean_ctor_get(v_l_3254_, 4);
                        lean_dec(v_unused_3314_);
                        v_unused_3315_ = lean_ctor_get(v_l_3254_, 3);
                        lean_dec(v_unused_3315_);
                        v_unused_3316_ = lean_ctor_get(v_l_3254_, 2);
                        lean_dec(v_unused_3316_);
                        v_unused_3317_ = lean_ctor_get(v_l_3254_, 1);
                        lean_dec(v_unused_3317_);
                        v_unused_3318_ = lean_ctor_get(v_l_3254_, 0);
                        lean_dec(v_unused_3318_);
                        v___x_3287_ = v_l_3254_;
                        v_isShared_3288_ = v_isSharedCheck_3313_;
                        state = 32;
                        continue;
                    } else {
                        lean_dec(v_l_3254_);
                        v___x_3287_ = lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3313_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_3319_ = lean_nat_add(v___x_3256_, v_size_3265_);
                    v___x_3320_ = lean_nat_add(v___x_3319_, v_size_3251_);
                    lean_dec(v_size_3251_);
                    v___x_3321_ = lean_nat_add(v___x_3319_, v_size_3277_);
                    lean_dec(v___x_3319_);
                    if v_isShared_3276_ == 0 {
                        lean_ctor_set(v___x_3275_, 4, v_l_3254_);
                        lean_ctor_set(v___x_3275_, 3, v_tree_3262_);
                        lean_ctor_set(v___x_3275_, 2, v_v_3264_);
                        lean_ctor_set(v___x_3275_, 1, v_k_3263_);
                        lean_ctor_set(v___x_3275_, 0, v___x_3321_);
                        v___x_3323_ = v___x_3275_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3321_);
                        lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_k_3263_);
                        lean_ctor_set(v_reuseFailAlloc_3327_, 2, v_v_3264_);
                        lean_ctor_set(v_reuseFailAlloc_3327_, 3, v_tree_3262_);
                        lean_ctor_set(v_reuseFailAlloc_3327_, 4, v_l_3254_);
                        v___x_3323_ = v_reuseFailAlloc_3327_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_3289_ = lean_nat_add(v___x_3256_, v_size_3265_);
                v___x_3290_ = lean_nat_add(v___x_3289_, v_size_3251_);
                lean_dec(v_size_3251_);
                if lean_obj_tag(v_l_3280_) == 0 {
                    v_size_3311_ = lean_ctor_get(v_l_3280_, 0);
                    lean_inc(v_size_3311_);
                    v___y_3303_ = v_size_3311_;
                    state = 36;
                    continue;
                } else {
                    v___x_3312_ = lean_unsigned_to_nat(0);
                    v___y_3303_ = v___x_3312_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_3295_ = lean_nat_add(v___y_3292_, v___y_3294_);
                lean_dec(v___y_3294_);
                lean_dec(v___y_3292_);
                if v_isShared_3288_ == 0 {
                    lean_ctor_set(v___x_3287_, 4, v_r_3255_);
                    lean_ctor_set(v___x_3287_, 3, v_r_3281_);
                    lean_ctor_set(v___x_3287_, 2, v_v_3253_);
                    lean_ctor_set(v___x_3287_, 1, v_k_3252_);
                    lean_ctor_set(v___x_3287_, 0, v___x_3295_);
                    v___x_3297_ = v___x_3287_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3295_);
                    lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_k_3252_);
                    lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_v_3253_);
                    lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_r_3281_);
                    lean_ctor_set(v_reuseFailAlloc_3301_, 4, v_r_3255_);
                    v___x_3297_ = v_reuseFailAlloc_3301_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_3276_ == 0 {
                    lean_ctor_set(v___x_3275_, 4, v___x_3297_);
                    lean_ctor_set(v___x_3275_, 3, v___y_3293_);
                    lean_ctor_set(v___x_3275_, 2, v_v_3279_);
                    lean_ctor_set(v___x_3275_, 1, v_k_3278_);
                    lean_ctor_set(v___x_3275_, 0, v___x_3290_);
                    v___x_3299_ = v___x_3275_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3290_);
                    lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3278_);
                    lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3279_);
                    lean_ctor_set(v_reuseFailAlloc_3300_, 3, v___y_3293_);
                    lean_ctor_set(v_reuseFailAlloc_3300_, 4, v___x_3297_);
                    v___x_3299_ = v_reuseFailAlloc_3300_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3299_;
            }
            36 => {
                v___x_3304_ = lean_nat_add(v___x_3289_, v___y_3303_);
                lean_dec(v___y_3303_);
                lean_dec(v___x_3289_);
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 4, v_l_3280_);
                    lean_ctor_set(v___x_3259_, 3, v_tree_3262_);
                    lean_ctor_set(v___x_3259_, 2, v_v_3264_);
                    lean_ctor_set(v___x_3259_, 1, v_k_3263_);
                    lean_ctor_set(v___x_3259_, 0, v___x_3304_);
                    v___x_3306_ = v___x_3259_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3304_);
                    lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_k_3263_);
                    lean_ctor_set(v_reuseFailAlloc_3310_, 2, v_v_3264_);
                    lean_ctor_set(v_reuseFailAlloc_3310_, 3, v_tree_3262_);
                    lean_ctor_set(v_reuseFailAlloc_3310_, 4, v_l_3280_);
                    v___x_3306_ = v_reuseFailAlloc_3310_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_3307_ = lean_nat_add(v___x_3256_, v_size_3282_);
                if lean_obj_tag(v_r_3281_) == 0 {
                    v_size_3308_ = lean_ctor_get(v_r_3281_, 0);
                    lean_inc(v_size_3308_);
                    v___y_3292_ = v___x_3307_;
                    v___y_3293_ = v___x_3306_;
                    v___y_3294_ = v_size_3308_;
                    state = 33;
                    continue;
                } else {
                    v___x_3309_ = lean_unsigned_to_nat(0);
                    v___y_3292_ = v___x_3307_;
                    v___y_3293_ = v___x_3306_;
                    v___y_3294_ = v___x_3309_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 4, v_r_3255_);
                    lean_ctor_set(v___x_3259_, 3, v___x_3323_);
                    lean_ctor_set(v___x_3259_, 2, v_v_3253_);
                    lean_ctor_set(v___x_3259_, 1, v_k_3252_);
                    lean_ctor_set(v___x_3259_, 0, v___x_3320_);
                    v___x_3325_ = v___x_3259_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3320_);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_k_3252_);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 2, v_v_3253_);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 3, v___x_3323_);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 4, v_r_3255_);
                    v___x_3325_ = v_reuseFailAlloc_3326_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3325_;
            }
            40 => {
                if lean_obj_tag(v_l_3254_) == 0 {
                    if lean_obj_tag(v_r_3255_) == 0 {
                        v_k_3337_ = lean_ctor_get(v___x_3261_, 0);
                        lean_inc(v_k_3337_);
                        v_v_3338_ = lean_ctor_get(v___x_3261_, 1);
                        lean_inc(v_v_3338_);
                        lean_dec_ref(v___x_3261_);
                        v_size_3339_ = lean_ctor_get(v_l_3254_, 0);
                        v___x_3340_ = lean_nat_add(v___x_3256_, v_size_3251_);
                        lean_dec(v_size_3251_);
                        v___x_3341_ = lean_nat_add(v___x_3256_, v_size_3339_);
                        if v_isShared_3336_ == 0 {
                            lean_ctor_set(v___x_3335_, 4, v_l_3254_);
                            lean_ctor_set(v___x_3335_, 3, v_tree_3262_);
                            lean_ctor_set(v___x_3335_, 2, v_v_3338_);
                            lean_ctor_set(v___x_3335_, 1, v_k_3337_);
                            lean_ctor_set(v___x_3335_, 0, v___x_3341_);
                            v___x_3343_ = v___x_3335_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3341_);
                            lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_k_3337_);
                            lean_ctor_set(v_reuseFailAlloc_3347_, 2, v_v_3338_);
                            lean_ctor_set(v_reuseFailAlloc_3347_, 3, v_tree_3262_);
                            lean_ctor_set(v_reuseFailAlloc_3347_, 4, v_l_3254_);
                            v___x_3343_ = v_reuseFailAlloc_3347_;
                            state = 41;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_3251_);
                        v_k_3348_ = lean_ctor_get(v___x_3261_, 0);
                        lean_inc(v_k_3348_);
                        v_v_3349_ = lean_ctor_get(v___x_3261_, 1);
                        lean_inc(v_v_3349_);
                        lean_dec_ref(v___x_3261_);
                        v_k_3350_ = lean_ctor_get(v_l_3254_, 1);
                        v_v_3351_ = lean_ctor_get(v_l_3254_, 2);
                        v_isSharedCheck_3365_ = (!lean_is_exclusive(v_l_3254_)) as u8;
                        if v_isSharedCheck_3365_ == 0 {
                            v_unused_3366_ = lean_ctor_get(v_l_3254_, 4);
                            lean_dec(v_unused_3366_);
                            v_unused_3367_ = lean_ctor_get(v_l_3254_, 3);
                            lean_dec(v_unused_3367_);
                            v_unused_3368_ = lean_ctor_get(v_l_3254_, 0);
                            lean_dec(v_unused_3368_);
                            v___x_3353_ = v_l_3254_;
                            v_isShared_3354_ = v_isSharedCheck_3365_;
                            state = 43;
                            continue;
                        } else {
                            lean_inc(v_v_3351_);
                            lean_inc(v_k_3350_);
                            lean_dec(v_l_3254_);
                            v___x_3353_ = lean_box(0);
                            v_isShared_3354_ = v_isSharedCheck_3365_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_r_3255_) == 0 {
                        lean_dec(v_size_3251_);
                        v_k_3369_ = lean_ctor_get(v___x_3261_, 0);
                        lean_inc(v_k_3369_);
                        v_v_3370_ = lean_ctor_get(v___x_3261_, 1);
                        lean_inc(v_v_3370_);
                        lean_dec_ref(v___x_3261_);
                        v___x_3371_ = lean_unsigned_to_nat(3);
                        if v_isShared_3336_ == 0 {
                            lean_ctor_set(v___x_3335_, 4, v_l_3254_);
                            lean_ctor_set(v___x_3335_, 2, v_v_3370_);
                            lean_ctor_set(v___x_3335_, 1, v_k_3369_);
                            lean_ctor_set(v___x_3335_, 0, v___x_3256_);
                            v___x_3373_ = v___x_3335_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3256_);
                            lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_k_3369_);
                            lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_v_3370_);
                            lean_ctor_set(v_reuseFailAlloc_3377_, 3, v_l_3254_);
                            lean_ctor_set(v_reuseFailAlloc_3377_, 4, v_l_3254_);
                            v___x_3373_ = v_reuseFailAlloc_3377_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_3378_ = lean_ctor_get(v___x_3261_, 0);
                        lean_inc(v_k_3378_);
                        v_v_3379_ = lean_ctor_get(v___x_3261_, 1);
                        lean_inc(v_v_3379_);
                        lean_dec_ref(v___x_3261_);
                        if v_isShared_3336_ == 0 {
                            lean_ctor_set(v___x_3335_, 3, v_r_3255_);
                            v___x_3381_ = v___x_3335_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_size_3251_);
                            lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_k_3252_);
                            lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_v_3253_);
                            lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_r_3255_);
                            lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_r_3255_);
                            v___x_3381_ = v_reuseFailAlloc_3386_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 4, v_r_3255_);
                    lean_ctor_set(v___x_3259_, 3, v___x_3343_);
                    lean_ctor_set(v___x_3259_, 2, v_v_3253_);
                    lean_ctor_set(v___x_3259_, 1, v_k_3252_);
                    lean_ctor_set(v___x_3259_, 0, v___x_3340_);
                    v___x_3345_ = v___x_3259_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3340_);
                    lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_k_3252_);
                    lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_v_3253_);
                    lean_ctor_set(v_reuseFailAlloc_3346_, 3, v___x_3343_);
                    lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_r_3255_);
                    v___x_3345_ = v_reuseFailAlloc_3346_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3345_;
            }
            43 => {
                v___x_3355_ = lean_unsigned_to_nat(3);
                if v_isShared_3354_ == 0 {
                    lean_ctor_set(v___x_3353_, 4, v_r_3255_);
                    lean_ctor_set(v___x_3353_, 3, v_r_3255_);
                    lean_ctor_set(v___x_3353_, 2, v_v_3349_);
                    lean_ctor_set(v___x_3353_, 1, v_k_3348_);
                    lean_ctor_set(v___x_3353_, 0, v___x_3256_);
                    v___x_3357_ = v___x_3353_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3256_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_k_3348_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_v_3349_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_r_3255_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_r_3255_);
                    v___x_3357_ = v_reuseFailAlloc_3364_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 3, v_r_3255_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3256_);
                    v___x_3359_ = v___x_3335_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3256_);
                    lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3252_);
                    lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3253_);
                    lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_r_3255_);
                    lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_r_3255_);
                    v___x_3359_ = v_reuseFailAlloc_3363_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 4, v___x_3359_);
                    lean_ctor_set(v___x_3259_, 3, v___x_3357_);
                    lean_ctor_set(v___x_3259_, 2, v_v_3351_);
                    lean_ctor_set(v___x_3259_, 1, v_k_3350_);
                    lean_ctor_set(v___x_3259_, 0, v___x_3355_);
                    v___x_3361_ = v___x_3259_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3355_);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_k_3350_);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 2, v_v_3351_);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 3, v___x_3357_);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 4, v___x_3359_);
                    v___x_3361_ = v_reuseFailAlloc_3362_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3361_;
            }
            47 => {
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 4, v_r_3255_);
                    lean_ctor_set(v___x_3259_, 3, v___x_3373_);
                    lean_ctor_set(v___x_3259_, 2, v_v_3253_);
                    lean_ctor_set(v___x_3259_, 1, v_k_3252_);
                    lean_ctor_set(v___x_3259_, 0, v___x_3371_);
                    v___x_3375_ = v___x_3259_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3371_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_k_3252_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_v_3253_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 3, v___x_3373_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 4, v_r_3255_);
                    v___x_3375_ = v_reuseFailAlloc_3376_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_3375_;
            }
            49 => {
                v___x_3382_ = lean_unsigned_to_nat(2);
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 4, v___x_3381_);
                    lean_ctor_set(v___x_3259_, 3, v_r_3255_);
                    lean_ctor_set(v___x_3259_, 2, v_v_3379_);
                    lean_ctor_set(v___x_3259_, 1, v_k_3378_);
                    lean_ctor_set(v___x_3259_, 0, v___x_3382_);
                    v___x_3384_ = v___x_3259_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_k_3378_);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_v_3379_);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_r_3255_);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 4, v___x_3381_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_3384_;
            }
            51 => {
                v___x_3402_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_3252_, v_v_3253_, v_l_3254_, v_r_3255_,
                );
                v_tree_3403_ = lean_ctor_get(v___x_3402_, 2);
                lean_inc(v_tree_3403_);
                if lean_obj_tag(v_tree_3403_) == 0 {
                    v_k_3404_ = lean_ctor_get(v___x_3402_, 0);
                    lean_inc(v_k_3404_);
                    v_v_3405_ = lean_ctor_get(v___x_3402_, 1);
                    lean_inc(v_v_3405_);
                    lean_dec_ref(v___x_3402_);
                    v_size_3406_ = lean_ctor_get(v_tree_3403_, 0);
                    v___x_3407_ = lean_unsigned_to_nat(3);
                    v___x_3408_ = lean_nat_mul(v___x_3407_, v_size_3406_);
                    v___x_3409_ = lean_nat_dec_lt(v___x_3408_, v_size_3246_);
                    lean_dec(v___x_3408_);
                    if v___x_3409_ == 0 {
                        lean_dec(v_r_3250_);
                        v___x_3410_ = lean_nat_add(v___x_3256_, v_size_3246_);
                        v___x_3411_ = lean_nat_add(v___x_3410_, v_size_3406_);
                        lean_dec(v___x_3410_);
                        if v_isShared_3401_ == 0 {
                            lean_ctor_set(v___x_3400_, 4, v_tree_3403_);
                            lean_ctor_set(v___x_3400_, 3, v_l_3066_);
                            lean_ctor_set(v___x_3400_, 2, v_v_3405_);
                            lean_ctor_set(v___x_3400_, 1, v_k_3404_);
                            lean_ctor_set(v___x_3400_, 0, v___x_3411_);
                            v___x_3413_ = v___x_3400_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
                            lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_k_3404_);
                            lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_v_3405_);
                            lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_l_3066_);
                            lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_tree_3403_);
                            v___x_3413_ = v_reuseFailAlloc_3414_;
                            state = 52;
                            continue;
                        }
                    } else {
                        lean_inc(v_l_3249_);
                        lean_inc(v_v_3248_);
                        lean_inc(v_k_3247_);
                        lean_inc(v_size_3246_);
                        v_isSharedCheck_3480_ = (!lean_is_exclusive(v_l_3066_)) as u8;
                        if v_isSharedCheck_3480_ == 0 {
                            v_unused_3481_ = lean_ctor_get(v_l_3066_, 4);
                            lean_dec(v_unused_3481_);
                            v_unused_3482_ = lean_ctor_get(v_l_3066_, 3);
                            lean_dec(v_unused_3482_);
                            v_unused_3483_ = lean_ctor_get(v_l_3066_, 2);
                            lean_dec(v_unused_3483_);
                            v_unused_3484_ = lean_ctor_get(v_l_3066_, 1);
                            lean_dec(v_unused_3484_);
                            v_unused_3485_ = lean_ctor_get(v_l_3066_, 0);
                            lean_dec(v_unused_3485_);
                            v___x_3416_ = v_l_3066_;
                            v_isShared_3417_ = v_isSharedCheck_3480_;
                            state = 53;
                            continue;
                        } else {
                            lean_dec(v_l_3066_);
                            v___x_3416_ = lean_box(0);
                            v_isShared_3417_ = v_isSharedCheck_3480_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_l_3249_) == 0 {
                        lean_inc_ref(v_l_3249_);
                        lean_inc(v_v_3248_);
                        lean_inc(v_k_3247_);
                        lean_inc(v_size_3246_);
                        v_isSharedCheck_3509_ = (!lean_is_exclusive(v_l_3066_)) as u8;
                        if v_isSharedCheck_3509_ == 0 {
                            v_unused_3510_ = lean_ctor_get(v_l_3066_, 4);
                            lean_dec(v_unused_3510_);
                            v_unused_3511_ = lean_ctor_get(v_l_3066_, 3);
                            lean_dec(v_unused_3511_);
                            v_unused_3512_ = lean_ctor_get(v_l_3066_, 2);
                            lean_dec(v_unused_3512_);
                            v_unused_3513_ = lean_ctor_get(v_l_3066_, 1);
                            lean_dec(v_unused_3513_);
                            v_unused_3514_ = lean_ctor_get(v_l_3066_, 0);
                            lean_dec(v_unused_3514_);
                            v___x_3487_ = v_l_3066_;
                            v_isShared_3488_ = v_isSharedCheck_3509_;
                            state = 63;
                            continue;
                        } else {
                            lean_dec(v_l_3066_);
                            v___x_3487_ = lean_box(0);
                            v_isShared_3488_ = v_isSharedCheck_3509_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_r_3250_) == 0 {
                            lean_inc(v_l_3249_);
                            lean_inc(v_v_3248_);
                            lean_inc(v_k_3247_);
                            v_isSharedCheck_3539_ = (!lean_is_exclusive(v_l_3066_)) as u8;
                            if v_isSharedCheck_3539_ == 0 {
                                v_unused_3540_ = lean_ctor_get(v_l_3066_, 4);
                                lean_dec(v_unused_3540_);
                                v_unused_3541_ = lean_ctor_get(v_l_3066_, 3);
                                lean_dec(v_unused_3541_);
                                v_unused_3542_ = lean_ctor_get(v_l_3066_, 2);
                                lean_dec(v_unused_3542_);
                                v_unused_3543_ = lean_ctor_get(v_l_3066_, 1);
                                lean_dec(v_unused_3543_);
                                v_unused_3544_ = lean_ctor_get(v_l_3066_, 0);
                                lean_dec(v_unused_3544_);
                                v___x_3516_ = v_l_3066_;
                                v_isShared_3517_ = v_isSharedCheck_3539_;
                                state = 68;
                                continue;
                            } else {
                                lean_dec(v_l_3066_);
                                v___x_3516_ = lean_box(0);
                                v_isShared_3517_ = v_isSharedCheck_3539_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_3545_ = lean_ctor_get(v___x_3402_, 0);
                            lean_inc(v_k_3545_);
                            v_v_3546_ = lean_ctor_get(v___x_3402_, 1);
                            lean_inc(v_v_3546_);
                            lean_dec_ref(v___x_3402_);
                            v___x_3547_ = lean_unsigned_to_nat(2);
                            if v_isShared_3401_ == 0 {
                                lean_ctor_set(v___x_3400_, 4, v_r_3250_);
                                lean_ctor_set(v___x_3400_, 3, v_l_3066_);
                                lean_ctor_set(v___x_3400_, 2, v_v_3546_);
                                lean_ctor_set(v___x_3400_, 1, v_k_3545_);
                                lean_ctor_set(v___x_3400_, 0, v___x_3547_);
                                v___x_3549_ = v___x_3400_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
                                lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_k_3545_);
                                lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_v_3546_);
                                lean_ctor_set(v_reuseFailAlloc_3550_, 3, v_l_3066_);
                                lean_ctor_set(v_reuseFailAlloc_3550_, 4, v_r_3250_);
                                v___x_3549_ = v_reuseFailAlloc_3550_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                return v___x_3413_;
            }
            53 => {
                v_size_3418_ = lean_ctor_get(v_l_3249_, 0);
                v_size_3419_ = lean_ctor_get(v_r_3250_, 0);
                v_k_3420_ = lean_ctor_get(v_r_3250_, 1);
                v_v_3421_ = lean_ctor_get(v_r_3250_, 2);
                v_l_3422_ = lean_ctor_get(v_r_3250_, 3);
                v_r_3423_ = lean_ctor_get(v_r_3250_, 4);
                v___x_3424_ = lean_unsigned_to_nat(2);
                v___x_3425_ = lean_nat_mul(v___x_3424_, v_size_3418_);
                v___x_3426_ = lean_nat_dec_lt(v_size_3419_, v___x_3425_);
                lean_dec(v___x_3425_);
                if v___x_3426_ == 0 {
                    lean_inc(v_r_3423_);
                    lean_inc(v_l_3422_);
                    lean_inc(v_v_3421_);
                    lean_inc(v_k_3420_);
                    lean_del_object(v___x_3416_);
                    v_isSharedCheck_3464_ = (!lean_is_exclusive(v_r_3250_)) as u8;
                    if v_isSharedCheck_3464_ == 0 {
                        v_unused_3465_ = lean_ctor_get(v_r_3250_, 4);
                        lean_dec(v_unused_3465_);
                        v_unused_3466_ = lean_ctor_get(v_r_3250_, 3);
                        lean_dec(v_unused_3466_);
                        v_unused_3467_ = lean_ctor_get(v_r_3250_, 2);
                        lean_dec(v_unused_3467_);
                        v_unused_3468_ = lean_ctor_get(v_r_3250_, 1);
                        lean_dec(v_unused_3468_);
                        v_unused_3469_ = lean_ctor_get(v_r_3250_, 0);
                        lean_dec(v_unused_3469_);
                        v___x_3428_ = v_r_3250_;
                        v_isShared_3429_ = v_isSharedCheck_3464_;
                        state = 54;
                        continue;
                    } else {
                        lean_dec(v_r_3250_);
                        v___x_3428_ = lean_box(0);
                        v_isShared_3429_ = v_isSharedCheck_3464_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_3470_ = lean_nat_add(v___x_3256_, v_size_3246_);
                    lean_dec(v_size_3246_);
                    v___x_3471_ = lean_nat_add(v___x_3470_, v_size_3406_);
                    lean_dec(v___x_3470_);
                    v___x_3472_ = lean_nat_add(v___x_3256_, v_size_3406_);
                    v___x_3473_ = lean_nat_add(v___x_3472_, v_size_3419_);
                    lean_dec(v___x_3472_);
                    if v_isShared_3401_ == 0 {
                        lean_ctor_set(v___x_3400_, 4, v_tree_3403_);
                        lean_ctor_set(v___x_3400_, 3, v_r_3250_);
                        lean_ctor_set(v___x_3400_, 2, v_v_3405_);
                        lean_ctor_set(v___x_3400_, 1, v_k_3404_);
                        lean_ctor_set(v___x_3400_, 0, v___x_3473_);
                        v___x_3475_ = v___x_3400_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3473_);
                        lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3404_);
                        lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3405_);
                        lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_r_3250_);
                        lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_tree_3403_);
                        v___x_3475_ = v_reuseFailAlloc_3479_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_3430_ = lean_nat_add(v___x_3256_, v_size_3246_);
                lean_dec(v_size_3246_);
                v___x_3431_ = lean_nat_add(v___x_3430_, v_size_3406_);
                lean_dec(v___x_3430_);
                v___x_3452_ = lean_nat_add(v___x_3256_, v_size_3418_);
                if lean_obj_tag(v_l_3422_) == 0 {
                    v_size_3462_ = lean_ctor_get(v_l_3422_, 0);
                    lean_inc(v_size_3462_);
                    v___y_3454_ = v_size_3462_;
                    state = 59;
                    continue;
                } else {
                    v___x_3463_ = lean_unsigned_to_nat(0);
                    v___y_3454_ = v___x_3463_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_3436_ = lean_nat_add(v___y_3434_, v___y_3435_);
                lean_dec(v___y_3435_);
                lean_dec(v___y_3434_);
                lean_inc_ref(v_tree_3403_);
                if v_isShared_3429_ == 0 {
                    lean_ctor_set(v___x_3428_, 4, v_tree_3403_);
                    lean_ctor_set(v___x_3428_, 3, v_r_3423_);
                    lean_ctor_set(v___x_3428_, 2, v_v_3405_);
                    lean_ctor_set(v___x_3428_, 1, v_k_3404_);
                    lean_ctor_set(v___x_3428_, 0, v___x_3436_);
                    v___x_3438_ = v___x_3428_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3436_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3404_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3405_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_r_3423_);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_tree_3403_);
                    v___x_3438_ = v_reuseFailAlloc_3451_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_3445_ = (!lean_is_exclusive(v_tree_3403_)) as u8;
                if v_isSharedCheck_3445_ == 0 {
                    v_unused_3446_ = lean_ctor_get(v_tree_3403_, 4);
                    lean_dec(v_unused_3446_);
                    v_unused_3447_ = lean_ctor_get(v_tree_3403_, 3);
                    lean_dec(v_unused_3447_);
                    v_unused_3448_ = lean_ctor_get(v_tree_3403_, 2);
                    lean_dec(v_unused_3448_);
                    v_unused_3449_ = lean_ctor_get(v_tree_3403_, 1);
                    lean_dec(v_unused_3449_);
                    v_unused_3450_ = lean_ctor_get(v_tree_3403_, 0);
                    lean_dec(v_unused_3450_);
                    v___x_3440_ = v_tree_3403_;
                    v_isShared_3441_ = v_isSharedCheck_3445_;
                    state = 57;
                    continue;
                } else {
                    lean_dec(v_tree_3403_);
                    v___x_3440_ = lean_box(0);
                    v_isShared_3441_ = v_isSharedCheck_3445_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_3441_ == 0 {
                    lean_ctor_set(v___x_3440_, 4, v___x_3438_);
                    lean_ctor_set(v___x_3440_, 3, v___y_3433_);
                    lean_ctor_set(v___x_3440_, 2, v_v_3421_);
                    lean_ctor_set(v___x_3440_, 1, v_k_3420_);
                    lean_ctor_set(v___x_3440_, 0, v___x_3431_);
                    v___x_3443_ = v___x_3440_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3431_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_k_3420_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_v_3421_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 3, v___y_3433_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 4, v___x_3438_);
                    v___x_3443_ = v_reuseFailAlloc_3444_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_3443_;
            }
            59 => {
                v___x_3455_ = lean_nat_add(v___x_3452_, v___y_3454_);
                lean_dec(v___y_3454_);
                lean_dec(v___x_3452_);
                if v_isShared_3401_ == 0 {
                    lean_ctor_set(v___x_3400_, 4, v_l_3422_);
                    lean_ctor_set(v___x_3400_, 3, v_l_3249_);
                    lean_ctor_set(v___x_3400_, 2, v_v_3248_);
                    lean_ctor_set(v___x_3400_, 1, v_k_3247_);
                    lean_ctor_set(v___x_3400_, 0, v___x_3455_);
                    v___x_3457_ = v___x_3400_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3455_);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_k_3247_);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_v_3248_);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 3, v_l_3249_);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 4, v_l_3422_);
                    v___x_3457_ = v_reuseFailAlloc_3461_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_3458_ = lean_nat_add(v___x_3256_, v_size_3406_);
                if lean_obj_tag(v_r_3423_) == 0 {
                    v_size_3459_ = lean_ctor_get(v_r_3423_, 0);
                    lean_inc(v_size_3459_);
                    v___y_3433_ = v___x_3457_;
                    v___y_3434_ = v___x_3458_;
                    v___y_3435_ = v_size_3459_;
                    state = 55;
                    continue;
                } else {
                    v___x_3460_ = lean_unsigned_to_nat(0);
                    v___y_3433_ = v___x_3457_;
                    v___y_3434_ = v___x_3458_;
                    v___y_3435_ = v___x_3460_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_3417_ == 0 {
                    lean_ctor_set(v___x_3416_, 4, v___x_3475_);
                    lean_ctor_set(v___x_3416_, 0, v___x_3471_);
                    v___x_3477_ = v___x_3416_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3471_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3247_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3248_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_l_3249_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 4, v___x_3475_);
                    v___x_3477_ = v_reuseFailAlloc_3478_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_3477_;
            }
            63 => {
                if lean_obj_tag(v_r_3250_) == 0 {
                    v_k_3489_ = lean_ctor_get(v___x_3402_, 0);
                    lean_inc(v_k_3489_);
                    v_v_3490_ = lean_ctor_get(v___x_3402_, 1);
                    lean_inc(v_v_3490_);
                    lean_dec_ref(v___x_3402_);
                    v_size_3491_ = lean_ctor_get(v_r_3250_, 0);
                    v___x_3492_ = lean_nat_add(v___x_3256_, v_size_3246_);
                    lean_dec(v_size_3246_);
                    v___x_3493_ = lean_nat_add(v___x_3256_, v_size_3491_);
                    if v_isShared_3401_ == 0 {
                        lean_ctor_set(v___x_3400_, 4, v_tree_3403_);
                        lean_ctor_set(v___x_3400_, 3, v_r_3250_);
                        lean_ctor_set(v___x_3400_, 2, v_v_3490_);
                        lean_ctor_set(v___x_3400_, 1, v_k_3489_);
                        lean_ctor_set(v___x_3400_, 0, v___x_3493_);
                        v___x_3495_ = v___x_3400_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3493_);
                        lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_k_3489_);
                        lean_ctor_set(v_reuseFailAlloc_3499_, 2, v_v_3490_);
                        lean_ctor_set(v_reuseFailAlloc_3499_, 3, v_r_3250_);
                        lean_ctor_set(v_reuseFailAlloc_3499_, 4, v_tree_3403_);
                        v___x_3495_ = v_reuseFailAlloc_3499_;
                        state = 64;
                        continue;
                    }
                } else {
                    lean_dec(v_size_3246_);
                    v_k_3500_ = lean_ctor_get(v___x_3402_, 0);
                    lean_inc(v_k_3500_);
                    v_v_3501_ = lean_ctor_get(v___x_3402_, 1);
                    lean_inc(v_v_3501_);
                    lean_dec_ref(v___x_3402_);
                    v___x_3502_ = lean_unsigned_to_nat(3);
                    if v_isShared_3401_ == 0 {
                        lean_ctor_set(v___x_3400_, 4, v_r_3250_);
                        lean_ctor_set(v___x_3400_, 3, v_r_3250_);
                        lean_ctor_set(v___x_3400_, 2, v_v_3501_);
                        lean_ctor_set(v___x_3400_, 1, v_k_3500_);
                        lean_ctor_set(v___x_3400_, 0, v___x_3256_);
                        v___x_3504_ = v___x_3400_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3256_);
                        lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_k_3500_);
                        lean_ctor_set(v_reuseFailAlloc_3508_, 2, v_v_3501_);
                        lean_ctor_set(v_reuseFailAlloc_3508_, 3, v_r_3250_);
                        lean_ctor_set(v_reuseFailAlloc_3508_, 4, v_r_3250_);
                        v___x_3504_ = v_reuseFailAlloc_3508_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_3488_ == 0 {
                    lean_ctor_set(v___x_3487_, 4, v___x_3495_);
                    lean_ctor_set(v___x_3487_, 0, v___x_3492_);
                    v___x_3497_ = v___x_3487_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3492_);
                    lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_k_3247_);
                    lean_ctor_set(v_reuseFailAlloc_3498_, 2, v_v_3248_);
                    lean_ctor_set(v_reuseFailAlloc_3498_, 3, v_l_3249_);
                    lean_ctor_set(v_reuseFailAlloc_3498_, 4, v___x_3495_);
                    v___x_3497_ = v_reuseFailAlloc_3498_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_3497_;
            }
            66 => {
                if v_isShared_3488_ == 0 {
                    lean_ctor_set(v___x_3487_, 4, v___x_3504_);
                    lean_ctor_set(v___x_3487_, 0, v___x_3502_);
                    v___x_3506_ = v___x_3487_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3502_);
                    lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_k_3247_);
                    lean_ctor_set(v_reuseFailAlloc_3507_, 2, v_v_3248_);
                    lean_ctor_set(v_reuseFailAlloc_3507_, 3, v_l_3249_);
                    lean_ctor_set(v_reuseFailAlloc_3507_, 4, v___x_3504_);
                    v___x_3506_ = v_reuseFailAlloc_3507_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_3506_;
            }
            68 => {
                v_k_3518_ = lean_ctor_get(v___x_3402_, 0);
                lean_inc(v_k_3518_);
                v_v_3519_ = lean_ctor_get(v___x_3402_, 1);
                lean_inc(v_v_3519_);
                lean_dec_ref(v___x_3402_);
                v_k_3520_ = lean_ctor_get(v_r_3250_, 1);
                v_v_3521_ = lean_ctor_get(v_r_3250_, 2);
                v_isSharedCheck_3535_ = (!lean_is_exclusive(v_r_3250_)) as u8;
                if v_isSharedCheck_3535_ == 0 {
                    v_unused_3536_ = lean_ctor_get(v_r_3250_, 4);
                    lean_dec(v_unused_3536_);
                    v_unused_3537_ = lean_ctor_get(v_r_3250_, 3);
                    lean_dec(v_unused_3537_);
                    v_unused_3538_ = lean_ctor_get(v_r_3250_, 0);
                    lean_dec(v_unused_3538_);
                    v___x_3523_ = v_r_3250_;
                    v_isShared_3524_ = v_isSharedCheck_3535_;
                    state = 69;
                    continue;
                } else {
                    lean_inc(v_v_3521_);
                    lean_inc(v_k_3520_);
                    lean_dec(v_r_3250_);
                    v___x_3523_ = lean_box(0);
                    v_isShared_3524_ = v_isSharedCheck_3535_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_3525_ = lean_unsigned_to_nat(3);
                if v_isShared_3524_ == 0 {
                    lean_ctor_set(v___x_3523_, 4, v_l_3249_);
                    lean_ctor_set(v___x_3523_, 3, v_l_3249_);
                    lean_ctor_set(v___x_3523_, 2, v_v_3248_);
                    lean_ctor_set(v___x_3523_, 1, v_k_3247_);
                    lean_ctor_set(v___x_3523_, 0, v___x_3256_);
                    v___x_3527_ = v___x_3523_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3256_);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_k_3247_);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_v_3248_);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_l_3249_);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_l_3249_);
                    v___x_3527_ = v_reuseFailAlloc_3534_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_3401_ == 0 {
                    lean_ctor_set(v___x_3400_, 4, v_l_3249_);
                    lean_ctor_set(v___x_3400_, 3, v_l_3249_);
                    lean_ctor_set(v___x_3400_, 2, v_v_3519_);
                    lean_ctor_set(v___x_3400_, 1, v_k_3518_);
                    lean_ctor_set(v___x_3400_, 0, v___x_3256_);
                    v___x_3529_ = v___x_3400_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3256_);
                    lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_k_3518_);
                    lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_v_3519_);
                    lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_l_3249_);
                    lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_l_3249_);
                    v___x_3529_ = v_reuseFailAlloc_3533_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_3517_ == 0 {
                    lean_ctor_set(v___x_3516_, 4, v___x_3529_);
                    lean_ctor_set(v___x_3516_, 3, v___x_3527_);
                    lean_ctor_set(v___x_3516_, 2, v_v_3521_);
                    lean_ctor_set(v___x_3516_, 1, v_k_3520_);
                    lean_ctor_set(v___x_3516_, 0, v___x_3525_);
                    v___x_3531_ = v___x_3516_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3525_);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_k_3520_);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 2, v_v_3521_);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 3, v___x_3527_);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 4, v___x_3529_);
                    v___x_3531_ = v_reuseFailAlloc_3532_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_3531_;
            }
            73 => {
                return v___x_3549_;
            }
            74 => {
                return v___x_3571_;
            }
            75 => {
                v_size_3576_ = lean_ctor_get(v_l_3563_, 0);
                v_size_3577_ = lean_ctor_get(v_r_3564_, 0);
                v_k_3578_ = lean_ctor_get(v_r_3564_, 1);
                v_v_3579_ = lean_ctor_get(v_r_3564_, 2);
                v_l_3580_ = lean_ctor_get(v_r_3564_, 3);
                v_r_3581_ = lean_ctor_get(v_r_3564_, 4);
                v___x_3582_ = lean_unsigned_to_nat(2);
                v___x_3583_ = lean_nat_mul(v___x_3582_, v_size_3576_);
                v___x_3584_ = lean_nat_dec_lt(v_size_3577_, v___x_3583_);
                lean_dec(v___x_3583_);
                if v___x_3584_ == 0 {
                    lean_inc(v_r_3581_);
                    lean_inc(v_l_3580_);
                    lean_inc(v_v_3579_);
                    lean_inc(v_k_3578_);
                    v_isSharedCheck_3613_ = (!lean_is_exclusive(v_r_3564_)) as u8;
                    if v_isSharedCheck_3613_ == 0 {
                        v_unused_3614_ = lean_ctor_get(v_r_3564_, 4);
                        lean_dec(v_unused_3614_);
                        v_unused_3615_ = lean_ctor_get(v_r_3564_, 3);
                        lean_dec(v_unused_3615_);
                        v_unused_3616_ = lean_ctor_get(v_r_3564_, 2);
                        lean_dec(v_unused_3616_);
                        v_unused_3617_ = lean_ctor_get(v_r_3564_, 1);
                        lean_dec(v_unused_3617_);
                        v_unused_3618_ = lean_ctor_get(v_r_3564_, 0);
                        lean_dec(v_unused_3618_);
                        v___x_3586_ = v_r_3564_;
                        v_isShared_3587_ = v_isSharedCheck_3613_;
                        state = 76;
                        continue;
                    } else {
                        lean_dec(v_r_3564_);
                        v___x_3586_ = lean_box(0);
                        v_isShared_3587_ = v_isSharedCheck_3613_;
                        state = 76;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3069_);
                    v___x_3619_ = lean_nat_add(v___x_3558_, v_size_3560_);
                    lean_dec(v_size_3560_);
                    v___x_3620_ = lean_nat_add(v___x_3619_, v_size_3559_);
                    lean_dec(v___x_3619_);
                    v___x_3621_ = lean_nat_add(v___x_3558_, v_size_3559_);
                    lean_dec(v_size_3559_);
                    v___x_3622_ = lean_nat_add(v___x_3621_, v_size_3577_);
                    lean_dec(v___x_3621_);
                    lean_inc_ref(v_impl_3557_);
                    if v_isShared_3575_ == 0 {
                        lean_ctor_set(v___x_3574_, 4, v_impl_3557_);
                        lean_ctor_set(v___x_3574_, 3, v_r_3564_);
                        lean_ctor_set(v___x_3574_, 2, v_v_3065_);
                        lean_ctor_set(v___x_3574_, 1, v_k_3064_);
                        lean_ctor_set(v___x_3574_, 0, v___x_3622_);
                        v___x_3624_ = v___x_3574_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3622_);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_k_3064_);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_v_3065_);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_r_3564_);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_impl_3557_);
                        v___x_3624_ = v_reuseFailAlloc_3637_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_3588_ = lean_nat_add(v___x_3558_, v_size_3560_);
                lean_dec(v_size_3560_);
                v___x_3589_ = lean_nat_add(v___x_3588_, v_size_3559_);
                lean_dec(v___x_3588_);
                v___x_3601_ = lean_nat_add(v___x_3558_, v_size_3576_);
                if lean_obj_tag(v_l_3580_) == 0 {
                    v_size_3611_ = lean_ctor_get(v_l_3580_, 0);
                    lean_inc(v_size_3611_);
                    v___y_3603_ = v_size_3611_;
                    state = 80;
                    continue;
                } else {
                    v___x_3612_ = lean_unsigned_to_nat(0);
                    v___y_3603_ = v___x_3612_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_3594_ = lean_nat_add(v___y_3592_, v___y_3593_);
                lean_dec(v___y_3593_);
                lean_dec(v___y_3592_);
                if v_isShared_3587_ == 0 {
                    lean_ctor_set(v___x_3586_, 4, v_impl_3557_);
                    lean_ctor_set(v___x_3586_, 3, v_r_3581_);
                    lean_ctor_set(v___x_3586_, 2, v_v_3065_);
                    lean_ctor_set(v___x_3586_, 1, v_k_3064_);
                    lean_ctor_set(v___x_3586_, 0, v___x_3594_);
                    v___x_3596_ = v___x_3586_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3594_);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_r_3581_);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_impl_3557_);
                    v___x_3596_ = v_reuseFailAlloc_3600_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_3575_ == 0 {
                    lean_ctor_set(v___x_3574_, 4, v___x_3596_);
                    lean_ctor_set(v___x_3574_, 3, v___y_3591_);
                    lean_ctor_set(v___x_3574_, 2, v_v_3579_);
                    lean_ctor_set(v___x_3574_, 1, v_k_3578_);
                    lean_ctor_set(v___x_3574_, 0, v___x_3589_);
                    v___x_3598_ = v___x_3574_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3589_);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_k_3578_);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_v_3579_);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 3, v___y_3591_);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 4, v___x_3596_);
                    v___x_3598_ = v_reuseFailAlloc_3599_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_3598_;
            }
            80 => {
                v___x_3604_ = lean_nat_add(v___x_3601_, v___y_3603_);
                lean_dec(v___y_3603_);
                lean_dec(v___x_3601_);
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v_l_3580_);
                    lean_ctor_set(v___x_3069_, 3, v_l_3563_);
                    lean_ctor_set(v___x_3069_, 2, v_v_3562_);
                    lean_ctor_set(v___x_3069_, 1, v_k_3561_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3604_);
                    v___x_3606_ = v___x_3069_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3604_);
                    lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3561_);
                    lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3562_);
                    lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_l_3563_);
                    lean_ctor_set(v_reuseFailAlloc_3610_, 4, v_l_3580_);
                    v___x_3606_ = v_reuseFailAlloc_3610_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_3607_ = lean_nat_add(v___x_3558_, v_size_3559_);
                lean_dec(v_size_3559_);
                if lean_obj_tag(v_r_3581_) == 0 {
                    v_size_3608_ = lean_ctor_get(v_r_3581_, 0);
                    lean_inc(v_size_3608_);
                    v___y_3591_ = v___x_3606_;
                    v___y_3592_ = v___x_3607_;
                    v___y_3593_ = v_size_3608_;
                    state = 77;
                    continue;
                } else {
                    v___x_3609_ = lean_unsigned_to_nat(0);
                    v___y_3591_ = v___x_3606_;
                    v___y_3592_ = v___x_3607_;
                    v___y_3593_ = v___x_3609_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_3631_ = (!lean_is_exclusive(v_impl_3557_)) as u8;
                if v_isSharedCheck_3631_ == 0 {
                    v_unused_3632_ = lean_ctor_get(v_impl_3557_, 4);
                    lean_dec(v_unused_3632_);
                    v_unused_3633_ = lean_ctor_get(v_impl_3557_, 3);
                    lean_dec(v_unused_3633_);
                    v_unused_3634_ = lean_ctor_get(v_impl_3557_, 2);
                    lean_dec(v_unused_3634_);
                    v_unused_3635_ = lean_ctor_get(v_impl_3557_, 1);
                    lean_dec(v_unused_3635_);
                    v_unused_3636_ = lean_ctor_get(v_impl_3557_, 0);
                    lean_dec(v_unused_3636_);
                    v___x_3626_ = v_impl_3557_;
                    v_isShared_3627_ = v_isSharedCheck_3631_;
                    state = 83;
                    continue;
                } else {
                    lean_dec(v_impl_3557_);
                    v___x_3626_ = lean_box(0);
                    v_isShared_3627_ = v_isSharedCheck_3631_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_3627_ == 0 {
                    lean_ctor_set(v___x_3626_, 4, v___x_3624_);
                    lean_ctor_set(v___x_3626_, 3, v_l_3563_);
                    lean_ctor_set(v___x_3626_, 2, v_v_3562_);
                    lean_ctor_set(v___x_3626_, 1, v_k_3561_);
                    lean_ctor_set(v___x_3626_, 0, v___x_3620_);
                    v___x_3629_ = v___x_3626_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3620_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3561_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3562_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_l_3563_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 4, v___x_3624_);
                    v___x_3629_ = v_reuseFailAlloc_3630_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_3629_;
            }
            85 => {
                return v___x_3647_;
            }
            86 => {
                v_size_3657_ = lean_ctor_get(v_r_3650_, 0);
                v___x_3658_ = lean_nat_add(v___x_3558_, v_size_3651_);
                lean_dec(v_size_3651_);
                v___x_3659_ = lean_nat_add(v___x_3558_, v_size_3657_);
                if v_isShared_3656_ == 0 {
                    lean_ctor_set(v___x_3655_, 4, v_impl_3557_);
                    lean_ctor_set(v___x_3655_, 3, v_r_3650_);
                    lean_ctor_set(v___x_3655_, 2, v_v_3065_);
                    lean_ctor_set(v___x_3655_, 1, v_k_3064_);
                    lean_ctor_set(v___x_3655_, 0, v___x_3659_);
                    v___x_3661_ = v___x_3655_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3659_);
                    lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3665_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3665_, 3, v_r_3650_);
                    lean_ctor_set(v_reuseFailAlloc_3665_, 4, v_impl_3557_);
                    v___x_3661_ = v_reuseFailAlloc_3665_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v___x_3661_);
                    lean_ctor_set(v___x_3069_, 3, v_l_3649_);
                    lean_ctor_set(v___x_3069_, 2, v_v_3653_);
                    lean_ctor_set(v___x_3069_, 1, v_k_3652_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3658_);
                    v___x_3663_ = v___x_3069_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3658_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_k_3652_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_v_3653_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 3, v_l_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 4, v___x_3661_);
                    v___x_3663_ = v_reuseFailAlloc_3664_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_3663_;
            }
            89 => {
                v___x_3674_ = lean_unsigned_to_nat(3);
                if v_isShared_3673_ == 0 {
                    lean_ctor_set(v___x_3672_, 3, v_r_3650_);
                    lean_ctor_set(v___x_3672_, 2, v_v_3065_);
                    lean_ctor_set(v___x_3672_, 1, v_k_3064_);
                    lean_ctor_set(v___x_3672_, 0, v___x_3558_);
                    v___x_3676_ = v___x_3672_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3558_);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_r_3650_);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_r_3650_);
                    v___x_3676_ = v_reuseFailAlloc_3680_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v___x_3676_);
                    lean_ctor_set(v___x_3069_, 3, v_l_3649_);
                    lean_ctor_set(v___x_3069_, 2, v_v_3670_);
                    lean_ctor_set(v___x_3069_, 1, v_k_3669_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3674_);
                    v___x_3678_ = v___x_3069_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3674_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_k_3669_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_v_3670_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_l_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 4, v___x_3676_);
                    v___x_3678_ = v_reuseFailAlloc_3679_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_3678_;
            }
            92 => {
                v_k_3691_ = lean_ctor_get(v_r_3685_, 1);
                v_v_3692_ = lean_ctor_get(v_r_3685_, 2);
                v_isSharedCheck_3706_ = (!lean_is_exclusive(v_r_3685_)) as u8;
                if v_isSharedCheck_3706_ == 0 {
                    v_unused_3707_ = lean_ctor_get(v_r_3685_, 4);
                    lean_dec(v_unused_3707_);
                    v_unused_3708_ = lean_ctor_get(v_r_3685_, 3);
                    lean_dec(v_unused_3708_);
                    v_unused_3709_ = lean_ctor_get(v_r_3685_, 0);
                    lean_dec(v_unused_3709_);
                    v___x_3694_ = v_r_3685_;
                    v_isShared_3695_ = v_isSharedCheck_3706_;
                    state = 93;
                    continue;
                } else {
                    lean_inc(v_v_3692_);
                    lean_inc(v_k_3691_);
                    lean_dec(v_r_3685_);
                    v___x_3694_ = lean_box(0);
                    v_isShared_3695_ = v_isSharedCheck_3706_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_3696_ = lean_unsigned_to_nat(3);
                if v_isShared_3695_ == 0 {
                    lean_ctor_set(v___x_3694_, 4, v_l_3649_);
                    lean_ctor_set(v___x_3694_, 3, v_l_3649_);
                    lean_ctor_set(v___x_3694_, 2, v_v_3687_);
                    lean_ctor_set(v___x_3694_, 1, v_k_3686_);
                    lean_ctor_set(v___x_3694_, 0, v___x_3558_);
                    v___x_3698_ = v___x_3694_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3558_);
                    lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_k_3686_);
                    lean_ctor_set(v_reuseFailAlloc_3705_, 2, v_v_3687_);
                    lean_ctor_set(v_reuseFailAlloc_3705_, 3, v_l_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3705_, 4, v_l_3649_);
                    v___x_3698_ = v_reuseFailAlloc_3705_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_3690_ == 0 {
                    lean_ctor_set(v___x_3689_, 4, v_l_3649_);
                    lean_ctor_set(v___x_3689_, 2, v_v_3065_);
                    lean_ctor_set(v___x_3689_, 1, v_k_3064_);
                    lean_ctor_set(v___x_3689_, 0, v___x_3558_);
                    v___x_3700_ = v___x_3689_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3558_);
                    lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_k_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_v_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_l_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_l_3649_);
                    v___x_3700_ = v_reuseFailAlloc_3704_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_3070_ == 0 {
                    lean_ctor_set(v___x_3069_, 4, v___x_3700_);
                    lean_ctor_set(v___x_3069_, 3, v___x_3698_);
                    lean_ctor_set(v___x_3069_, 2, v_v_3692_);
                    lean_ctor_set(v___x_3069_, 1, v_k_3691_);
                    lean_ctor_set(v___x_3069_, 0, v___x_3696_);
                    v___x_3702_ = v___x_3069_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3696_);
                    lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_k_3691_);
                    lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_v_3692_);
                    lean_ctor_set(v_reuseFailAlloc_3703_, 3, v___x_3698_);
                    lean_ctor_set(v_reuseFailAlloc_3703_, 4, v___x_3700_);
                    v___x_3702_ = v_reuseFailAlloc_3703_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_3702_;
            }
            97 => {
                return v___x_3716_;
            }
            98 => {
                return v___x_3719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg___boxed(
    mut v_k_3723_: *mut LeanObject,
    mut v_t_3724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3725_: *mut LeanObject = core::ptr::null_mut();
    v_res_3725_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_k_3723_, v_t_3724_);
    lean_dec(v_k_3723_);
    return v_res_3725_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1(
    mut v_as_3726_: *mut LeanObject,
    mut v_i_3727_: usize,
    mut v_stop_3728_: usize,
    mut v_b_3729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thm_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: usize = 0;
    let mut v___x_3735_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3730_ = lean_usize_dec_eq(v_i_3727_, v_stop_3728_);
                if v___x_3730_ == 0 {
                    v___x_3731_ = lean_array_uget_borrowed(v_as_3726_, v_i_3727_);
                    v_thm_3732_ = lean_ctor_get(v___x_3731_, 2);
                    lean_inc_ref(v_thm_3732_);
                    v___x_3733_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_3729_, v_thm_3732_);
                    v___x_3734_ = 1usize;
                    v___x_3735_ = lean_usize_add(v_i_3727_, v___x_3734_);
                    v_i_3727_ = v___x_3735_;
                    v_b_3729_ = v___x_3733_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3729_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1___boxed(
    mut v_as_3737_: *mut LeanObject,
    mut v_i_3738_: *mut LeanObject,
    mut v_stop_3739_: *mut LeanObject,
    mut v_b_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3741_: usize = 0;
    let mut v_stop_boxed_3742_: usize = 0;
    let mut v_res_3743_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3741_ = lean_unbox_usize(v_i_3738_);
    lean_dec(v_i_3738_);
    v_stop_boxed_3742_ = lean_unbox_usize(v_stop_3739_);
    lean_dec(v_stop_3739_);
    v_res_3743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1(v_as_3737_, v_i_boxed_3741_, v_stop_boxed_3742_, v_b_3740_);
    lean_dec_ref(v_as_3737_);
    return v_res_3743_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas(
    mut v_entries_3746_: *mut LeanObject,
    mut v_appFn_3747_: *mut LeanObject,
    mut v_lemmas_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_appFnEntries_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    v___x_3749_ = lean_unsigned_to_nat(0);
    v___x_3750_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0;
    v_appFnEntries_3751_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg(v_entries_3746_, v_appFn_3747_, v___x_3750_);
    v___x_3752_ = lean_array_get_size(v_appFnEntries_3751_);
    v___x_3753_ = lean_nat_dec_eq(v___x_3752_, v___x_3749_);
    if v___x_3753_ == 0 {
        let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3755_: u8 = 0;
        v___x_3754_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2_once),
            _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2,
        );
        v___x_3755_ = lean_nat_dec_lt(v___x_3749_, v___x_3752_);
        if v___x_3755_ == 0 {
            let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_appFnEntries_3751_);
            v___x_3756_ =
                l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
                    v_appFn_3747_,
                    v___x_3754_,
                    v_lemmas_3748_,
                );
            return v___x_3756_;
        } else {
            let mut v___x_3757_: u8 = 0;
            v___x_3757_ = lean_nat_dec_le(v___x_3752_, v___x_3752_);
            if v___x_3757_ == 0 {
                if v___x_3755_ == 0 {
                    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_appFnEntries_3751_);
                    v___x_3758_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3747_, v___x_3754_, v_lemmas_3748_);
                    return v___x_3758_;
                } else {
                    let mut v___x_3759_: usize = 0;
                    let mut v___x_3760_: usize = 0;
                    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
                    v___x_3759_ = 0usize;
                    v___x_3760_ = lean_usize_of_nat(v___x_3752_);
                    v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1(v_appFnEntries_3751_, v___x_3759_, v___x_3760_, v___x_3754_);
                    lean_dec(v_appFnEntries_3751_);
                    v___x_3762_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3747_, v___x_3761_, v_lemmas_3748_);
                    return v___x_3762_;
                }
            } else {
                let mut v___x_3763_: usize = 0;
                let mut v___x_3764_: usize = 0;
                let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
                v___x_3763_ = 0usize;
                v___x_3764_ = lean_usize_of_nat(v___x_3752_);
                v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1(v_appFnEntries_3751_, v___x_3763_, v___x_3764_, v___x_3754_);
                lean_dec(v_appFnEntries_3751_);
                v___x_3766_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3747_, v___x_3765_, v_lemmas_3748_);
                return v___x_3766_;
            }
        }
    } else {
        let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_appFnEntries_3751_);
        v___x_3767_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_appFn_3747_, v_lemmas_3748_);
        lean_dec(v_appFn_3747_);
        return v___x_3767_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___boxed(
    mut v_entries_3768_: *mut LeanObject,
    mut v_appFn_3769_: *mut LeanObject,
    mut v_lemmas_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3771_: *mut LeanObject = core::ptr::null_mut();
    v_res_3771_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas(v_entries_3768_, v_appFn_3769_, v_lemmas_3770_);
    lean_dec(v_entries_3768_);
    return v_res_3771_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0(
    mut v_00_u03b4_3772_: *mut LeanObject,
    mut v_t_3773_: *mut LeanObject,
    mut v_k_3774_: *mut LeanObject,
    mut v_fallback_3775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg(v_t_3773_, v_k_3774_, v_fallback_3775_);
    return v___x_3776_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___boxed(
    mut v_00_u03b4_3777_: *mut LeanObject,
    mut v_t_3778_: *mut LeanObject,
    mut v_k_3779_: *mut LeanObject,
    mut v_fallback_3780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3781_: *mut LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0(v_00_u03b4_3777_, v_t_3778_, v_k_3779_, v_fallback_3780_);
    lean_dec(v_fallback_3780_);
    lean_dec(v_k_3779_);
    lean_dec(v_t_3778_);
    return v_res_3781_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2(
    mut v_00_u03b2_3782_: *mut LeanObject,
    mut v_k_3783_: *mut LeanObject,
    mut v_t_3784_: *mut LeanObject,
    mut v_h_3785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___x_3786_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_k_3783_, v_t_3784_);
    return v___x_3786_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___boxed(
    mut v_00_u03b2_3787_: *mut LeanObject,
    mut v_k_3788_: *mut LeanObject,
    mut v_t_3789_: *mut LeanObject,
    mut v_h_3790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3791_: *mut LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2(v_00_u03b2_3787_, v_k_3788_, v_t_3789_, v_h_3790_);
    lean_dec(v_k_3788_);
    return v_res_3791_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2(
    mut v_declName_3792_: *mut LeanObject,
    mut v_as_3793_: *mut LeanObject,
    mut v_i_3794_: usize,
    mut v_stop_3795_: usize,
    mut v_b_3796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: usize = 0;
    let mut v___x_3800_: usize = 0;
    let mut v___x_3802_: u8 = 0;
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3802_ = lean_usize_dec_eq(v_i_3794_, v_stop_3795_);
                if v___x_3802_ == 0 {
                    v___x_3803_ = lean_array_uget_borrowed(v_as_3793_, v_i_3794_);
                    v_origin_3804_ = lean_ctor_get(v___x_3803_, 0);
                    v___x_3805_ = lean_name_eq(v_origin_3804_, v_declName_3792_);
                    if v___x_3805_ == 0 {
                        lean_inc(v___x_3803_);
                        v___x_3806_ = lean_array_push(v_b_3796_, v___x_3803_);
                        v___y_3798_ = v___x_3806_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3798_ = v_b_3796_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3796_;
                }
            }
            1 => {
                v___x_3799_ = 1usize;
                v___x_3800_ = lean_usize_add(v_i_3794_, v___x_3799_);
                v_i_3794_ = v___x_3800_;
                v_b_3796_ = v___y_3798_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2___boxed(
    mut v_declName_3807_: *mut LeanObject,
    mut v_as_3808_: *mut LeanObject,
    mut v_i_3809_: *mut LeanObject,
    mut v_stop_3810_: *mut LeanObject,
    mut v_b_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3812_: usize = 0;
    let mut v_stop_boxed_3813_: usize = 0;
    let mut v_res_3814_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3812_ = lean_unbox_usize(v_i_3809_);
    lean_dec(v_i_3809_);
    v_stop_boxed_3813_ = lean_unbox_usize(v_stop_3810_);
    lean_dec(v_stop_3810_);
    v_res_3814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2(v_declName_3807_, v_as_3808_, v_i_boxed_3812_, v_stop_boxed_3813_, v_b_3811_);
    lean_dec_ref(v_as_3808_);
    lean_dec(v_declName_3807_);
    return v_res_3814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__0(
    mut v_declName_3815_: *mut LeanObject,
    mut v_as_3816_: *mut LeanObject,
    mut v_i_3817_: usize,
    mut v_stop_3818_: usize,
) -> u8 {
    let mut v___x_3819_: u8 = 0;
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: u8 = 0;
    let mut v___x_3823_: usize = 0;
    let mut v___x_3824_: usize = 0;
    let mut v___x_3826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3819_ = lean_usize_dec_eq(v_i_3817_, v_stop_3818_);
                if v___x_3819_ == 0 {
                    v___x_3820_ = lean_array_uget_borrowed(v_as_3816_, v_i_3817_);
                    v_origin_3821_ = lean_ctor_get(v___x_3820_, 0);
                    v___x_3822_ = lean_name_eq(v_origin_3821_, v_declName_3815_);
                    if v___x_3822_ == 0 {
                        v___x_3823_ = 1usize;
                        v___x_3824_ = lean_usize_add(v_i_3817_, v___x_3823_);
                        v_i_3817_ = v___x_3824_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3822_;
                    }
                } else {
                    v___x_3826_ = 0;
                    return v___x_3826_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__0___boxed(
    mut v_declName_3827_: *mut LeanObject,
    mut v_as_3828_: *mut LeanObject,
    mut v_i_3829_: *mut LeanObject,
    mut v_stop_3830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3831_: usize = 0;
    let mut v_stop_boxed_3832_: usize = 0;
    let mut v_res_3833_: u8 = 0;
    let mut v_r_3834_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3831_ = lean_unbox_usize(v_i_3829_);
    lean_dec(v_i_3829_);
    v_stop_boxed_3832_ = lean_unbox_usize(v_stop_3830_);
    lean_dec(v_stop_3830_);
    v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__0(v_declName_3827_, v_as_3828_, v_i_boxed_3831_, v_stop_boxed_3832_);
    lean_dec_ref(v_as_3828_);
    lean_dec(v_declName_3827_);
    v_r_3834_ = lean_box((v_res_3833_) as usize);
    return v_r_3834_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(
    mut v_declName_3835_: *mut LeanObject,
    mut v_init_3836_: *mut LeanObject,
    mut v_x_3837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3848_: usize = 0;
    let mut v___x_3849_: usize = 0;
    let mut v___x_3850_: u8 = 0;
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3837_) == 0 {
                    v_k_3838_ = lean_ctor_get(v_x_3837_, 1);
                    v_v_3839_ = lean_ctor_get(v_x_3837_, 2);
                    v_l_3840_ = lean_ctor_get(v_x_3837_, 3);
                    v_r_3841_ = lean_ctor_get(v_x_3837_, 4);
                    v___x_3842_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(v_declName_3835_, v_init_3836_, v_l_3840_);
                    if lean_obj_tag(v___x_3842_) == 0 {
                        v___x_3843_ = lean_unsigned_to_nat(0);
                        v___x_3844_ = lean_array_get_size(v_v_3839_);
                        v___x_3845_ = lean_nat_dec_lt(v___x_3843_, v___x_3844_);
                        if v___x_3845_ == 0 {
                            v_init_3836_ = v___x_3842_;
                            v_x_3837_ = v_r_3841_;
                            state = 0;
                            continue;
                        } else {
                            if v___x_3845_ == 0 {
                                v_init_3836_ = v___x_3842_;
                                v_x_3837_ = v_r_3841_;
                                state = 0;
                                continue;
                            } else {
                                v___x_3848_ = 0usize;
                                v___x_3849_ = lean_usize_of_nat(v___x_3844_);
                                v___x_3850_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__0(v_declName_3835_, v_v_3839_, v___x_3848_, v___x_3849_);
                                if v___x_3850_ == 0 {
                                    v_init_3836_ = v___x_3842_;
                                    v_x_3837_ = v_r_3841_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_inc(v_v_3839_);
                                    lean_inc(v_k_3838_);
                                    v___x_3852_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_3852_, 0, v_k_3838_);
                                    lean_ctor_set(v___x_3852_, 1, v_v_3839_);
                                    v___x_3853_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_3853_, 0, v___x_3852_);
                                    v_init_3836_ = v___x_3853_;
                                    v_x_3837_ = v_r_3841_;
                                    state = 0;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_init_3836_ = v___x_3842_;
                        v_x_3837_ = v_r_3841_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v_init_3836_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1___boxed(
    mut v_declName_3856_: *mut LeanObject,
    mut v_init_3857_: *mut LeanObject,
    mut v_x_3858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3859_: *mut LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(v_declName_3856_, v_init_3857_, v_x_3858_);
    lean_dec(v_x_3858_);
    lean_dec(v_declName_3856_);
    return v_res_3859_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvEvalState_erase(
    mut v_s_3860_: *mut LeanObject,
    mut v_declName_3861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lemmas_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v_fst_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: u8 = 0;
    let mut v___x_3895_: u8 = 0;
    let mut v___x_3896_: usize = 0;
    let mut v___x_3897_: usize = 0;
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: usize = 0;
    let mut v___x_3900_: usize = 0;
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lemmas_3862_ = lean_ctor_get(v_s_3860_, 0);
                v_entries_3863_ = lean_ctor_get(v_s_3860_, 1);
                v_isSharedCheck_3903_ = (!lean_is_exclusive(v_s_3860_)) as u8;
                if v_isSharedCheck_3903_ == 0 {
                    v___x_3865_ = v_s_3860_;
                    v_isShared_3866_ = v_isSharedCheck_3903_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_entries_3863_);
                    lean_inc(v_lemmas_3862_);
                    lean_dec(v_s_3860_);
                    v___x_3865_ = lean_box(0);
                    v_isShared_3866_ = v_isSharedCheck_3903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3867_ = lean_box(0);
                v___x_3868_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(v_declName_3861_, v___x_3867_, v_entries_3863_);
                if lean_obj_tag(v___x_3868_) == 0 {
                    lean_del_object(v___x_3865_);
                    lean_dec(v_entries_3863_);
                    lean_dec(v_lemmas_3862_);
                    return v___x_3867_;
                } else {
                    v_val_3869_ = lean_ctor_get(v___x_3868_, 0);
                    v_isSharedCheck_3902_ = (!lean_is_exclusive(v___x_3868_)) as u8;
                    if v_isSharedCheck_3902_ == 0 {
                        v___x_3871_ = v___x_3868_;
                        v_isShared_3872_ = v_isSharedCheck_3902_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3869_);
                        lean_dec(v___x_3868_);
                        v___x_3871_ = lean_box(0);
                        v_isShared_3872_ = v_isSharedCheck_3902_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3873_ = lean_ctor_get(v_val_3869_, 0);
                lean_inc(v_fst_3873_);
                v_snd_3874_ = lean_ctor_get(v_val_3869_, 1);
                lean_inc(v_snd_3874_);
                lean_dec(v_val_3869_);
                v___x_3891_ = lean_unsigned_to_nat(0);
                v___x_3892_ = lean_array_get_size(v_snd_3874_);
                v___x_3893_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0;
                v___x_3894_ = lean_nat_dec_lt(v___x_3891_, v___x_3892_);
                if v___x_3894_ == 0 {
                    lean_dec(v_snd_3874_);
                    v___y_3885_ = v___x_3893_;
                    state = 6;
                    continue;
                } else {
                    v___x_3895_ = lean_nat_dec_le(v___x_3892_, v___x_3892_);
                    if v___x_3895_ == 0 {
                        if v___x_3894_ == 0 {
                            lean_dec(v_snd_3874_);
                            v___y_3885_ = v___x_3893_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3896_ = 0usize;
                            v___x_3897_ = lean_usize_of_nat(v___x_3892_);
                            v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2(v_declName_3861_, v_snd_3874_, v___x_3896_, v___x_3897_, v___x_3893_);
                            lean_dec(v_snd_3874_);
                            v___y_3885_ = v___x_3898_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_3899_ = 0usize;
                        v___x_3900_ = lean_usize_of_nat(v___x_3892_);
                        v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2(v_declName_3861_, v_snd_3874_, v___x_3899_, v___x_3900_, v___x_3893_);
                        lean_dec(v_snd_3874_);
                        v___y_3885_ = v___x_3901_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3877_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas(v___y_3876_, v_fst_3873_, v_lemmas_3862_);
                if v_isShared_3866_ == 0 {
                    lean_ctor_set(v___x_3865_, 1, v___y_3876_);
                    lean_ctor_set(v___x_3865_, 0, v___x_3877_);
                    v___x_3879_ = v___x_3865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3877_);
                    lean_ctor_set(v_reuseFailAlloc_3883_, 1, v___y_3876_);
                    v___x_3879_ = v_reuseFailAlloc_3883_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3872_ == 0 {
                    lean_ctor_set(v___x_3871_, 0, v___x_3879_);
                    v___x_3881_ = v___x_3871_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
                    v___x_3881_ = v_reuseFailAlloc_3882_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3881_;
            }
            6 => {
                v___x_3886_ = lean_array_get_size(v___y_3885_);
                v___x_3887_ = lean_unsigned_to_nat(0);
                v___x_3888_ = lean_nat_dec_eq(v___x_3886_, v___x_3887_);
                if v___x_3888_ == 0 {
                    lean_inc(v_fst_3873_);
                    v___x_3889_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3873_, v___y_3885_, v_entries_3863_);
                    v___y_3876_ = v___x_3889_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v___y_3885_);
                    v___x_3890_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_fst_3873_, v_entries_3863_);
                    v___y_3876_ = v___x_3890_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvEvalState_erase___boxed(
    mut v_s_3904_: *mut LeanObject,
    mut v_declName_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3906_: *mut LeanObject = core::ptr::null_mut();
    v_res_3906_ = l_Lean_Meta_Tactic_Cbv_CbvEvalState_erase(v_s_3904_, v_declName_3905_);
    lean_dec(v_declName_3905_);
    return v_res_3906_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1(
    mut v_declName_3907_: *mut LeanObject,
    mut v_init_3908_: *mut LeanObject,
    mut v_t_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    v___x_3910_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(v_declName_3907_, v_init_3908_, v_t_3909_);
    return v___x_3910_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1___boxed(
    mut v_declName_3911_: *mut LeanObject,
    mut v_init_3912_: *mut LeanObject,
    mut v_t_3913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3914_: *mut LeanObject = core::ptr::null_mut();
    v_res_3914_ =
        l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1(
            v_declName_3911_,
            v_init_3912_,
            v_t_3913_,
        );
    lean_dec(v_t_3913_);
    lean_dec(v_declName_3911_);
    return v_res_3914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_(
    mut v_x_3917_: *mut LeanObject,
    mut v_entry_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_thm_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_unused_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut v_unused_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_thm_3919_ = lean_ctor_get(v_entry_3918_, 2);
                v___x_3920_ = l_Lean_Meta_Sym_Simp_Theorem_declName(v_thm_3919_);
                if lean_obj_tag(v___x_3920_) == 0 {
                    lean_dec_ref(v_entry_3918_);
                    v___x_3921_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_;
                    return v___x_3921_;
                } else {
                    v_val_3922_ = lean_ctor_get(v___x_3920_, 0);
                    v_isSharedCheck_3954_ = (!lean_is_exclusive(v___x_3920_)) as u8;
                    if v_isSharedCheck_3954_ == 0 {
                        v___x_3924_ = v___x_3920_;
                        v_isShared_3925_ = v_isSharedCheck_3954_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3922_);
                        lean_dec(v___x_3920_);
                        v___x_3924_ = lean_box(0);
                        v_isShared_3925_ = v_isSharedCheck_3954_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3926_ = l_Lean_isPrivateName(v_val_3922_);
                lean_dec(v_val_3922_);
                if v___x_3926_ == 0 {
                    lean_inc_ref(v_entry_3918_);
                    if v_isShared_3925_ == 0 {
                        lean_ctor_set(v___x_3924_, 0, v_entry_3918_);
                        v___x_3928_ = v___x_3924_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_entry_3918_);
                        v___x_3928_ = v_reuseFailAlloc_3939_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3940_ = lean_box(0);
                    lean_inc_ref(v_entry_3918_);
                    if v_isShared_3925_ == 0 {
                        lean_ctor_set(v___x_3924_, 0, v_entry_3918_);
                        v___x_3942_ = v___x_3924_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_entry_3918_);
                        v___x_3942_ = v_reuseFailAlloc_3953_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_isSharedCheck_3935_ = (!lean_is_exclusive(v_entry_3918_)) as u8;
                if v_isSharedCheck_3935_ == 0 {
                    v_unused_3936_ = lean_ctor_get(v_entry_3918_, 2);
                    lean_dec(v_unused_3936_);
                    v_unused_3937_ = lean_ctor_get(v_entry_3918_, 1);
                    lean_dec(v_unused_3937_);
                    v_unused_3938_ = lean_ctor_get(v_entry_3918_, 0);
                    lean_dec(v_unused_3938_);
                    v___x_3930_ = v_entry_3918_;
                    v_isShared_3931_ = v_isSharedCheck_3935_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_entry_3918_);
                    v___x_3930_ = lean_box(0);
                    v_isShared_3931_ = v_isSharedCheck_3935_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref_n(v___x_3928_, 2);
                if v_isShared_3931_ == 0 {
                    lean_ctor_set(v___x_3930_, 2, v___x_3928_);
                    lean_ctor_set(v___x_3930_, 1, v___x_3928_);
                    lean_ctor_set(v___x_3930_, 0, v___x_3928_);
                    v___x_3933_ = v___x_3930_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3928_);
                    lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3928_);
                    lean_ctor_set(v_reuseFailAlloc_3934_, 2, v___x_3928_);
                    v___x_3933_ = v_reuseFailAlloc_3934_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3933_;
            }
            5 => {
                v_isSharedCheck_3949_ = (!lean_is_exclusive(v_entry_3918_)) as u8;
                if v_isSharedCheck_3949_ == 0 {
                    v_unused_3950_ = lean_ctor_get(v_entry_3918_, 2);
                    lean_dec(v_unused_3950_);
                    v_unused_3951_ = lean_ctor_get(v_entry_3918_, 1);
                    lean_dec(v_unused_3951_);
                    v_unused_3952_ = lean_ctor_get(v_entry_3918_, 0);
                    lean_dec(v_unused_3952_);
                    v___x_3944_ = v_entry_3918_;
                    v_isShared_3945_ = v_isSharedCheck_3949_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_entry_3918_);
                    v___x_3944_ = lean_box(0);
                    v_isShared_3945_ = v_isSharedCheck_3949_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3945_ == 0 {
                    lean_ctor_set(v___x_3944_, 2, v___x_3942_);
                    lean_ctor_set(v___x_3944_, 1, v___x_3940_);
                    lean_ctor_set(v___x_3944_, 0, v___x_3940_);
                    v___x_3947_ = v___x_3944_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3940_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 1, v___x_3940_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 2, v___x_3942_);
                    v___x_3947_ = v_reuseFailAlloc_3948_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed(
    mut v_x_3955_: *mut LeanObject,
    mut v_entry_3956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3957_: *mut LeanObject = core::ptr::null_mut();
    v_res_3957_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_(v_x_3955_, v_entry_3956_);
    lean_dec_ref(v_x_3955_);
    return v_res_3957_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_(
    mut v___y_3958_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_3958_);
    return v___y_3958_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed(
    mut v___y_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3960_: *mut LeanObject = core::ptr::null_mut();
    v_res_3960_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_(v___y_3959_);
    lean_dec_ref(v___y_3959_);
    return v_res_3960_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    v___x_3974_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_;
    v___x_3975_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3974_);
    return v___x_3975_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed(
    mut v_a_3976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3977_: *mut LeanObject = core::ptr::null_mut();
    v_res_3977_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_();
    return v_res_3977_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(
    mut v_target_3978_: *mut LeanObject,
    mut v_a_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lemmas_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    v___x_3981_ = lean_st_ref_get(v_a_3979_);
    v_env_3982_ = lean_ctor_get(v___x_3981_, 0);
    lean_inc_ref(v_env_3982_);
    lean_dec(v___x_3981_);
    v___x_3983_ = l_Lean_Meta_Tactic_Cbv_cbvEvalExt;
    v_ext_3984_ = lean_ctor_get(v___x_3983_, 1);
    v_toEnvExtension_3985_ = lean_ctor_get(v_ext_3984_, 0);
    v_asyncMode_3986_ = lean_ctor_get(v_toEnvExtension_3985_, 2);
    v___x_3987_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default;
    v___x_3988_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_3987_,
        v___x_3983_,
        v_env_3982_,
        v_asyncMode_3986_,
    );
    v_lemmas_3989_ = lean_ctor_get(v___x_3988_, 0);
    lean_inc(v_lemmas_3989_);
    lean_dec(v___x_3988_);
    v___x_3990_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_lemmas_3989_,
            v_target_3978_,
        );
    lean_dec(v_lemmas_3989_);
    v___x_3991_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3991_, 0, v___x_3990_);
    return v___x_3991_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg___boxed(
    mut v_target_3992_: *mut LeanObject,
    mut v_a_3993_: *mut LeanObject,
    mut v_a_3994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3995_: *mut LeanObject = core::ptr::null_mut();
    v_res_3995_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_target_3992_, v_a_3993_);
    lean_dec(v_a_3993_);
    lean_dec(v_target_3992_);
    return v_res_3995_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas(
    mut v_target_3996_: *mut LeanObject,
    mut v_a_3997_: *mut LeanObject,
    mut v_a_3998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    v___x_4000_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_target_3996_, v_a_3998_);
    return v___x_4000_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___boxed(
    mut v_target_4001_: *mut LeanObject,
    mut v_a_4002_: *mut LeanObject,
    mut v_a_4003_: *mut LeanObject,
    mut v_a_4004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4005_: *mut LeanObject = core::ptr::null_mut();
    v_res_4005_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas(v_target_4001_, v_a_4002_, v_a_4003_);
    lean_dec(v_a_4003_);
    lean_dec_ref(v_a_4002_);
    lean_dec(v_target_4001_);
    return v_res_4005_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    v___x_4006_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4006_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    v___x_4007_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0);
    v___x_4008_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4008_, 0, v___x_4007_);
    return v___x_4008_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    v___x_4009_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1);
    v___x_4010_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4010_, 0, v___x_4009_);
    lean_ctor_set(v___x_4010_, 1, v___x_4009_);
    return v___x_4010_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg(
    mut v_ext_4011_: *mut LeanObject,
    mut v_b_4012_: *mut LeanObject,
    mut v_kind_4013_: u8,
    mut v___y_4014_: *mut LeanObject,
    mut v___y_4015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4029_: u8 = 0;
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v_unused_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_4017_ = lean_ctor_get(v___y_4014_, 6);
                v___x_4018_ = lean_st_ref_take(v___y_4015_);
                v_env_4019_ = lean_ctor_get(v___x_4018_, 0);
                v_nextMacroScope_4020_ = lean_ctor_get(v___x_4018_, 1);
                v_ngen_4021_ = lean_ctor_get(v___x_4018_, 2);
                v_auxDeclNGen_4022_ = lean_ctor_get(v___x_4018_, 3);
                v_traceState_4023_ = lean_ctor_get(v___x_4018_, 4);
                v_messages_4024_ = lean_ctor_get(v___x_4018_, 6);
                v_infoState_4025_ = lean_ctor_get(v___x_4018_, 7);
                v_snapshotTasks_4026_ = lean_ctor_get(v___x_4018_, 8);
                v_isSharedCheck_4038_ = (!lean_is_exclusive(v___x_4018_)) as u8;
                if v_isSharedCheck_4038_ == 0 {
                    v_unused_4039_ = lean_ctor_get(v___x_4018_, 5);
                    lean_dec(v_unused_4039_);
                    v___x_4028_ = v___x_4018_;
                    v_isShared_4029_ = v_isSharedCheck_4038_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4026_);
                    lean_inc(v_infoState_4025_);
                    lean_inc(v_messages_4024_);
                    lean_inc(v_traceState_4023_);
                    lean_inc(v_auxDeclNGen_4022_);
                    lean_inc(v_ngen_4021_);
                    lean_inc(v_nextMacroScope_4020_);
                    lean_inc(v_env_4019_);
                    lean_dec(v___x_4018_);
                    v___x_4028_ = lean_box(0);
                    v_isShared_4029_ = v_isSharedCheck_4038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_4017_);
                v___x_4030_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_4019_,
                    v_ext_4011_,
                    v_b_4012_,
                    v_kind_4013_,
                    v_currNamespace_4017_,
                );
                v___x_4031_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2);
                if v_isShared_4029_ == 0 {
                    lean_ctor_set(v___x_4028_, 5, v___x_4031_);
                    lean_ctor_set(v___x_4028_, 0, v___x_4030_);
                    v___x_4033_ = v___x_4028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4030_);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 1, v_nextMacroScope_4020_);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 2, v_ngen_4021_);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 3, v_auxDeclNGen_4022_);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 4, v_traceState_4023_);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 5, v___x_4031_);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 6, v_messages_4024_);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 7, v_infoState_4025_);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 8, v_snapshotTasks_4026_);
                    v___x_4033_ = v_reuseFailAlloc_4037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4034_ = lean_st_ref_set(v___y_4015_, v___x_4033_);
                v___x_4035_ = lean_box(0);
                v___x_4036_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4036_, 0, v___x_4035_);
                return v___x_4036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_ext_4040_: *mut LeanObject,
    mut v_b_4041_: *mut LeanObject,
    mut v_kind_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4046_: u8 = 0;
    let mut v_res_4047_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4046_ = (lean_unbox(v_kind_4042_) as u8);
    v_res_4047_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg(v_ext_4040_, v_b_4041_, v_kind_boxed_4046_, v___y_4043_, v___y_4044_);
    lean_dec(v___y_4044_);
    lean_dec_ref(v___y_4043_);
    return v_res_4047_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_4048_: *mut LeanObject,
    mut v_00_u03b2_4049_: *mut LeanObject,
    mut v_00_u03c3_4050_: *mut LeanObject,
    mut v_ext_4051_: *mut LeanObject,
    mut v_b_4052_: *mut LeanObject,
    mut v_kind_4053_: u8,
    mut v___y_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    v___x_4057_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg(v_ext_4051_, v_b_4052_, v_kind_4053_, v___y_4054_, v___y_4055_);
    return v___x_4057_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_4058_: *mut LeanObject,
    mut v_00_u03b2_4059_: *mut LeanObject,
    mut v_00_u03c3_4060_: *mut LeanObject,
    mut v_ext_4061_: *mut LeanObject,
    mut v_b_4062_: *mut LeanObject,
    mut v_kind_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4067_: u8 = 0;
    let mut v_res_4068_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4067_ = (lean_unbox(v_kind_4063_) as u8);
    v_res_4068_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0(v_00_u03b1_4058_, v_00_u03b2_4059_, v_00_u03c3_4060_, v_ext_4061_, v_b_4062_, v_kind_boxed_4067_, v___y_4064_, v___y_4065_);
    lean_dec(v___y_4065_);
    lean_dec_ref(v___y_4064_);
    return v_res_4068_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u64 = 0;
    v___x_4075_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
    v___x_4076_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4075_);
    return v___x_4076_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4077_: u64 = 0;
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    v___x_4077_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4078_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
    v___x_4079_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_4079_, 0, v___x_4078_);
    lean_ctor_set_uint64(
        v___x_4079_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4077_,
    );
    return v___x_4079_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    v___x_4080_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4080_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    v___x_4081_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4082_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4082_, 0, v___x_4081_);
    return v___x_4082_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    v___x_4083_ = lean_box(1);
    v___x_4084_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4);
    v___x_4085_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4086_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4086_, 0, v___x_4085_);
    lean_ctor_set(v___x_4086_, 1, v___x_4084_);
    lean_ctor_set(v___x_4086_, 2, v___x_4083_);
    return v___x_4086_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    v___x_4089_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4090_ = lean_unsigned_to_nat(0);
    v___x_4091_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4091_, 0, v___x_4090_);
    lean_ctor_set(v___x_4091_, 1, v___x_4090_);
    lean_ctor_set(v___x_4091_, 2, v___x_4090_);
    lean_ctor_set(v___x_4091_, 3, v___x_4090_);
    lean_ctor_set(v___x_4091_, 4, v___x_4089_);
    lean_ctor_set(v___x_4091_, 5, v___x_4089_);
    lean_ctor_set(v___x_4091_, 6, v___x_4089_);
    lean_ctor_set(v___x_4091_, 7, v___x_4089_);
    lean_ctor_set(v___x_4091_, 8, v___x_4089_);
    lean_ctor_set(v___x_4091_, 9, v___x_4089_);
    return v___x_4091_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    v___x_4092_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4093_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4093_, 0, v___x_4092_);
    lean_ctor_set(v___x_4093_, 1, v___x_4092_);
    lean_ctor_set(v___x_4093_, 2, v___x_4092_);
    lean_ctor_set(v___x_4093_, 3, v___x_4092_);
    lean_ctor_set(v___x_4093_, 4, v___x_4092_);
    lean_ctor_set(v___x_4093_, 5, v___x_4092_);
    return v___x_4093_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    v___x_4094_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4095_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4095_, 0, v___x_4094_);
    lean_ctor_set(v___x_4095_, 1, v___x_4094_);
    lean_ctor_set(v___x_4095_, 2, v___x_4094_);
    lean_ctor_set(v___x_4095_, 3, v___x_4094_);
    lean_ctor_set(v___x_4095_, 4, v___x_4094_);
    return v___x_4095_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(
    mut v___x_4096_: *mut LeanObject,
    mut v_lemmaName_4097_: *mut LeanObject,
    mut v_stx_4098_: *mut LeanObject,
    mut v_kind_4099_: u8,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4104_: u8 = 0;
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4127_: u8 = 0;
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4131_: u8 = 0;
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u8 = 0;
    let mut v___x_4135_: u8 = 0;
    let mut v___x_4136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4132_ = lean_unsigned_to_nat(1);
                v___x_4133_ = l_Lean_Syntax_getArg(v_stx_4098_, v___x_4132_);
                v___x_4134_ = l_Lean_Syntax_isNone(v___x_4133_);
                lean_dec(v___x_4133_);
                if v___x_4134_ == 0 {
                    v___x_4135_ = 1;
                    v___y_4104_ = v___x_4135_;
                    state = 1;
                    continue;
                } else {
                    v___x_4136_ = 0;
                    v___y_4104_ = v___x_4136_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4105_ = 0;
                v___x_4106_ = 1;
                v___x_4107_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4108_ = lean_unsigned_to_nat(0);
                v___x_4109_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4);
                v___x_4110_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4111_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
                v___x_4112_ = lean_box(0);
                lean_inc(v___x_4096_);
                v___x_4113_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4113_, 0, v___x_4107_);
                lean_ctor_set(v___x_4113_, 1, v___x_4096_);
                lean_ctor_set(v___x_4113_, 2, v___x_4110_);
                lean_ctor_set(v___x_4113_, 3, v___x_4111_);
                lean_ctor_set(v___x_4113_, 4, v___x_4112_);
                lean_ctor_set(v___x_4113_, 5, v___x_4108_);
                lean_ctor_set(v___x_4113_, 6, v___x_4112_);
                lean_ctor_set_uint8(
                    v___x_4113_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_4105_,
                );
                lean_ctor_set_uint8(
                    v___x_4113_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_4105_,
                );
                lean_ctor_set_uint8(
                    v___x_4113_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_4105_,
                );
                lean_ctor_set_uint8(
                    v___x_4113_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_4106_,
                );
                v___x_4114_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4115_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4116_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4117_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_4117_, 0, v___x_4114_);
                lean_ctor_set(v___x_4117_, 1, v___x_4115_);
                lean_ctor_set(v___x_4117_, 2, v___x_4096_);
                lean_ctor_set(v___x_4117_, 3, v___x_4109_);
                lean_ctor_set(v___x_4117_, 4, v___x_4116_);
                v___x_4118_ = lean_st_mk_ref(v___x_4117_);
                v___x_4119_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst(
                    v_lemmaName_4097_,
                    v___y_4104_,
                    v___x_4113_,
                    v___x_4118_,
                    v___y_4100_,
                    v___y_4101_,
                );
                lean_dec_ref_known(v___x_4113_, 7);
                if lean_obj_tag(v___x_4119_) == 0 {
                    v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
                    lean_inc(v_a_4120_);
                    lean_dec_ref_known(v___x_4119_, 1);
                    v___x_4121_ = lean_st_ref_get(v___x_4118_);
                    lean_dec(v___x_4118_);
                    lean_dec(v___x_4121_);
                    v___x_4122_ = l_Lean_Meta_Tactic_Cbv_cbvEvalExt;
                    v___x_4123_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg(v___x_4122_, v_a_4120_, v_kind_4099_, v___y_4100_, v___y_4101_);
                    return v___x_4123_;
                } else {
                    lean_dec(v___x_4118_);
                    v_a_4124_ = lean_ctor_get(v___x_4119_, 0);
                    v_isSharedCheck_4131_ = (!lean_is_exclusive(v___x_4119_)) as u8;
                    if v_isSharedCheck_4131_ == 0 {
                        v___x_4126_ = v___x_4119_;
                        v_isShared_4127_ = v_isSharedCheck_4131_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4124_);
                        lean_dec(v___x_4119_);
                        v___x_4126_ = lean_box(0);
                        v_isShared_4127_ = v_isSharedCheck_4131_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4127_ == 0 {
                    v___x_4129_ = v___x_4126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
                    v___x_4129_ = v_reuseFailAlloc_4130_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed(
    mut v___x_4137_: *mut LeanObject,
    mut v_lemmaName_4138_: *mut LeanObject,
    mut v_stx_4139_: *mut LeanObject,
    mut v_kind_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4144_: u8 = 0;
    let mut v_res_4145_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4144_ = (lean_unbox(v_kind_4140_) as u8);
    v_res_4145_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(v___x_4137_, v_lemmaName_4138_, v_stx_4139_, v_kind_boxed_4144_, v___y_4141_, v___y_4142_);
    lean_dec(v___y_4142_);
    lean_dec_ref(v___y_4141_);
    lean_dec(v_stx_4139_);
    return v_res_4145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(
    mut v_val_4146_: *mut LeanObject,
    mut v_x_4147_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_val_4146_);
    return v_val_4146_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed(
    mut v_val_4148_: *mut LeanObject,
    mut v_x_4149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4150_: *mut LeanObject = core::ptr::null_mut();
    v_res_4150_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(v_val_4148_, v_x_4149_);
    lean_dec_ref(v_x_4149_);
    lean_dec_ref(v_val_4148_);
    return v_res_4150_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(
    mut v_msgData_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
    mut v___y_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    v___x_4155_ = lean_st_ref_get(v___y_4153_);
    v_env_4156_ = lean_ctor_get(v___x_4155_, 0);
    lean_inc_ref(v_env_4156_);
    lean_dec(v___x_4155_);
    v_options_4157_ = lean_ctor_get(v___y_4152_, 2);
    v___x_4158_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2);
    v___x_4159_ = lean_unsigned_to_nat(32);
    v___x_4160_ = lean_mk_empty_array_with_capacity(v___x_4159_);
    lean_dec_ref(v___x_4160_);
    v___x_4161_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5);
    lean_inc_ref(v_options_4157_);
    v___x_4162_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4162_, 0, v_env_4156_);
    lean_ctor_set(v___x_4162_, 1, v___x_4158_);
    lean_ctor_set(v___x_4162_, 2, v___x_4161_);
    lean_ctor_set(v___x_4162_, 3, v_options_4157_);
    v___x_4163_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4163_, 0, v___x_4162_);
    lean_ctor_set(v___x_4163_, 1, v_msgData_4151_);
    v___x_4164_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4164_, 0, v___x_4163_);
    return v___x_4164_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_msgData_4165_: *mut LeanObject,
    mut v___y_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4169_: *mut LeanObject = core::ptr::null_mut();
    v_res_4169_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(v_msgData_4165_, v___y_4166_, v___y_4167_);
    lean_dec(v___y_4167_);
    lean_dec_ref(v___y_4166_);
    return v_res_4169_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0(
    mut v___y_4178_: u8,
    mut v_suppressElabErrors_4179_: u8,
    mut v_x_4180_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4180_) == 1 {
        let mut v_pre_4181_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4181_ = lean_ctor_get(v_x_4180_, 0);
        match lean_obj_tag(v_pre_4181_) {
            1 => {
                let mut v_pre_4182_: *mut LeanObject = core::ptr::null_mut();
                v_pre_4182_ = lean_ctor_get(v_pre_4181_, 0);
                match lean_obj_tag(v_pre_4182_) {
                    0 => {
                        let mut v_str_4183_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_4184_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4186_: u8 = 0;
                        v_str_4183_ = lean_ctor_get(v_x_4180_, 1);
                        v_str_4184_ = lean_ctor_get(v_pre_4181_, 1);
                        v___x_4185_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__0;
                        v___x_4186_ = lean_string_dec_eq(v_str_4184_, v___x_4185_);
                        if v___x_4186_ == 0 {
                            let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4188_: u8 = 0;
                            v___x_4187_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__1;
                            v___x_4188_ = lean_string_dec_eq(v_str_4184_, v___x_4187_);
                            if v___x_4188_ == 0 {
                                return v___y_4178_;
                            } else {
                                let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4190_: u8 = 0;
                                v___x_4189_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__2;
                                v___x_4190_ = lean_string_dec_eq(v_str_4183_, v___x_4189_);
                                if v___x_4190_ == 0 {
                                    return v___y_4178_;
                                } else {
                                    return v_suppressElabErrors_4179_;
                                }
                            }
                        } else {
                            let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4192_: u8 = 0;
                            v___x_4191_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__3;
                            v___x_4192_ = lean_string_dec_eq(v_str_4183_, v___x_4191_);
                            if v___x_4192_ == 0 {
                                return v___y_4178_;
                            } else {
                                return v_suppressElabErrors_4179_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4193_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_4193_ = lean_ctor_get(v_pre_4182_, 0);
                        if lean_obj_tag(v_pre_4193_) == 0 {
                            let mut v_str_4194_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4195_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4196_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4198_: u8 = 0;
                            v_str_4194_ = lean_ctor_get(v_x_4180_, 1);
                            v_str_4195_ = lean_ctor_get(v_pre_4181_, 1);
                            v_str_4196_ = lean_ctor_get(v_pre_4182_, 1);
                            v___x_4197_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__4;
                            v___x_4198_ = lean_string_dec_eq(v_str_4196_, v___x_4197_);
                            if v___x_4198_ == 0 {
                                return v___y_4178_;
                            } else {
                                let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4200_: u8 = 0;
                                v___x_4199_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__5;
                                v___x_4200_ = lean_string_dec_eq(v_str_4195_, v___x_4199_);
                                if v___x_4200_ == 0 {
                                    return v___y_4178_;
                                } else {
                                    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_4202_: u8 = 0;
                                    v___x_4201_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__6;
                                    v___x_4202_ = lean_string_dec_eq(v_str_4194_, v___x_4201_);
                                    if v___x_4202_ == 0 {
                                        return v___y_4178_;
                                    } else {
                                        return v_suppressElabErrors_4179_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4178_;
                        }
                    }
                    _ => {
                        return v___y_4178_;
                    }
                }
            }
            0 => {
                let mut v_str_4203_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4205_: u8 = 0;
                v_str_4203_ = lean_ctor_get(v_x_4180_, 1);
                v___x_4204_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__7;
                v___x_4205_ = lean_string_dec_eq(v_str_4203_, v___x_4204_);
                if v___x_4205_ == 0 {
                    return v___y_4178_;
                } else {
                    return v_suppressElabErrors_4179_;
                }
            }
            _ => {
                return v___y_4178_;
            }
        }
    } else {
        return v___y_4178_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___boxed(
    mut v___y_4206_: *mut LeanObject,
    mut v_suppressElabErrors_4207_: *mut LeanObject,
    mut v_x_4208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3876__boxed_4209_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4210_: u8 = 0;
    let mut v_res_4211_: u8 = 0;
    let mut v_r_4212_: *mut LeanObject = core::ptr::null_mut();
    v___y_3876__boxed_4209_ = (lean_unbox(v___y_4206_) as u8);
    v_suppressElabErrors_boxed_4210_ = (lean_unbox(v_suppressElabErrors_4207_) as u8);
    v_res_4211_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0(v___y_3876__boxed_4209_, v_suppressElabErrors_boxed_4210_, v_x_4208_);
    lean_dec(v_x_4208_);
    v_r_4212_ = lean_box((v_res_4211_) as usize);
    return v_r_4212_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(
    mut v_opts_4213_: *mut LeanObject,
    mut v_opt_4214_: *mut LeanObject,
) -> u8 {
    let mut v_name_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    v_name_4215_ = lean_ctor_get(v_opt_4214_, 0);
    v_defValue_4216_ = lean_ctor_get(v_opt_4214_, 1);
    v_map_4217_ = lean_ctor_get(v_opts_4213_, 0);
    v___x_4218_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4217_,
            v_name_4215_,
        );
    if lean_obj_tag(v___x_4218_) == 0 {
        let mut v___x_4219_: u8 = 0;
        v___x_4219_ = (lean_unbox(v_defValue_4216_) as u8);
        return v___x_4219_;
    } else {
        let mut v_val_4220_: *mut LeanObject = core::ptr::null_mut();
        v_val_4220_ = lean_ctor_get(v___x_4218_, 0);
        lean_inc(v_val_4220_);
        lean_dec_ref_known(v___x_4218_, 1);
        if lean_obj_tag(v_val_4220_) == 1 {
            let mut v_v_4221_: u8 = 0;
            v_v_4221_ = lean_ctor_get_uint8(v_val_4220_, 0 as u32);
            lean_dec_ref_known(v_val_4220_, 0);
            return v_v_4221_;
        } else {
            let mut v___x_4222_: u8 = 0;
            lean_dec(v_val_4220_);
            v___x_4222_ = (lean_unbox(v_defValue_4216_) as u8);
            return v___x_4222_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_opts_4223_: *mut LeanObject,
    mut v_opt_4224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4225_: u8 = 0;
    let mut v_r_4226_: *mut LeanObject = core::ptr::null_mut();
    v_res_4225_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_opts_4223_, v_opt_4224_);
    lean_dec_ref(v_opt_4224_);
    lean_dec_ref(v_opts_4223_);
    v_r_4226_ = lean_box((v_res_4225_) as usize);
    return v_r_4226_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2(
    mut v_ref_4228_: *mut LeanObject,
    mut v_msgData_4229_: *mut LeanObject,
    mut v_severity_4230_: u8,
    mut v_isSilent_4231_: u8,
    mut v___y_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4236_: u8 = 0;
    let mut v___y_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: u8 = 0;
    let mut v___y_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4259_: u8 = 0;
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v___y_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: u8 = 0;
    let mut v___y_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4276_: u8 = 0;
    let mut v___y_4277_: u8 = 0;
    let mut v___y_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4285_: u8 = 0;
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4295_: u8 = 0;
    let mut v___y_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4299_: u8 = 0;
    let mut v___y_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4301_: u8 = 0;
    let mut v___y_4302_: u8 = 0;
    let mut v___y_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: u8 = 0;
    let mut v___y_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: u8 = 0;
    let mut v___y_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: u8 = 0;
    let mut v_ref_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    let mut v___y_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4323_: u8 = 0;
    let mut v___y_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: u8 = 0;
    let mut v___y_4327_: u8 = 0;
    let mut v___y_4329_: u8 = 0;
    let mut v_fileName_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4334_: u8 = 0;
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: u8 = 0;
    let mut v___x_4339_: u8 = 0;
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: u8 = 0;
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: u8 = 0;
    let mut v___x_4345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4319_ = 2;
                v___x_4344_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4230_, v___x_4319_);
                if v___x_4344_ == 0 {
                    v___y_4329_ = v___x_4344_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_4229_);
                    v___x_4345_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4229_);
                    v___y_4329_ = v___x_4345_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4245_ = lean_st_ref_take(v___y_4244_);
                v_currNamespace_4246_ = lean_ctor_get(v___y_4243_, 6);
                v_openDecls_4247_ = lean_ctor_get(v___y_4243_, 7);
                v_env_4248_ = lean_ctor_get(v___x_4245_, 0);
                v_nextMacroScope_4249_ = lean_ctor_get(v___x_4245_, 1);
                v_ngen_4250_ = lean_ctor_get(v___x_4245_, 2);
                v_auxDeclNGen_4251_ = lean_ctor_get(v___x_4245_, 3);
                v_traceState_4252_ = lean_ctor_get(v___x_4245_, 4);
                v_cache_4253_ = lean_ctor_get(v___x_4245_, 5);
                v_messages_4254_ = lean_ctor_get(v___x_4245_, 6);
                v_infoState_4255_ = lean_ctor_get(v___x_4245_, 7);
                v_snapshotTasks_4256_ = lean_ctor_get(v___x_4245_, 8);
                v_isSharedCheck_4270_ = (!lean_is_exclusive(v___x_4245_)) as u8;
                if v_isSharedCheck_4270_ == 0 {
                    v___x_4258_ = v___x_4245_;
                    v_isShared_4259_ = v_isSharedCheck_4270_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4256_);
                    lean_inc(v_infoState_4255_);
                    lean_inc(v_messages_4254_);
                    lean_inc(v_cache_4253_);
                    lean_inc(v_traceState_4252_);
                    lean_inc(v_auxDeclNGen_4251_);
                    lean_inc(v_ngen_4250_);
                    lean_inc(v_nextMacroScope_4249_);
                    lean_inc(v_env_4248_);
                    lean_dec(v___x_4245_);
                    v___x_4258_ = lean_box(0);
                    v_isShared_4259_ = v_isSharedCheck_4270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_4247_);
                lean_inc(v_currNamespace_4246_);
                v___x_4260_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4260_, 0, v_currNamespace_4246_);
                lean_ctor_set(v___x_4260_, 1, v_openDecls_4247_);
                v___x_4261_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4261_, 0, v___x_4260_);
                lean_ctor_set(v___x_4261_, 1, v___y_4242_);
                lean_inc_ref(v___y_4238_);
                lean_inc_ref(v___y_4241_);
                v___x_4262_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_4262_, 0, v___y_4241_);
                lean_ctor_set(v___x_4262_, 1, v___y_4240_);
                lean_ctor_set(v___x_4262_, 2, v___y_4237_);
                lean_ctor_set(v___x_4262_, 3, v___y_4238_);
                lean_ctor_set(v___x_4262_, 4, v___x_4261_);
                lean_ctor_set_uint8(
                    v___x_4262_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_4236_,
                );
                lean_ctor_set_uint8(
                    v___x_4262_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_4239_,
                );
                lean_ctor_set_uint8(
                    v___x_4262_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4231_,
                );
                v___x_4263_ = l_Lean_MessageLog_add(v___x_4262_, v_messages_4254_);
                if v_isShared_4259_ == 0 {
                    lean_ctor_set(v___x_4258_, 6, v___x_4263_);
                    v___x_4265_ = v___x_4258_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_env_4248_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_nextMacroScope_4249_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 2, v_ngen_4250_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 3, v_auxDeclNGen_4251_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 4, v_traceState_4252_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 5, v_cache_4253_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 6, v___x_4263_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 7, v_infoState_4255_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 8, v_snapshotTasks_4256_);
                    v___x_4265_ = v_reuseFailAlloc_4269_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4266_ = lean_st_ref_set(v___y_4244_, v___x_4265_);
                v___x_4267_ = lean_box(0);
                v___x_4268_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4268_, 0, v___x_4267_);
                return v___x_4268_;
            }
            4 => {
                v___x_4280_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4229_,
                    );
                v___x_4281_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(v___x_4280_, v___y_4232_, v___y_4233_);
                v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
                v_isSharedCheck_4295_ = (!lean_is_exclusive(v___x_4281_)) as u8;
                if v_isSharedCheck_4295_ == 0 {
                    v___x_4284_ = v___x_4281_;
                    v_isShared_4285_ = v_isSharedCheck_4295_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_4282_);
                    lean_dec(v___x_4281_);
                    v___x_4284_ = lean_box(0);
                    v_isShared_4285_ = v_isSharedCheck_4295_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_4274_, 2);
                v___x_4286_ = l_Lean_FileMap_toPosition(v___y_4274_, v___y_4275_);
                lean_dec(v___y_4275_);
                v___x_4287_ = l_Lean_FileMap_toPosition(v___y_4274_, v___y_4279_);
                lean_dec(v___y_4279_);
                v___x_4288_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4288_, 0, v___x_4287_);
                v___x_4289_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___closed__0;
                if v___y_4277_ == 0 {
                    lean_del_object(v___x_4284_);
                    lean_dec_ref(v___y_4272_);
                    v___y_4236_ = v___y_4273_;
                    v___y_4237_ = v___x_4288_;
                    v___y_4238_ = v___x_4289_;
                    v___y_4239_ = v___y_4276_;
                    v___y_4240_ = v___x_4286_;
                    v___y_4241_ = v___y_4278_;
                    v___y_4242_ = v_a_4282_;
                    v___y_4243_ = v___y_4232_;
                    v___y_4244_ = v___y_4233_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4282_);
                    v___x_4290_ = l_Lean_MessageData_hasTag(v___y_4272_, v_a_4282_);
                    if v___x_4290_ == 0 {
                        lean_dec_ref_known(v___x_4288_, 1);
                        lean_dec_ref(v___x_4286_);
                        lean_dec(v_a_4282_);
                        v___x_4291_ = lean_box(0);
                        if v_isShared_4285_ == 0 {
                            lean_ctor_set(v___x_4284_, 0, v___x_4291_);
                            v___x_4293_ = v___x_4284_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4291_);
                            v___x_4293_ = v_reuseFailAlloc_4294_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4284_);
                        v___y_4236_ = v___y_4273_;
                        v___y_4237_ = v___x_4288_;
                        v___y_4238_ = v___x_4289_;
                        v___y_4239_ = v___y_4276_;
                        v___y_4240_ = v___x_4286_;
                        v___y_4241_ = v___y_4278_;
                        v___y_4242_ = v_a_4282_;
                        v___y_4243_ = v___y_4232_;
                        v___y_4244_ = v___y_4233_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4293_;
            }
            7 => {
                v___x_4305_ = l_Lean_Syntax_getTailPos_x3f(v___y_4298_, v___y_4299_);
                lean_dec(v___y_4298_);
                if lean_obj_tag(v___x_4305_) == 0 {
                    lean_inc(v___y_4304_);
                    v___y_4272_ = v___y_4297_;
                    v___y_4273_ = v___y_4299_;
                    v___y_4274_ = v___y_4300_;
                    v___y_4275_ = v___y_4304_;
                    v___y_4276_ = v___y_4301_;
                    v___y_4277_ = v___y_4302_;
                    v___y_4278_ = v___y_4303_;
                    v___y_4279_ = v___y_4304_;
                    state = 4;
                    continue;
                } else {
                    v_val_4306_ = lean_ctor_get(v___x_4305_, 0);
                    lean_inc(v_val_4306_);
                    lean_dec_ref_known(v___x_4305_, 1);
                    v___y_4272_ = v___y_4297_;
                    v___y_4273_ = v___y_4299_;
                    v___y_4274_ = v___y_4300_;
                    v___y_4275_ = v___y_4304_;
                    v___y_4276_ = v___y_4301_;
                    v___y_4277_ = v___y_4302_;
                    v___y_4278_ = v___y_4303_;
                    v___y_4279_ = v_val_4306_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4315_ = l_Lean_replaceRef(v_ref_4228_, v___y_4313_);
                v___x_4316_ = l_Lean_Syntax_getPos_x3f(v_ref_4315_, v___y_4309_);
                if lean_obj_tag(v___x_4316_) == 0 {
                    v___x_4317_ = lean_unsigned_to_nat(0);
                    v___y_4297_ = v___y_4308_;
                    v___y_4298_ = v_ref_4315_;
                    v___y_4299_ = v___y_4309_;
                    v___y_4300_ = v___y_4310_;
                    v___y_4301_ = v___y_4314_;
                    v___y_4302_ = v___y_4311_;
                    v___y_4303_ = v___y_4312_;
                    v___y_4304_ = v___x_4317_;
                    state = 7;
                    continue;
                } else {
                    v_val_4318_ = lean_ctor_get(v___x_4316_, 0);
                    lean_inc(v_val_4318_);
                    lean_dec_ref_known(v___x_4316_, 1);
                    v___y_4297_ = v___y_4308_;
                    v___y_4298_ = v_ref_4315_;
                    v___y_4299_ = v___y_4309_;
                    v___y_4300_ = v___y_4310_;
                    v___y_4301_ = v___y_4314_;
                    v___y_4302_ = v___y_4311_;
                    v___y_4303_ = v___y_4312_;
                    v___y_4304_ = v_val_4318_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4327_ == 0 {
                    v___y_4308_ = v___y_4321_;
                    v___y_4309_ = v___y_4326_;
                    v___y_4310_ = v___y_4322_;
                    v___y_4311_ = v___y_4323_;
                    v___y_4312_ = v___y_4324_;
                    v___y_4313_ = v___y_4325_;
                    v___y_4314_ = v_severity_4230_;
                    state = 8;
                    continue;
                } else {
                    v___y_4308_ = v___y_4321_;
                    v___y_4309_ = v___y_4326_;
                    v___y_4310_ = v___y_4322_;
                    v___y_4311_ = v___y_4323_;
                    v___y_4312_ = v___y_4324_;
                    v___y_4313_ = v___y_4325_;
                    v___y_4314_ = v___x_4319_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4329_ == 0 {
                    v_fileName_4330_ = lean_ctor_get(v___y_4232_, 0);
                    v_fileMap_4331_ = lean_ctor_get(v___y_4232_, 1);
                    v_options_4332_ = lean_ctor_get(v___y_4232_, 2);
                    v_ref_4333_ = lean_ctor_get(v___y_4232_, 5);
                    v_suppressElabErrors_4334_ = lean_ctor_get_uint8(
                        v___y_4232_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4335_ = lean_box((v___y_4329_) as usize);
                    v___x_4336_ = lean_box((v_suppressElabErrors_4334_) as usize);
                    v___f_4337_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_4337_, 0, v___x_4335_);
                    lean_closure_set(v___f_4337_, 1, v___x_4336_);
                    v___x_4338_ = 1;
                    v___x_4339_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4230_, v___x_4338_);
                    if v___x_4339_ == 0 {
                        v___y_4321_ = v___f_4337_;
                        v___y_4322_ = v_fileMap_4331_;
                        v___y_4323_ = v_suppressElabErrors_4334_;
                        v___y_4324_ = v_fileName_4330_;
                        v___y_4325_ = v_ref_4333_;
                        v___y_4326_ = v___y_4329_;
                        v___y_4327_ = v___x_4339_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4340_ = l_Lean_warningAsError;
                        v___x_4341_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_options_4332_, v___x_4340_);
                        v___y_4321_ = v___f_4337_;
                        v___y_4322_ = v_fileMap_4331_;
                        v___y_4323_ = v_suppressElabErrors_4334_;
                        v___y_4324_ = v_fileName_4330_;
                        v___y_4325_ = v_ref_4333_;
                        v___y_4326_ = v___y_4329_;
                        v___y_4327_ = v___x_4341_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_4229_);
                    v___x_4342_ = lean_box(0);
                    v___x_4343_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4343_, 0, v___x_4342_);
                    return v___x_4343_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(
    mut v_ref_4346_: *mut LeanObject,
    mut v_msgData_4347_: *mut LeanObject,
    mut v_severity_4348_: *mut LeanObject,
    mut v_isSilent_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4353_: u8 = 0;
    let mut v_isSilent_boxed_4354_: u8 = 0;
    let mut v_res_4355_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4353_ = (lean_unbox(v_severity_4348_) as u8);
    v_isSilent_boxed_4354_ = (lean_unbox(v_isSilent_4349_) as u8);
    v_res_4355_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_ref_4346_, v_msgData_4347_, v_severity_boxed_4353_, v_isSilent_boxed_4354_, v___y_4350_, v___y_4351_);
    lean_dec(v___y_4351_);
    lean_dec_ref(v___y_4350_);
    lean_dec(v_ref_4346_);
    return v_res_4355_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1(
    mut v_msgData_4356_: *mut LeanObject,
    mut v_severity_4357_: u8,
    mut v_isSilent_4358_: u8,
    mut v___y_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4362_ = lean_ctor_get(v___y_4359_, 5);
    v___x_4363_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_ref_4362_, v_msgData_4356_, v_severity_4357_, v_isSilent_4358_, v___y_4359_, v___y_4360_);
    return v___x_4363_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_msgData_4364_: *mut LeanObject,
    mut v_severity_4365_: *mut LeanObject,
    mut v_isSilent_4366_: *mut LeanObject,
    mut v___y_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4370_: u8 = 0;
    let mut v_isSilent_boxed_4371_: u8 = 0;
    let mut v_res_4372_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4370_ = (lean_unbox(v_severity_4365_) as u8);
    v_isSilent_boxed_4371_ = (lean_unbox(v_isSilent_4366_) as u8);
    v_res_4372_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1(v_msgData_4364_, v_severity_boxed_4370_, v_isSilent_boxed_4371_, v___y_4367_, v___y_4368_);
    lean_dec(v___y_4368_);
    lean_dec_ref(v___y_4367_);
    return v_res_4372_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1(
    mut v_msgData_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4377_: u8 = 0;
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    v___x_4377_ = 1;
    v___x_4378_ = 0;
    v___x_4379_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1(v_msgData_4373_, v___x_4377_, v___x_4378_, v___y_4374_, v___y_4375_);
    return v___x_4379_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1___boxed(
    mut v_msgData_4380_: *mut LeanObject,
    mut v___y_4381_: *mut LeanObject,
    mut v___y_4382_: *mut LeanObject,
    mut v___y_4383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4384_: *mut LeanObject = core::ptr::null_mut();
    v_res_4384_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1(v_msgData_4380_, v___y_4381_, v___y_4382_);
    lean_dec(v___y_4382_);
    lean_dec_ref(v___y_4381_);
    return v_res_4384_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    v___x_4386_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
    v___x_4387_ = l_Lean_stringToMessageData(v___x_4386_);
    return v___x_4387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(
    mut v___x_4388_: *mut LeanObject,
    mut v_declName_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4411_: u8 = 0;
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4423_: u8 = 0;
    let mut v___f_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut v_unused_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4393_ = lean_st_ref_get(v___y_4391_);
                v_env_4394_ = lean_ctor_get(v___x_4393_, 0);
                lean_inc_ref(v_env_4394_);
                lean_dec(v___x_4393_);
                v___x_4395_ = l_Lean_Meta_Tactic_Cbv_cbvEvalExt;
                v_ext_4396_ = lean_ctor_get(v___x_4395_, 1);
                v_toEnvExtension_4397_ = lean_ctor_get(v_ext_4396_, 0);
                v_asyncMode_4398_ = lean_ctor_get(v_toEnvExtension_4397_, 2);
                v___x_4399_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_4388_,
                    v___x_4395_,
                    v_env_4394_,
                    v_asyncMode_4398_,
                );
                v___x_4400_ =
                    l_Lean_Meta_Tactic_Cbv_CbvEvalState_erase(v___x_4399_, v_declName_4389_);
                if lean_obj_tag(v___x_4400_) == 0 {
                    v___x_4401_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3);
                    v___x_4402_ = 0;
                    v___x_4403_ = l_Lean_MessageData_ofConstName(v_declName_4389_, v___x_4402_);
                    v___x_4404_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4404_, 0, v___x_4401_);
                    lean_ctor_set(v___x_4404_, 1, v___x_4403_);
                    v___x_4405_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                    v___x_4406_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4406_, 0, v___x_4404_);
                    lean_ctor_set(v___x_4406_, 1, v___x_4405_);
                    v___x_4407_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1(v___x_4406_, v___y_4390_, v___y_4391_);
                    return v___x_4407_;
                } else {
                    lean_dec(v_declName_4389_);
                    v_val_4408_ = lean_ctor_get(v___x_4400_, 0);
                    v_isSharedCheck_4437_ = (!lean_is_exclusive(v___x_4400_)) as u8;
                    if v_isSharedCheck_4437_ == 0 {
                        v___x_4410_ = v___x_4400_;
                        v_isShared_4411_ = v_isSharedCheck_4437_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4408_);
                        lean_dec(v___x_4400_);
                        v___x_4410_ = lean_box(0);
                        v_isShared_4411_ = v_isSharedCheck_4437_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4412_ = lean_st_ref_take(v___y_4391_);
                v_env_4413_ = lean_ctor_get(v___x_4412_, 0);
                v_nextMacroScope_4414_ = lean_ctor_get(v___x_4412_, 1);
                v_ngen_4415_ = lean_ctor_get(v___x_4412_, 2);
                v_auxDeclNGen_4416_ = lean_ctor_get(v___x_4412_, 3);
                v_traceState_4417_ = lean_ctor_get(v___x_4412_, 4);
                v_messages_4418_ = lean_ctor_get(v___x_4412_, 6);
                v_infoState_4419_ = lean_ctor_get(v___x_4412_, 7);
                v_snapshotTasks_4420_ = lean_ctor_get(v___x_4412_, 8);
                v_isSharedCheck_4435_ = (!lean_is_exclusive(v___x_4412_)) as u8;
                if v_isSharedCheck_4435_ == 0 {
                    v_unused_4436_ = lean_ctor_get(v___x_4412_, 5);
                    lean_dec(v_unused_4436_);
                    v___x_4422_ = v___x_4412_;
                    v_isShared_4423_ = v_isSharedCheck_4435_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4420_);
                    lean_inc(v_infoState_4419_);
                    lean_inc(v_messages_4418_);
                    lean_inc(v_traceState_4417_);
                    lean_inc(v_auxDeclNGen_4416_);
                    lean_inc(v_ngen_4415_);
                    lean_inc(v_nextMacroScope_4414_);
                    lean_inc(v_env_4413_);
                    lean_dec(v___x_4412_);
                    v___x_4422_ = lean_box(0);
                    v_isShared_4423_ = v_isSharedCheck_4435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4424_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_4424_, 0, v_val_4408_);
                v___x_4425_ = l_Lean_ScopedEnvExtension_modifyState___redArg(
                    v___x_4395_,
                    v_env_4413_,
                    v___f_4424_,
                );
                v___x_4426_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2);
                if v_isShared_4423_ == 0 {
                    lean_ctor_set(v___x_4422_, 5, v___x_4426_);
                    lean_ctor_set(v___x_4422_, 0, v___x_4425_);
                    v___x_4428_ = v___x_4422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4425_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_nextMacroScope_4414_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 2, v_ngen_4415_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 3, v_auxDeclNGen_4416_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 4, v_traceState_4417_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 5, v___x_4426_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 6, v_messages_4418_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 7, v_infoState_4419_);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 8, v_snapshotTasks_4420_);
                    v___x_4428_ = v_reuseFailAlloc_4434_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4429_ = lean_st_ref_set(v___y_4391_, v___x_4428_);
                v___x_4430_ = lean_box(0);
                if v_isShared_4411_ == 0 {
                    lean_ctor_set_tag(v___x_4410_, 0);
                    lean_ctor_set(v___x_4410_, 0, v___x_4430_);
                    v___x_4432_ = v___x_4410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4430_);
                    v___x_4432_ = v_reuseFailAlloc_4433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed(
    mut v___x_4438_: *mut LeanObject,
    mut v_declName_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4443_: *mut LeanObject = core::ptr::null_mut();
    v_res_4443_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(v___x_4438_, v_declName_4439_, v___y_4440_, v___y_4441_);
    lean_dec(v___y_4441_);
    lean_dec_ref(v___y_4440_);
    lean_dec_ref(v___x_4438_);
    return v_res_4443_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    v___x_4465_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
    v___x_4466_ = l_Lean_registerBuiltinAttribute(v___x_4465_);
    return v___x_4466_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed(
    mut v_a_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4468_: *mut LeanObject = core::ptr::null_mut();
    v_res_4468_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_();
    return v_res_4468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_NameMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default();
    lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry();
    lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Tactic_Cbv_cbvEvalExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvEvalExt);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_NameMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
}
